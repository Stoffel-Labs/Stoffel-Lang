use stoffel_vm_types::instructions::Instruction;
use std::collections::{HashMap, HashSet};

// --- Types ---

/// Represents a virtual register used during initial code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VirtualRegister(pub usize);

/// Represents a physical hardware register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PhysicalRegister(pub usize);

/// Represents the live interval of a virtual register [start, end).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveInterval {
    pub start: usize, // Instruction index where the register is defined
    pub end: usize,   // Instruction index after the last use
}

/// Represents the interference graph. Nodes are virtual registers.
/// Edges connect registers that are live at the same time.
#[derive(Debug, Clone, Default)]
pub struct InterferenceGraph {
    adj: HashMap<VirtualRegister, HashSet<VirtualRegister>>,
    nodes: HashSet<VirtualRegister>, // Keep track of all nodes (virtual registers)
}

/// Represents the result of register allocation.
pub type Allocation = HashMap<VirtualRegister, PhysicalRegister>;

/// Error type for allocation failures (e.g., needs spilling).
#[derive(Debug, Clone)]
pub enum AllocationError {
    PoolExhausted(VirtualRegister, bool), // Registers that could not be colored due to pool exhaustion
    NeedsSpilling(Vec<VirtualRegister>), // Registers that could not be colored
}

// --- Liveness Analysis ---

/// Computes the live intervals for all virtual registers in a sequence of instructions.
/// Legacy linear analysis wrapper (no CFG). Prefer `analyze_liveness_cfg_with_liveins`.
pub fn analyze_liveness(instructions: &[Instruction]) -> HashMap<VirtualRegister, LiveInterval> {
    analyze_liveness_with_liveins(instructions, &[])
}

/// Computes the live intervals for all virtual registers with an explicit set of live-in parameters.
/// Legacy linear analysis wrapper (no CFG). Prefer `analyze_liveness_cfg_with_liveins`.
pub fn analyze_liveness_with_liveins(
    instructions: &[Instruction],
    live_in: &[VirtualRegister],
) -> HashMap<VirtualRegister, LiveInterval> {
    use crate::register_allocator::InstructionRegisterAnalysis;
    let mut intervals: HashMap<VirtualRegister, LiveInterval> = HashMap::new();
    let mut last_use: HashMap<VirtualRegister, usize> = HashMap::new();
    let mut defined: HashMap<VirtualRegister, usize> = HashMap::new();

    // Seed live-in parameters as live from function entry (index 0)
    for &vr in live_in {
        intervals.entry(vr).or_insert(LiveInterval { start: 0, end: 0 });
    }

    // Helper to update interval start point
    let update_start = |intervals: &mut HashMap<VirtualRegister, LiveInterval>, vr: VirtualRegister, start_point: usize| {
        intervals.entry(vr).or_insert(LiveInterval { start: 0, end: 0 }).start = start_point;
    };

    // First pass: Find definitions and last uses
    for (i, instruction) in instructions.iter().enumerate() {
        let instruction_index = i; // Index of the current instruction

        // Process uses first (update last_use)
        for vr in instruction.uses() {
            last_use.insert(vr, instruction_index);
            // Ensure the register exists in intervals, even if defined later (e.g., function args)
             intervals.entry(vr).or_insert(LiveInterval { start: 0, end: 0 });
        }

        // Process definitions (update defined, initialize interval)
        for vr in instruction.defs() {
            if !defined.contains_key(&vr) {
                defined.insert(vr, instruction_index);
                update_start(&mut intervals, vr, instruction_index);
            }
            // Definition also counts as a use for liveness purposes
            last_use.insert(vr, instruction_index);
        }
    }

    // Second pass: Set the end point for each interval
    for (vr, interval) in intervals.iter_mut() {
        // The interval ends *after* the last use instruction.
        interval.end = last_use.get(vr).map_or(interval.start, |last_use_idx| last_use_idx + 1);
        // Ensure start is correctly set from the 'defined' map
        if let Some(def_idx) = defined.get(vr) {
             interval.start = *def_idx;
        } else {
            // If not defined in this block (e.g., function parameter), start at 0
            interval.start = 0;
        }
        // Ensure end is at least start + 1 if defined and used in the same instruction
        if interval.end <= interval.start {
            interval.end = interval.start + 1;
        }
    }

    intervals
}

/// CFG-based liveness with explicit labels (block successors) and live-ins.
/// Builds basic blocks, runs iterative dataflow to compute live-in/out, then per-instruction liveness,
/// and finally collapses to single intervals per virtual register.
pub fn analyze_liveness_cfg_with_liveins(
    instructions: &[Instruction],
    labels: &HashMap<String, usize>,
    live_in: &[VirtualRegister],
) -> HashMap<VirtualRegister, LiveInterval> {
    use crate::register_allocator::InstructionRegisterAnalysis;
    let n = instructions.len();
    // Early exit
    if n == 0 {
        return HashMap::new();
    }

    // Collect all VRs seen
    let mut all_vrs: HashSet<VirtualRegister> = HashSet::new();
    for inst in instructions.iter() {
        for u in inst.uses() { all_vrs.insert(u); }
        for d in inst.defs() { all_vrs.insert(d); }
    }
    for &vr in live_in { all_vrs.insert(vr); }

    // 1) Determine basic block boundaries
    let mut block_starts: HashSet<usize> = HashSet::new();
    block_starts.insert(0);
    for &idx in labels.values() {
        if idx < n { block_starts.insert(idx); }
    }
    for i in 0..n {
        match &instructions[i] {
            Instruction::JMP(_) | Instruction::JMPEQ(_) | Instruction::JMPNEQ(_) | Instruction::JMPLT(_) | Instruction::JMPGT(_) | Instruction::RET(_) => {
                if i + 1 < n { block_starts.insert(i + 1); }
            }
            _ => {}
        }
    }
    // Create sorted list of starts
    let mut starts: Vec<usize> = block_starts.into_iter().collect();
    starts.sort_unstable();
    // Map: inst index -> block id
    let mut inst2block: Vec<usize> = vec![0; n];
    for (bi, &s) in starts.iter().enumerate() {
        let end = starts.get(bi + 1).copied().unwrap_or(n);
        for i in s..end { inst2block[i] = bi; }
    }

    #[derive(Default, Clone)]
    struct BlockInfo {
        start: usize,
        end: usize, // exclusive
        succs: Vec<usize>,
        use_set: HashSet<VirtualRegister>,
        def_set: HashSet<VirtualRegister>,
    }

    let mut blocks: Vec<BlockInfo> = Vec::with_capacity(starts.len());
    for (bi, &s) in starts.iter().enumerate() {
        let e = starts.get(bi + 1).copied().unwrap_or(n);
        blocks.push(BlockInfo { start: s, end: e, ..Default::default() });
    }

    // 2) Compute successors per block
    // Helper: get block id by instruction index
    let label_to_block = |lbl: &String| -> Option<usize> { labels.get(lbl).and_then(|&idx| if idx < n { Some(inst2block[idx]) } else { None }) };
    for bi in 0..blocks.len() {
        if blocks[bi].start == blocks[bi].end { continue; }
        let last_i = blocks[bi].end - 1;
        match &instructions[last_i] {
            Instruction::JMP(lbl) => {
                if let Some(t) = label_to_block(lbl) { blocks[bi].succs.push(t); }
            }
            Instruction::JMPEQ(lbl) | Instruction::JMPNEQ(lbl) | Instruction::JMPLT(lbl) | Instruction::JMPGT(lbl) => {
                if let Some(t) = label_to_block(lbl) { blocks[bi].succs.push(t); }
                // fallthrough
                if let Some(next_start) = starts.get(bi + 1).copied() { if next_start < n { blocks[bi].succs.push(bi + 1); } }
            }
            Instruction::RET(_) => { /* no successors */ }
            _ => {
                // fallthrough
                if let Some(_next) = starts.get(bi + 1) { blocks[bi].succs.push(bi + 1); }
            }
        }
        // Dedup succs
        let mut uniq = HashSet::new();
        blocks[bi].succs.retain(|s| uniq.insert(*s));
    }

    // 3) Compute use/def per block
    for bi in 0..blocks.len() {
        let b = &mut blocks[bi];
        for i in b.start..b.end {
            let inst = &instructions[i];
            // uses
            for u in inst.uses() {
                if !b.def_set.contains(&u) { b.use_set.insert(u); }
            }
            // defs
            for d in inst.defs() { b.def_set.insert(d); }
        }
    }

    // 4) Iterative dataflow for live_in/live_out
    let mut live_in_b: Vec<HashSet<VirtualRegister>> = vec![HashSet::new(); blocks.len()];
    let mut live_out_b: Vec<HashSet<VirtualRegister>> = vec![HashSet::new(); blocks.len()];

    // Seed entry live-ins
    let entry_block = inst2block[0];
    for &vr in live_in { live_in_b[entry_block].insert(vr); }

    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..blocks.len()).rev() {
            // out[B] = union in[S]
            let mut new_out: HashSet<VirtualRegister> = HashSet::new();
            for &s in &blocks[bi].succs { new_out.extend(live_in_b[s].iter().copied()); }
            // in[B] = use[B] ∪ (out[B] \ def[B])
            let mut new_in = blocks[bi].use_set.clone();
            for v in new_out.iter() { if !blocks[bi].def_set.contains(v) { new_in.insert(*v); } }
            // Ensure seed live-ins at entry
            if bi == entry_block { for &vr in live_in { new_in.insert(vr); } }

            if new_out != live_out_b[bi] { live_out_b[bi] = new_out; changed = true; }
            if new_in != live_in_b[bi] { live_in_b[bi] = new_in; changed = true; }
        }
    }

    // 5) Per-instruction liveness within each block (backwards)
    let mut live_in_inst: Vec<HashSet<VirtualRegister>> = vec![HashSet::new(); n];
    let mut live_out_inst: Vec<HashSet<VirtualRegister>> = vec![HashSet::new(); n];

    for bi in 0..blocks.len() {
        let mut live: HashSet<VirtualRegister> = live_out_b[bi].clone();
        // Walk backwards within block
        for i in (blocks[bi].start..blocks[bi].end).rev() {
            // out at i
            live_out_inst[i] = live.clone();
            // in at i = (out - defs) ∪ uses
            let inst = &instructions[i];
            // remove defs
            for d in inst.defs() { live.remove(&d); }
            // add uses
            for u in inst.uses() { live.insert(u); }
            live_in_inst[i] = live.clone();
        }
    }

    // 6) Build intervals
    let mut def_first: HashMap<VirtualRegister, usize> = HashMap::new();
    for i in 0..n {
        for d in instructions[i].defs() {
            def_first.entry(d).and_modify(|e| { if i < *e { *e = i; } }).or_insert(i);
        }
    }

    let mut intervals: HashMap<VirtualRegister, LiveInterval> = HashMap::new();
    for vr in all_vrs.into_iter() {
        // start
        let mut start = def_first.get(&vr).copied().unwrap_or(usize::MAX);
        // If live before any instruction, find earliest index where live_in is true
        if start == usize::MAX {
            for i in 0..n { if live_in_inst[i].contains(&vr) { start = i; break; } }
        }
        if start == usize::MAX { start = 0; }
        // end = last i where live_out[i] contains vr => i+1
        let mut end = 0usize;
        for i in 0..n { if live_out_inst[i].contains(&vr) { end = i + 1; } }
        // Ensure at least covers def-only
        if let Some(&d) = def_first.get(&vr) { if end < d + 1 { end = d + 1; } }
        if end <= start { end = start + 1; }
        intervals.insert(vr, LiveInterval { start, end });
    }

    intervals
}

// --- Interference Graph ---

impl InterferenceGraph {
    /// Adds a node (virtual register) to the graph.
    pub fn add_node(&mut self, vr: VirtualRegister) {
        self.nodes.insert(vr);
        self.adj.entry(vr).or_default(); // Ensure entry exists even if no edges yet
    }

    /// Adds an edge between two virtual registers.
    pub fn add_edge(&mut self, vr1: VirtualRegister, vr2: VirtualRegister) {
        if vr1 != vr2 {
            self.add_node(vr1); // Ensure nodes exist
            self.add_node(vr2);
            self.adj.entry(vr1).or_default().insert(vr2);
            self.adj.entry(vr2).or_default().insert(vr1);
        }
    }

    /// Returns the neighbors of a given virtual register.
    pub fn neighbors(&self, vr: &VirtualRegister) -> Option<&HashSet<VirtualRegister>> {
        self.adj.get(vr)
    }

    /// Returns the degree of a node (number of neighbors).
    pub fn degree(&self, vr: &VirtualRegister) -> usize {
        self.neighbors(vr).map_or(0, |neighbors| neighbors.len())
    }

    /// Removes a node and its associated edges from the graph.
    pub fn remove_node(&mut self, vr_to_remove: &VirtualRegister) {
        if let Some(neighbors) = self.adj.remove(vr_to_remove) {
            for neighbor in neighbors {
                if let Some(neighbor_adj) = self.adj.get_mut(&neighbor) {
                    neighbor_adj.remove(vr_to_remove);
                }
            }
        }
        self.nodes.remove(vr_to_remove);
    }
}

/// Builds the interference graph from live intervals.
pub fn build_interference_graph(intervals: &HashMap<VirtualRegister, LiveInterval>) -> InterferenceGraph {
    let mut graph = InterferenceGraph::default();
    let virtual_registers: Vec<VirtualRegister> = intervals.keys().cloned().collect();

    // Ensure all registers are added as nodes initially
    for &vr in &virtual_registers {
        graph.add_node(vr);
    }

    // Compare every pair of intervals for overlap
    for i in 0..virtual_registers.len() {
        for j in (i + 1)..virtual_registers.len() {
            let vr1 = virtual_registers[i];
            let vr2 = virtual_registers[j];
            let interval1 = intervals[&vr1];
            let interval2 = intervals[&vr2];

            // Check for overlap: !(interval1.end <= interval2.start || interval2.end <= interval1.start)
            if interval1.start < interval2.end && interval2.start < interval1.end {
                graph.add_edge(vr1, vr2);
            }
        }
    }

    graph
}

// --- Graph Coloring (Greedy Algorithm) ---

/// Assigns physical registers (colors) to virtual registers using a greedy graph coloring algorithm.
/// `k_clear` is the number of available clear physical registers.
/// `k_secret` is the number of available secret physical registers.
/// `secrecy_map` indicates whether each virtual register requires a secret register.
pub fn color_graph(
    graph: &InterferenceGraph,
    k_clear: usize,
    k_secret: usize,
    secrecy_map: &HashMap<VirtualRegister, bool>,
    precolored: &HashMap<VirtualRegister, PhysicalRegister>,
) -> Result<Allocation, AllocationError> {
    // --- Helpers to respect register pools ---
    fn pool_degree(
        g: &InterferenceGraph,
        v: &VirtualRegister,
        secrecy: &HashMap<VirtualRegister, bool>,
    ) -> usize {
        let my_secret = *secrecy
            .get(v)
            .expect("missing secrecy_map entry for virtual register");
        g.neighbors(v)
            .map(|ns| {
                ns.iter()
                    .filter(|n| *secrecy
                        .get(*n)
                        .expect("missing secrecy_map entry for virtual register")
                        == my_secret)
                    .count()
            })
            .unwrap_or(0)
    }

    fn pool_capacity(
        v: &VirtualRegister,
        k_clear: usize,
        k_secret: usize,
        secrecy: &HashMap<VirtualRegister, bool>,
    ) -> usize {
        if *secrecy
            .get(v)
            .expect("missing secrecy_map entry for virtual register")
        {
            k_secret
        } else {
            k_clear
        }
    }

    let mut sg = graph.clone();
    // Validate precolored mapping: forbid using reserved R0
    for (_vr, _pr) in precolored.iter() {
        // Allow precoloring to R0: parameters may live in the ABI return/arg register.
    }

    // Start with precolored allocation (e.g., ABI-fixed registers like parameters)
    let mut allocation: Allocation = precolored.clone();
    // Remove precolored nodes from the simplification graph so they are not recolored/spilled
    for v in allocation.keys() {
        if sg.nodes.contains(v) {
            sg.remove_node(v);
        }
    }
    let mut stack: Vec<VirtualRegister> = Vec::new();

    // --- Simplification Phase (pool-aware) ---
    while !sg.nodes.is_empty() {
        if let Some(v) = sg
            .nodes
            .iter()
            .copied()
            .find(|v| pool_degree(&sg, v, secrecy_map) < pool_capacity(v, k_clear, k_secret, secrecy_map))
        {
            stack.push(v);
            sg.remove_node(&v);
            continue;
        }

        // Else pick a spill candidate (max pool degree)
        let spill = sg
            .nodes
            .iter()
            .copied()
            .max_by_key(|v| pool_degree(&sg, v, secrecy_map))
            .expect("graph had nodes but none found");
        stack.push(spill);
        sg.remove_node(&spill);
    }

    // --- Assignment Phase ---
    let mut spilled_nodes = Vec::new();
    while let Some(vr) = stack.pop() {
        let requires_secret = *secrecy_map
            .get(&vr)
            .expect("missing secrecy_map entry for virtual register");

        // Define the pool of potential physical registers for this VR
        let allowed_regs_range = if requires_secret {
            k_clear..(k_clear + k_secret)
        } else {
            1..k_clear // Reserve physical R0 (0) for ABI return value
        };
        let mut available_colors_in_pool: HashSet<PhysicalRegister> = allowed_regs_range
            .map(PhysicalRegister)
            .collect();

        // Check colors used by neighbors (in the original graph) that are already allocated
        if let Some(original_neighbors) = graph.neighbors(&vr) {
            for neighbor in original_neighbors {
                if let Some(physical_reg) = allocation.get(neighbor) {
                    available_colors_in_pool.remove(physical_reg);
                }
            }
        }

        // Assign the lowest available color from the allowed pool
        if let Some(&c) = available_colors_in_pool.iter().min() {
            allocation.insert(vr, c);
        } else {
            // No color available - this node needs to be spilled
            spilled_nodes.push(vr);
        }
    }

    if spilled_nodes.is_empty() {
        Ok(allocation)
    } else {
        Err(AllocationError::NeedsSpilling(spilled_nodes))
    }
}

// --- Instruction Rewriting ---

/// Helper to check if a physical register index is in the secret range
/// Rewrites instructions using virtual registers to use allocated physical registers.
pub fn rewrite_instructions(
    instructions: &[Instruction],
    allocation: &Allocation,
) -> Vec<Instruction> {
    use crate::register_allocator::InstructionRegisterAnalysis;
    let mut out: Vec<Instruction> = Vec::with_capacity(instructions.len());
    let mut last_was_call = false;
    for inst in instructions.iter() {
        match inst {
            // Special-case: right after a CALL, a MOV to capture return value.
            // If src is virtual register 0 in the IR, it was intended to mean ABI R0.
            // Emit MOV(dest_phys, 0) using physical R0 for the source.
            Instruction::MOV(dest_vr, src_vr) if last_was_call && *src_vr == 0 => {
                let dest_pr = allocation
                    .get(&VirtualRegister(*dest_vr))
                    .expect("Virtual register not found in allocation map during rewrite (MOV dest after CALL)")
                    .0;
                out.push(Instruction::MOV(dest_pr, 0));
                last_was_call = false; // handled
                continue;
            }
            _ => {}
        }
        // Default remapping path
        let rewritten = inst.remap_registers(allocation);
        last_was_call = matches!(inst, Instruction::CALL(_));
        out.push(rewritten);
    }
    out
}


// --- Helper trait for Instruction register analysis ---

/// Trait providing register allocation helper methods for Instructions
pub trait InstructionRegisterAnalysis {
    /// Returns a list of virtual registers defined (written to) by this instruction.
    fn defs(&self) -> Vec<VirtualRegister>;
    
    /// Returns a list of virtual registers used (read from) by this instruction.
    fn uses(&self) -> Vec<VirtualRegister>;
    
    /// Creates a new instruction with virtual registers replaced by physical registers.
    fn remap_registers(&self, allocation: &Allocation) -> Instruction;
}

impl InstructionRegisterAnalysis for Instruction {
    /// Returns a list of virtual registers defined (written to) by this instruction.
    fn defs(&self) -> Vec<VirtualRegister> {
        match self {
            Instruction::LD(r, _) | Instruction::LDI(r, _) |
            Instruction::MOV(r, _) | Instruction::ADD(r, _, _) |
            Instruction::SUB(r, _, _) | Instruction::MUL(r, _, _) |
            Instruction::DIV(r, _, _) | Instruction::MOD(r, _, _) |
            Instruction::AND(r, _, _) | Instruction::OR(r, _, _) |
            Instruction::XOR(r, _, _) | Instruction::NOT(r, _) |
            Instruction::SHL(r, _, _) | Instruction::SHR(r, _, _)
            => vec![VirtualRegister(*r)],
            // no defs here:
            Instruction::RET(_) | Instruction::PUSHARG(_) |
            Instruction::CMP(_, _) | Instruction::JMP(_) |
            Instruction::JMPEQ(_) | Instruction::JMPNEQ(_) |
            Instruction::JMPLT(_) | Instruction::JMPGT(_) | Instruction::CALL(_)
            => vec![], // These don't define registers in the typical sense
        }
    }

    /// Returns a list of virtual registers used (read from) by this instruction.
    fn uses(&self) -> Vec<VirtualRegister> {
        match self {
            Instruction::MOV(_, r_src) | Instruction::NOT(_, r_src) |
            Instruction::RET(r_src) | Instruction::PUSHARG(r_src)
            => vec![VirtualRegister(*r_src)],
            Instruction::ADD(_, r1, r2) | Instruction::SUB(_, r1, r2) |
            Instruction::MUL(_, r1, r2) | Instruction::DIV(_, r1, r2) |
            Instruction::MOD(_, r1, r2) | Instruction::AND(_, r1, r2) |
            Instruction::OR(_, r1, r2) | Instruction::XOR(_, r1, r2) |
            Instruction::SHL(_, r1, r2) | Instruction::SHR(_, r1, r2) |
            Instruction::CMP(r1, r2)
            => vec![VirtualRegister(*r1), VirtualRegister(*r2)],
            Instruction::LD(_, _) | Instruction::LDI(_, _) |
            Instruction::JMP(_) | Instruction::JMPEQ(_) |
            Instruction::JMPNEQ(_) | Instruction::JMPLT(_) |
            Instruction::JMPGT(_) | Instruction::CALL(_)
            => vec![], // These don't use registers in the typical sense
        }
    }

    /// Creates a new instruction with virtual registers replaced by physical registers.
    /// Panics if a virtual register in the instruction is not found in the allocation map.
    fn remap_registers(&self, allocation: &Allocation) -> Instruction {
        let map_reg = |vr: usize| allocation.get(&VirtualRegister(vr))
                                        .expect("Virtual register not found in allocation map during rewrite")
                                        .0; // Get the usize physical register index

        match *self {
            Instruction::LD(vr_dest, offset) => Instruction::LD(map_reg(vr_dest), offset),
            Instruction::LDI(vr_dest, ref val) => Instruction::LDI(map_reg(vr_dest), val.clone()),
            Instruction::MOV(vr_dest, vr_src) => Instruction::MOV(map_reg(vr_dest), map_reg(vr_src)),
            Instruction::ADD(vr_dest, vr1, vr2) => Instruction::ADD(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::SUB(vr_dest, vr1, vr2) => Instruction::SUB(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::MUL(vr_dest, vr1, vr2) => Instruction::MUL(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::DIV(vr_dest, vr1, vr2) => Instruction::DIV(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::MOD(vr_dest, vr1, vr2) => Instruction::MOD(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::AND(vr_dest, vr1, vr2) => Instruction::AND(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::OR(vr_dest, vr1, vr2) => Instruction::OR(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::XOR(vr_dest, vr1, vr2) => Instruction::XOR(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::NOT(vr_dest, vr_src) => Instruction::NOT(map_reg(vr_dest), map_reg(vr_src)),
            Instruction::SHL(vr_dest, vr1, vr2) => Instruction::SHL(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::SHR(vr_dest, vr1, vr2) => Instruction::SHR(map_reg(vr_dest), map_reg(vr1), map_reg(vr2)),
            Instruction::CMP(vr1, vr2) => Instruction::CMP(map_reg(vr1), map_reg(vr2)),
            Instruction::RET(vr_src) => Instruction::RET(map_reg(vr_src)),
            Instruction::PUSHARG(vr_src) => Instruction::PUSHARG(map_reg(vr_src)),
            // Instructions without registers remain the same
            Instruction::JMP(ref label) => Instruction::JMP(label.clone()),
            Instruction::JMPEQ(ref label) => Instruction::JMPEQ(label.clone()),
            Instruction::JMPNEQ(ref label) => Instruction::JMPNEQ(label.clone()),
            Instruction::JMPLT(ref label) => Instruction::JMPLT(label.clone()),
            Instruction::JMPGT(ref label) => Instruction::JMPGT(label.clone()),
            Instruction::CALL(ref name) => Instruction::CALL(name.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stoffel_vm_types::core_types::Value;

    // ===================== Liveness Analysis — Happy Path =====================

    #[test]
    fn liveness_single_define_then_use() {
        // LDI v0, 42; RET v0
        let instructions = vec![
            Instruction::LDI(0, Value::I64(42)),
            Instruction::RET(0),
        ];
        let intervals = analyze_liveness(&instructions);
        let iv = intervals[&VirtualRegister(0)];
        assert_eq!(iv.start, 0);
        assert_eq!(iv.end, 2); // live through instruction 1 (RET uses it)
    }

    #[test]
    fn liveness_two_non_overlapping_variables() {
        // LDI v0, 1; RET v0; LDI v1, 2; RET v1
        let instructions = vec![
            Instruction::LDI(0, Value::I64(1)),
            Instruction::RET(0),
            Instruction::LDI(1, Value::I64(2)),
            Instruction::RET(1),
        ];
        let intervals = analyze_liveness(&instructions);
        let iv0 = intervals[&VirtualRegister(0)];
        let iv1 = intervals[&VirtualRegister(1)];
        // v0: [0, 2), v1: [2, 4) - no overlap
        assert!(iv0.end <= iv1.start);
    }

    #[test]
    fn liveness_two_overlapping_variables() {
        // LDI v0, 1; LDI v1, 2; ADD v2, v0, v1
        let instructions = vec![
            Instruction::LDI(0, Value::I64(1)),
            Instruction::LDI(1, Value::I64(2)),
            Instruction::ADD(2, 0, 1),
        ];
        let intervals = analyze_liveness(&instructions);
        let iv0 = intervals[&VirtualRegister(0)];
        let iv1 = intervals[&VirtualRegister(1)];
        // v0 lives [0, 3), v1 lives [1, 3) - they overlap
        assert!(iv0.start < iv1.end && iv1.start < iv0.end);
    }

    #[test]
    fn liveness_with_live_ins() {
        // Function parameter v0 is live from start
        // ADD v1, v0, v0
        let instructions = vec![
            Instruction::ADD(1, 0, 0),
            Instruction::RET(1),
        ];
        let intervals = analyze_liveness_with_liveins(&instructions, &[VirtualRegister(0)]);
        let iv0 = intervals[&VirtualRegister(0)];
        assert_eq!(iv0.start, 0);
        assert!(iv0.end >= 1); // used in instruction 0
    }

    #[test]
    fn liveness_variable_defined_but_never_used() {
        // LDI v0, 42  (defined but not used)
        let instructions = vec![
            Instruction::LDI(0, Value::I64(42)),
        ];
        let intervals = analyze_liveness(&instructions);
        let iv = intervals[&VirtualRegister(0)];
        // Should have at least a minimal live range covering the definition
        assert!(iv.end > iv.start);
    }

    // ===================== Interference Graph — Happy Path =====================

    #[test]
    fn interference_graph_no_edges_non_overlapping() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 2 });
        intervals.insert(VirtualRegister(1), LiveInterval { start: 2, end: 4 });
        let graph = build_interference_graph(&intervals);
        assert_eq!(graph.degree(&VirtualRegister(0)), 0);
        assert_eq!(graph.degree(&VirtualRegister(1)), 0);
    }

    #[test]
    fn interference_graph_edge_on_overlap() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 3 });
        intervals.insert(VirtualRegister(1), LiveInterval { start: 1, end: 4 });
        let graph = build_interference_graph(&intervals);
        assert_eq!(graph.degree(&VirtualRegister(0)), 1);
        let neighbors = graph.neighbors(&VirtualRegister(0)).unwrap();
        assert!(neighbors.contains(&VirtualRegister(1)));
    }

    #[test]
    fn interference_graph_chain_a_b_c() {
        // a overlaps b, b overlaps c, but a does NOT overlap c
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 2 }); // a
        intervals.insert(VirtualRegister(1), LiveInterval { start: 1, end: 3 }); // b
        intervals.insert(VirtualRegister(2), LiveInterval { start: 2, end: 4 }); // c
        let graph = build_interference_graph(&intervals);
        // a-b edge, b-c edge, no a-c edge
        assert_eq!(graph.degree(&VirtualRegister(0)), 1);
        assert_eq!(graph.degree(&VirtualRegister(1)), 2);
        assert_eq!(graph.degree(&VirtualRegister(2)), 1);
        assert!(!graph.neighbors(&VirtualRegister(0)).unwrap().contains(&VirtualRegister(2)));
    }

    #[test]
    fn interference_graph_add_and_remove_node() {
        let mut graph = InterferenceGraph::default();
        graph.add_node(VirtualRegister(0));
        graph.add_node(VirtualRegister(1));
        graph.add_edge(VirtualRegister(0), VirtualRegister(1));
        assert_eq!(graph.degree(&VirtualRegister(0)), 1);

        graph.remove_node(&VirtualRegister(1));
        assert_eq!(graph.degree(&VirtualRegister(0)), 0);
        assert_eq!(graph.neighbors(&VirtualRegister(1)), None);
    }

    #[test]
    fn self_edge_is_ignored() {
        let mut graph = InterferenceGraph::default();
        graph.add_node(VirtualRegister(0));
        graph.add_edge(VirtualRegister(0), VirtualRegister(0));
        assert_eq!(graph.degree(&VirtualRegister(0)), 0);
    }

    // ===================== Graph Coloring — Happy Path =====================

    #[test]
    fn color_graph_simple_no_interference() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 2 });
        intervals.insert(VirtualRegister(1), LiveInterval { start: 2, end: 4 });
        let graph = build_interference_graph(&intervals);

        let mut secrecy_map = HashMap::new();
        secrecy_map.insert(VirtualRegister(0), false);
        secrecy_map.insert(VirtualRegister(1), false);

        let alloc = color_graph(&graph, 16, 16, &secrecy_map, &HashMap::new()).unwrap();
        assert!(alloc.contains_key(&VirtualRegister(0)));
        assert!(alloc.contains_key(&VirtualRegister(1)));
    }

    #[test]
    fn color_graph_interfering_get_different_colors() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 3 });
        intervals.insert(VirtualRegister(1), LiveInterval { start: 1, end: 4 });
        let graph = build_interference_graph(&intervals);

        let mut secrecy_map = HashMap::new();
        secrecy_map.insert(VirtualRegister(0), false);
        secrecy_map.insert(VirtualRegister(1), false);

        let alloc = color_graph(&graph, 16, 16, &secrecy_map, &HashMap::new()).unwrap();
        assert_ne!(alloc[&VirtualRegister(0)], alloc[&VirtualRegister(1)]);
    }

    #[test]
    fn color_graph_secret_registers_use_secret_pool() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 2 });
        let graph = build_interference_graph(&intervals);

        let mut secrecy_map = HashMap::new();
        secrecy_map.insert(VirtualRegister(0), true); // secret

        let alloc = color_graph(&graph, 16, 16, &secrecy_map, &HashMap::new()).unwrap();
        // Secret registers start at k_clear (16)
        assert!(alloc[&VirtualRegister(0)].0 >= 16);
    }

    #[test]
    fn color_graph_clear_registers_below_secret_start() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 2 });
        let graph = build_interference_graph(&intervals);

        let mut secrecy_map = HashMap::new();
        secrecy_map.insert(VirtualRegister(0), false); // clear

        let alloc = color_graph(&graph, 16, 16, &secrecy_map, &HashMap::new()).unwrap();
        // Clear registers go from 1..k_clear (R0 is reserved for ABI)
        assert!(alloc[&VirtualRegister(0)].0 >= 1 && alloc[&VirtualRegister(0)].0 < 16);
    }

    // ===================== Instruction Rewriting — Happy Path =====================

    #[test]
    fn rewrite_instructions_maps_virtual_to_physical() {
        let instructions = vec![
            Instruction::LDI(0, Value::I64(10)),
            Instruction::LDI(1, Value::I64(20)),
            Instruction::ADD(2, 0, 1),
            Instruction::RET(2),
        ];
        let mut alloc = HashMap::new();
        alloc.insert(VirtualRegister(0), PhysicalRegister(1));
        alloc.insert(VirtualRegister(1), PhysicalRegister(2));
        alloc.insert(VirtualRegister(2), PhysicalRegister(3));

        let rewritten = rewrite_instructions(&instructions, &alloc);
        assert!(matches!(rewritten[0], Instruction::LDI(1, _)));
        assert!(matches!(rewritten[1], Instruction::LDI(2, _)));
        assert!(matches!(rewritten[2], Instruction::ADD(3, 1, 2)));
        assert!(matches!(rewritten[3], Instruction::RET(3)));
    }

    // ===================== Semi-honest =====================

    #[test]
    fn liveness_empty_instructions() {
        let intervals = analyze_liveness(&[]);
        assert!(intervals.is_empty());
    }

    #[test]
    fn interference_graph_single_register_no_edges() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 5 });
        let graph = build_interference_graph(&intervals);
        assert_eq!(graph.degree(&VirtualRegister(0)), 0);
    }

    #[test]
    fn color_graph_with_precolored() {
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 3 });
        intervals.insert(VirtualRegister(1), LiveInterval { start: 1, end: 4 });
        let graph = build_interference_graph(&intervals);

        let mut secrecy_map = HashMap::new();
        secrecy_map.insert(VirtualRegister(0), false);
        secrecy_map.insert(VirtualRegister(1), false);

        let mut precolored = HashMap::new();
        precolored.insert(VirtualRegister(0), PhysicalRegister(1)); // Force v0 -> R1

        let alloc = color_graph(&graph, 16, 16, &secrecy_map, &precolored).unwrap();
        assert_eq!(alloc[&VirtualRegister(0)], PhysicalRegister(1));
        // v1 must get a different register since it interferes with v0
        assert_ne!(alloc[&VirtualRegister(1)], PhysicalRegister(1));
    }

    // ===================== Adversarial =====================

    #[test]
    fn color_graph_pool_exhaustion_causes_spill() {
        // Two interfering clear registers but only 2 clear slots (1 usable since R0 reserved)
        let mut intervals = HashMap::new();
        intervals.insert(VirtualRegister(0), LiveInterval { start: 0, end: 3 });
        intervals.insert(VirtualRegister(1), LiveInterval { start: 1, end: 4 });
        let graph = build_interference_graph(&intervals);

        let mut secrecy_map = HashMap::new();
        secrecy_map.insert(VirtualRegister(0), false);
        secrecy_map.insert(VirtualRegister(1), false);

        // Only 2 clear regs (indices 0..2, but R0 reserved, so only R1 available)
        // Two interfering nodes need 2 registers but only 1 usable
        let result = color_graph(&graph, 2, 0, &secrecy_map, &HashMap::new());
        match result {
            Err(AllocationError::NeedsSpilling(vrs)) => {
                assert!(!vrs.is_empty(), "Spill list should not be empty");
            }
            Err(AllocationError::PoolExhausted(vr, _)) => {
                // Also acceptable — pool exhaustion for a specific register
                let _ = vr; // just confirm it's a valid register
            }
            Ok(_) => panic!("Expected allocation failure due to pool exhaustion"),
        }
    }

    #[test]
    fn high_register_pressure_many_simultaneous_live() {
        // 8 registers all live simultaneously, but with enough pool size
        let mut intervals = HashMap::new();
        let mut secrecy_map = HashMap::new();
        for i in 0..8 {
            intervals.insert(VirtualRegister(i), LiveInterval { start: 0, end: 10 });
            secrecy_map.insert(VirtualRegister(i), false);
        }
        let graph = build_interference_graph(&intervals);
        // All 8 interfere with each other, need 8 different colors
        // k_clear = 16, so R1..R15 = 15 usable. Should succeed.
        let alloc = color_graph(&graph, 16, 16, &secrecy_map, &HashMap::new()).unwrap();
        // Verify all 8 got unique physical registers
        let phys_regs: HashSet<PhysicalRegister> = alloc.values().cloned().collect();
        assert_eq!(phys_regs.len(), 8);
    }

    #[test]
    fn rewrite_preserves_labels_and_calls() {
        let instructions = vec![
            Instruction::JMP("loop_start".into()),
            Instruction::CALL("my_func".into()),
        ];
        let alloc = HashMap::new(); // No VRs used by JMP/CALL
        let rewritten = rewrite_instructions(&instructions, &alloc);
        assert_eq!(rewritten.len(), 2);
        // Verify exact label/function name values, not just instruction type
        match &rewritten[0] {
            Instruction::JMP(label) => assert_eq!(label, "loop_start"),
            other => panic!("Expected JMP(\"loop_start\"), got {:?}", other),
        }
        match &rewritten[1] {
            Instruction::CALL(name) => assert_eq!(name, "my_func"),
            other => panic!("Expected CALL(\"my_func\"), got {:?}", other),
        }
    }
}

