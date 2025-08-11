use stoffel_vm_types::instructions::Instruction;
use stoffel_vm_types::core_types::Value;
use std::collections::{HashMap, HashSet, VecDeque};

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
/// This is a simplified version assuming basic blocks (no complex control flow analysis yet).
pub fn analyze_liveness(instructions: &[Instruction]) -> HashMap<VirtualRegister, LiveInterval> {
    use crate::register_allocator::InstructionRegisterAnalysis;
    let mut intervals: HashMap<VirtualRegister, LiveInterval> = HashMap::new();
    let mut last_use: HashMap<VirtualRegister, usize> = HashMap::new();
    let mut defined: HashMap<VirtualRegister, usize> = HashMap::new();

    // Helper to update interval end point
    let update_end = |intervals: &mut HashMap<VirtualRegister, LiveInterval>, vr: VirtualRegister, end_point: usize| {
        intervals.entry(vr).or_insert(LiveInterval { start: 0, end: 0 }).end = end_point;
    };

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
) -> Result<Allocation, AllocationError> {
    let mut simplified_graph = graph.clone();
    let mut allocation: Allocation = HashMap::new();
    let mut node_stack: VecDeque<VirtualRegister> = VecDeque::new();
    let k_total = k_clear + k_secret; // Total available registers

    // --- Simplification Phase ---
    // Find nodes with degree < k and push them onto the stack
    let mut nodes_to_process: Vec<VirtualRegister> = simplified_graph.nodes.iter().cloned().collect();
    nodes_to_process.sort_by_key(|vr| simplified_graph.degree(vr)); // Process lower degree nodes first

    let mut temp_nodes = HashSet::new(); // Track nodes pushed to stack
    while let Some(vr) = nodes_to_process.pop() {
         // Determine the relevant 'k' based on the VR's secrecy requirement
         let requires_secret = *secrecy_map.get(&vr).unwrap_or(&false); // Default to clear if not found? Should exist.
         let k_limit = if requires_secret { k_secret } else { k_clear };

         // Check if degree is less than the limit for *its specific pool*
         // Note: This simplification check is less precise with pools. A node might
         // interfere with many nodes from the *other* pool. A better check might be needed.
         // For now, use the simple degree < k_total check, assignment phase handles pools.
         if simplified_graph.degree(&vr) < k_total {
             node_stack.push_back(vr);
             temp_nodes.insert(vr); // Mark as pushed
             simplified_graph.remove_node(&vr);
             // Re-evaluate degrees of neighbors (could optimize this)
             nodes_to_process = simplified_graph.nodes.iter().cloned().collect();
             nodes_to_process.sort_by_key(|v| simplified_graph.degree(v));
         } else {
             // If no node with degree < k is left, but graph is not empty,
             // we need to spill (or handle potential spills later).
             // For now, push the highest degree node as a potential spill candidate.
             if !simplified_graph.nodes.is_empty() {
                 // Find node with highest degree among remaining
                 if let Some(spill_candidate) = simplified_graph.nodes.iter()
                    .max_by_key(|&v| simplified_graph.degree(v))
                    .cloned()
                 {
                     // Find and remove the spill candidate from nodes_to_process
                     if let Some(pos) = nodes_to_process.iter().position(|&v| v == spill_candidate) {
                         nodes_to_process.remove(pos);
                     } else {
                         // Should not happen if nodes_to_process mirrors simplified_graph.nodes
                         eprintln!("Warning: Spill candidate not found in process list.");
                     }
                     node_stack.push_back(spill_candidate);
                     temp_nodes.insert(spill_candidate); // Mark as pushed
                     simplified_graph.remove_node(&spill_candidate);
                     // Re-evaluate degrees again
                     nodes_to_process = simplified_graph.nodes.iter().cloned().collect();
                     nodes_to_process.sort_by_key(|v| simplified_graph.degree(v));
                 }
             }
         }
    }


    // --- Assignment Phase ---
    let mut spilled_nodes = Vec::new();
    while let Some(vr) = node_stack.pop_back() {
        let requires_secret = *secrecy_map.get(&vr)
            .expect("Virtual register missing from secrecy map during allocation");

        // Define the pool of potential physical registers for this VR
        let allowed_regs_range = if requires_secret {
            k_clear..(k_clear + k_secret)
        } else {
            0..k_clear
        };
        let mut available_colors_in_pool: HashSet<PhysicalRegister> = allowed_regs_range
            .map(PhysicalRegister)
            .collect();

        // Check colors used by neighbors (in the original graph) that are already allocated
        if let Some(original_neighbors) = graph.neighbors(&vr) {
            for neighbor in original_neighbors {
                if let Some(physical_reg) = allocation.get(neighbor) {
                    // Remove the neighbor's color only if it falls within our allowed pool
                    // (Though technically, we just need to know it's unavailable)
                    available_colors_in_pool.remove(physical_reg);
                }
            }
        }

        // Assign the lowest available color *from the allowed pool*
        if let Some(assigned_color) = available_colors_in_pool.iter().min() {
            allocation.insert(vr, *assigned_color);
        } else {
            // No color available - this node needs to be spilled
            spilled_nodes.push(vr);
            return Err(AllocationError::PoolExhausted(vr, requires_secret));
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
pub fn is_secret_register(reg_index: usize, k_clear: usize) -> bool {
    reg_index >= k_clear
}

/// Rewrites instructions using virtual registers to use allocated physical registers.
pub fn rewrite_instructions(
    instructions: &[Instruction],
    allocation: &Allocation,
    k_clear: usize,
) -> Vec<Instruction> {
    use crate::register_allocator::InstructionRegisterAnalysis;
    instructions
        .iter()
        .map(|inst| inst.remap_registers(allocation, k_clear))
        .collect()
}


// --- Helper trait for Instruction register analysis ---

/// Trait providing register allocation helper methods for Instructions
pub trait InstructionRegisterAnalysis {
    /// Returns a list of virtual registers defined (written to) by this instruction.
    fn defs(&self) -> Vec<VirtualRegister>;
    
    /// Returns a list of virtual registers used (read from) by this instruction.
    fn uses(&self) -> Vec<VirtualRegister>;
    
    /// Creates a new instruction with virtual registers replaced by physical registers.
    fn remap_registers(&self, allocation: &Allocation, k_clear: usize) -> Instruction;
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
            Instruction::SHL(r, _, _) | Instruction::SHR(r, _, _) |
            Instruction::RET(r) | Instruction::PUSHARG(r) // RET/PUSHARG don't strictly define, but are often the last use
            => vec![VirtualRegister(*r)],
            Instruction::CMP(_, _) | Instruction::JMP(_) |
            Instruction::JMPEQ(_) | Instruction::JMPNEQ(_) |
            Instruction::JMPLT(_) | Instruction::JMPGT(_) |
            Instruction::CALL(_)
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
    fn remap_registers(&self, allocation: &Allocation, k_clear: usize) -> Instruction {
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
