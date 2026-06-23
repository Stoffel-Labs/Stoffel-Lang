#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
EXAMPLES_DIR="${ROOT_DIR}/examples"
VM_DIR="${STOFFEL_VM_DIR:-/Users/gabriel/RustroverProjects/StoffelVM}"
OUT_DIR="${STOFFEL_EXAMPLES_OUT:-${EXAMPLES_DIR}/dist}"
RUN_DOCKER_MPC=0
RUN_HOST_MPC=0

for arg in "$@"; do
  case "$arg" in
    --docker-mpc)
      RUN_DOCKER_MPC=1
      ;;
    --host-mpc)
      RUN_HOST_MPC=1
      ;;
    -h|--help)
      cat <<'USAGE'
Usage: examples/validate_examples.sh [--docker-mpc] [--host-mpc]

Compiles every examples/**/main.stfl program to examples/dist.
Runs local-only examples through StoffelVM.
Optionally runs an MPC smoke test either through Docker Compose or through
five local StoffelVM host processes.

Environment:
  STOFFEL_VM_DIR          VM checkout path
  STOFFEL_EXAMPLES_OUT   Output directory for .stflb files
  STOFFEL_PROGRAM_NAME   Compiled binary to run in docker compose
  STOFFEL_MPC_BACKEND    honeybadger or avss
  STOFFEL_MPC_CURVE      bls12-381, secp256k1, p-256, etc.
USAGE
      exit 0
      ;;
    *)
      echo "unknown argument: $arg" >&2
      exit 2
      ;;
  esac
done

if [ ! -d "$VM_DIR" ]; then
  echo "VM checkout not found: $VM_DIR" >&2
  exit 2
fi

mkdir -p "$OUT_DIR"

echo "Building Stoffel compiler..."
cargo build --quiet --manifest-path "${ROOT_DIR}/Cargo.toml"
COMPILER="${ROOT_DIR}/target/debug/stoffellang"

echo "Compiling examples into ${OUT_DIR}..."
find "$EXAMPLES_DIR" -path "$OUT_DIR" -prune -o -name main.stfl -print | sort | while read -r source; do
  rel="${source#${EXAMPLES_DIR}/}"
  rel_dir="$(dirname "$rel")"
  binary_name="$(printf '%s' "$rel_dir" | tr '/ ' '__').stflb"
  output="${OUT_DIR}/${binary_name}"
  echo "  ${rel} -> ${binary_name}"
  "$COMPILER" -b -o "$output" "$source" >/dev/null
done

run_vm() {
  local binary_name="$1"
  shift
  echo "Running local VM example: ${binary_name}"
  cargo run --quiet --manifest-path "${VM_DIR}/Cargo.toml" -p stoffel-vm --bin stoffel-run -- \
    "${OUT_DIR}/${binary_name}" main "$@"
}

run_vm local_control_flow.stflb
run_vm local_collections.stflb
run_vm language_policy_engine.stflb
run_vm local_text_processing.stflb
run_vm local_dynamic_workflow.stflb
run_vm local_closure_counter.stflb
run_vm language_mpc_schemas.stflb

LOCAL_STORE="$(mktemp -d "${TMPDIR:-/tmp}/stoffel-local-store.XXXXXX")"
trap 'rm -rf "$LOCAL_STORE"' EXIT
run_vm local_storage.stflb --local-store "${LOCAL_STORE}/example.redb"

if [ "$RUN_DOCKER_MPC" -eq 1 ]; then
  echo "Running docker compose MPC example..."
  (
    cd "$EXAMPLES_DIR"
    STOFFEL_VM_DIR="$VM_DIR" \
    STOFFEL_EXAMPLES_OUT="$OUT_DIR" \
      docker compose -f docker-compose.mpc.yml up --build --abort-on-container-exit --exit-code-from party0
  )
  (
    cd "$EXAMPLES_DIR"
    STOFFEL_VM_DIR="$VM_DIR" \
    STOFFEL_EXAMPLES_OUT="$OUT_DIR" \
      docker compose -f docker-compose.mpc.yml down --remove-orphans
  )
fi

if [ "$RUN_HOST_MPC" -eq 1 ]; then
  echo "Running host-process MPC example..."
  "${EXAMPLES_DIR}/run_mpc_local.sh"
fi

echo "Example validation complete."
