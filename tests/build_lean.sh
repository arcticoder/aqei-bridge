#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# If elan is installed, load its env to put `lake` on PATH.
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1090
  source "$HOME/.elan/env"
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found on PATH. Install Lean 4 (elan) so 'lake build' works." >&2
  exit 1
fi

cd "$ROOT_DIR/lean"
lake build
