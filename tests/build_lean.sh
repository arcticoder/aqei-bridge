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

# Fetch dependencies if any (none by default), then build.
# We capture stdout+stderr so we can filter noisy lines before printing.
# IMPORTANT: do NOT use "cmd; ec=$?" with set -e active — set -e fires on
# the failing command before ec is assigned.  Use an if/else instead.
tmpout=$(mktemp)
if lake build >"$tmpout" 2>&1; then
  ec=0
else
  ec=$?
fi

# Context-aware filter: suppress Mathlib-originating noise while preserving
# all diagnostics from our own src/ files.
#
# Rules (applied by the Python script below):
#   1. Suppress "⚠ [N/M] Replayed Mathlib.*" progress lines entirely.
#   2. Suppress "warning: ... .lake/packages/ ..." lines (Mathlib warnings).
#   3. Suppress continuation lines that follow a Mathlib warning (lines with
#      no file:line: prefix that appear before the next diagnostic or progress
#      marker).  This covers "Declarations whose name ends with..." and
#      "note: this linter can be disabled" continuations.
#   4. Suppress "#print axioms" output lines of the form
#      "info: ... depends on axioms: [...]" (benign; formal axioms are
#      propext / Classical.choice / Quot.sound for all definitions).
#
# We explicitly do NOT suppress warnings/errors/info from src/ files so that
# problems in our own code are always visible.

LEAN_LOG="$ROOT_DIR/lean/build.log"

python3 - "$tmpout" "$LEAN_LOG" <<'PYEOF'
import sys

in_path, out_path = sys.argv[1], sys.argv[2]

def _is_progress(line):
    return line[:1] in ('⚠', 'ℹ', '✓')

def _is_diagnostic(line):
    return line.startswith(('warning:', 'error:', 'info:'))

def _from_mathlib(line):
    return '.lake/packages/' in line

def _is_axiom_info(line):
    # "#print axioms" output — benign, every definition uses core Lean axioms
    return line.startswith('info:') and 'depends on axioms:' in line

filtered = []
in_mathlib_block = False

with open(in_path, encoding='utf-8', errors='replace') as fh:
    for raw in fh:
        line = raw.rstrip('\n')

        # Rule 1: Mathlib replay progress header → enter skip mode
        if _is_progress(line) and 'Replayed Mathlib' in line:
            in_mathlib_block = True
            continue

        # Any other progress marker → leave skip mode (our own module replayed)
        if _is_progress(line):
            in_mathlib_block = False
            filtered.append(line)
            continue

        # Rule 2: diagnostic from .lake/packages/ → enter skip mode
        if _is_diagnostic(line) and _from_mathlib(line):
            in_mathlib_block = True
            continue

        # Diagnostic from our own src/ → always leave skip mode and keep
        if _is_diagnostic(line) and not _from_mathlib(line):
            in_mathlib_block = False
            # Rule 4: axiom-dependency info is benign, suppress from output
            if _is_axiom_info(line):
                continue
            filtered.append(line)
            continue

        # Rule 3: continuation lines while in a Mathlib block → suppress
        if in_mathlib_block:
            continue

        filtered.append(line)

text = '\n'.join(filtered)
# Write filtered output to lean/build.log for manual inspection
with open(out_path, 'w', encoding='utf-8') as fh:
    fh.write(text + '\n')
# Also print to stdout for the test runner
print(text)
PYEOF

rm -f "$tmpout"
[ $ec -eq 0 ] || { echo "lake build failed (exit $ec)" >&2; exit $ec; }
echo "Lean build log written to: $LEAN_LOG"
