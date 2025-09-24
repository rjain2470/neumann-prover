#!/usr/bin/env bash
set -euo pipefail

if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
fi

[[ -f "$HOME/.elan/env" ]] && source "$HOME/.elan/env"

TOOLCHAIN="${LEAN_TOOLCHAIN:-leanprover/lean4:v4.22.0}"
elan toolchain install "$TOOLCHAIN" || true

if [[ $# -ge 1 ]]; then
  PROJECT_DIR="$1"
else
  if [[ -f "./pyproject.toml" || -d "./src/neumann_prover" || "$(basename "$(pwd)")" == "neumann-prover" ]]; then
    PROJECT_DIR="./lean_project"
  else
    PROJECT_DIR="$HOME/lean_project"
  fi
fi

mkdir -p "$PROJECT_DIR"
cd "$PROJECT_DIR"
elan override set "$TOOLCHAIN"
echo "$TOOLCHAIN" > lean-toolchain

ML_REF="${MATHLIB_REF:-v4.22.0}"
cat > lakefile.lean <<EOF
import Lake
open Lake DSL

package «lean_project» where

require «mathlib» from git
  "https://github.com/leanprover-community/mathlib4" @ "${ML_REF}"
EOF

lake update
lake exe cache get || true
lake build || true

export NEUMANN_LEAN_PROJECT="$PROJECT_DIR"
echo "Lean + Mathlib set up successfully at $PROJECT_DIR ✅"
