"""End-to-end smoke test (needs a built lean_project; Part B also needs API keys).

Run:  NEUMANN_LEAN_PROJECT=./lean_project python tests/e2e_smoke.py

Part A (no API keys): drives `verify_lean` against the REAL Lean compiler on
hand-written snippets — this is the load-bearing check that the soundness layer
rejects reward-hacking (`sorry` / `native_decide`) that a bare exit-code check
would have accepted. Part B runs the full pipeline if keys are present.
"""
import os
import sys

os.environ.setdefault("NEUMANN_LEAN_PROJECT", os.path.abspath("lean_project"))

from neumann_prover.utils import verify_lean  # noqa: E402

CLEAN = """import Mathlib
namespace Demo
theorem four_dvd_sq_of_even (n : Int) (h : ∃ k, n = 2 * k) : (4 : Int) ∣ n ^ 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k ^ 2, by ring⟩
end Demo
"""

SORRY = """import Mathlib
namespace Demo
theorem four_dvd_sq_of_even (n : Int) (h : ∃ k, n = 2 * k) : (4 : Int) ∣ n ^ 2 := by
  sorry
end Demo
"""

NATIVE = """import Mathlib
namespace Demo
theorem foo : (2 : Nat) + 2 = 4 := by native_decide
end Demo
"""


def part_a() -> bool:
    print("=== Part A: soundness against the real compiler ===")
    ok = True
    r = verify_lean(CLEAN, expect="proof")
    print(f"clean proof        -> ok={r.ok} axioms={r.axioms} reason={r.reason!r}")
    ok &= r.ok

    r = verify_lean(SORRY, expect="proof")
    print(f"sorry proof        -> ok={r.ok} reason={r.reason!r}  (must be rejected)")
    ok &= (not r.ok)

    r = verify_lean(NATIVE, expect="proof")
    print(f"native_decide proof-> ok={r.ok} reason={r.reason!r}  (must be rejected)")
    ok &= (not r.ok)

    r = verify_lean(SORRY, expect="statement")
    print(f"statement (sorry)  -> ok={r.ok}  (must be accepted)")
    ok &= r.ok
    print("Part A:", "PASS" if ok else "FAIL")
    return ok


def part_b() -> bool:
    if not (os.environ.get("OPENAI_API_KEY") and os.environ.get("ANTHROPIC_API_KEY")):
        print("\n=== Part B: skipped (no OPENAI/ANTHROPIC keys) ===")
        return True
    print("\n=== Part B: full pipeline on one example ===")
    from neumann_prover import run_pipeline
    res = run_pipeline(
        informal_inputs=[{
            "id": "ex1",
            "informal_text": "For every even integer n, 4 divides n^2.",
            "informal_proof": "If n is even, n = 2k, so n^2 = 4k^2, divisible by 4.",
        }],
        num_statement_iters=2,
        num_proof_iters=3,
    )
    print("summary:", res["summary"])
    return True


if __name__ == "__main__":
    a = part_a()
    b = part_b()
    sys.exit(0 if (a and b) else 1)
