# Changelog

## 0.2.0 — debug & modernize (cleanup/debug-modernize)

A debug + cleanup pass over the 0.1 codebase. No new framework dependencies; the
DSP-style cascade (informal → informal proof → pseudocode → formal statement →
formal proof, with compile-feedback correction) is unchanged in spirit. All unit
tests pass and the pipeline was verified end-to-end against real Lean 4 / Mathlib.

### Soundness / correctness (the important part)
- **Sound proof verification (`utils.verify_lean`).** Success now means *sound*,
  not just "the compiler exited 0". A proof is rejected if it uses
  `sorry` / `admit` / `native_decide` / `sorryAx`, if the compiler emits a
  "declaration uses 'sorry'" warning, or if `#print axioms` reports any axiom
  outside `{propext, Classical.choice, Quot.sound}`. Previously a `sorry` proof
  compiled (warning, exit 0) and was counted as solved — the classic
  reward-hacking hole.
- **Statement/proof recoupling.** `run_pipeline` now threads the *verified* formal
  statement into the proof stage instead of letting the proof stage re-formalize
  from the informal text, so the proof targets the theorem that was checked.
- **Anthropic truncation fixed.** `max_tokens` raised from 2048 to 16000.
- **Safer compilation.** `compile_lean_snippet` no longer interpolates paths into a
  `bash -lc` string (runs `lake env lean` with `cwd`/args) and has a timeout.

### Providers & models
- Model defaults centralized in `stages.py` and updated to current-best:
  Claude **Opus 4.8** / **Sonnet 4.6** (were `opus-4-1` / `sonnet-4`); OpenAI gpt-5 family.
- **Temperature handled correctly.** gpt-5 reasoning models and Claude Opus 4.7/4.8
  reject `temperature` (HTTP 400). It is now optional and only forwarded to models
  that accept it; the Anthropic adapter uses adaptive thinking instead.
- **Lazy SDK imports.** `openai`/`anthropic`/`together` are imported inside their
  adapters, so the package imports (and unit tests run) without all three installed.
- `_provider_for` hardened (o-series, explicit Claude prefixes).

### Cleanup
- `extract_lean_code` rewritten: takes the last fenced ```lean(4)``` block,
  namespace-agnostic (no hard-coded `end Demo`).
- Pseudocode stage wired in properly (was dead code / arg-mismatched) — it now
  translates the informal proof.
- `formal_statement_generator` returns Lean code directly (was a report string that
  callers re-parsed) and no longer double-compiles.
- Unified Lean-project-root resolution (`utils.resolve_project_root`); dropped the
  Colab `/content/lean_project` default.
- Removed unused interactive CLI helpers; simplified the CLI flags.
- `requires-python` bumped to `>=3.10` (the code already used `X | None` syntax).

### Tests
- `tests/test_units.py`: pure-logic pytest suite (mocked compiler/LLM, no keys) —
  extraction, provider routing, temperature policy, dispatch, and the full
  `verify_lean` soundness matrix.
- `tests/e2e_smoke.py`: drives `verify_lean` against the real compiler (Part A) and
  runs the full pipeline when API keys are present (Part B).
