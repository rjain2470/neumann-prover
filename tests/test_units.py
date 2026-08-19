"""Pure-logic unit tests — no API keys, no Lean toolchain required.

The Lean compiler is monkeypatched so `verify_lean`'s soundness logic can be
exercised deterministically. End-to-end compilation is covered separately.
"""
import importlib

import neumann_prover.utils as U
from neumann_prover.utils import (
    extract_lean_code, ensure_import_mathlib, verify_lean, _parse_axioms,
)
from neumann_prover.providers import _provider_for, _accepts_temperature

# The package re-exports a function named `ask_llm`, which shadows the submodule
# attribute — fetch the real module explicitly.
A = importlib.import_module("neumann_prover.ask_llm")


# ------------------------- extraction -------------------------

def test_extract_prefers_last_fenced_block():
    text = "blah\n```lean\nimport Mathlib\ntheorem a : True := trivial\n```\nnote\n```lean4\nimport Mathlib\ntheorem b : True := trivial\n```"
    assert "theorem b" in extract_lean_code(text)
    assert "theorem a" not in extract_lean_code(text)


def test_extract_no_fence_keeps_from_import():
    text = "Here is the code:\nimport Mathlib\ntheorem t : True := trivial"
    out = extract_lean_code(text)
    assert out.startswith("import Mathlib")


def test_extract_namespace_agnostic():
    # No `end Demo` sentinel required anymore.
    text = "```lean4\nimport Mathlib\nnamespace Foo\ntheorem t : True := trivial\nend Foo\n```"
    out = extract_lean_code(text)
    assert "namespace Foo" in out and "end Foo" in out


def test_ensure_import_mathlib_idempotent():
    code = "import Mathlib\ntheorem t : True := trivial"
    once = ensure_import_mathlib(code)
    assert once == ensure_import_mathlib(once)
    assert once.count("import Mathlib") == 1
    assert ensure_import_mathlib("theorem t : True := trivial").startswith("import Mathlib")


# ------------------------- provider routing -------------------------

def test_provider_inference():
    assert _provider_for("gpt-5") == "openai"
    assert _provider_for("o3-mini") == "openai"
    assert _provider_for("claude-opus-4-8") == "anthropic"
    assert _provider_for("opus-4-8") == "anthropic"
    assert _provider_for("deepseek-ai/DeepSeek-Prover-V2") == "together"


def test_temperature_policy():
    assert _accepts_temperature("gpt-5") is False
    assert _accepts_temperature("claude-opus-4-8") is False
    assert _accepts_temperature("claude-opus-4-7") is False
    assert _accepts_temperature("claude-sonnet-4-6") is True
    assert _accepts_temperature("gpt-4o") is True


# ------------------------- ask_llm dispatch -------------------------

def test_ask_llm_dispatches_and_passes_temperature(monkeypatch):
    seen = {}

    def fake(name):
        def _f(model, text, temperature=None):
            seen["provider"] = name
            seen["model"] = model
            seen["temperature"] = temperature
            return f"{name}:{model}"
        return _f

    monkeypatch.setattr(A, "_ask_openai", fake("openai"))
    monkeypatch.setattr(A, "_ask_anthropic", fake("anthropic"))
    monkeypatch.setattr(A, "_ask_together", fake("together"))

    assert A.ask_llm("hi", model="claude-opus-4-8") == "anthropic:claude-opus-4-8"
    assert seen["provider"] == "anthropic"
    A.ask_llm("hi", model="Qwen/Qwen2.5", temperature=0.7)
    assert seen["provider"] == "together" and seen["temperature"] == 0.7


# ------------------------- verify_lean (compiler mocked) -------------------------

def _fake_compile(ok, stdout="", stderr=""):
    def _c(code, project_root=None, filename="Main.lean", *, timeout=300):
        return ok, stdout, stderr
    return _c


def test_proof_with_sorry_rejected_without_compiling(monkeypatch):
    # Static scan fires first; compiler must never be called.
    def boom(*a, **k):
        raise AssertionError("compiler should not run when sorry is present")
    monkeypatch.setattr(U, "compile_lean_snippet", boom)
    res = verify_lean("import Mathlib\ntheorem t : True := by sorry", expect="proof")
    assert not res.ok and "sorry" in res.reason


def test_proof_with_native_decide_rejected(monkeypatch):
    monkeypatch.setattr(U, "compile_lean_snippet", _fake_compile(True))
    res = verify_lean("import Mathlib\ntheorem t : 2 = 2 := by native_decide", expect="proof")
    assert not res.ok and "native_decide" in res.reason


def test_clean_proof_accepted(monkeypatch):
    axioms = "'Demo.t' depends on axioms: [propext, Classical.choice, Quot.sound]"
    monkeypatch.setattr(U, "compile_lean_snippet", _fake_compile(True, stdout=axioms))
    res = verify_lean("import Mathlib\ntheorem t : True := trivial", expect="proof")
    assert res.ok and set(res.axioms) <= U.AXIOM_WHITELIST


def test_proof_with_bad_axiom_rejected(monkeypatch):
    axioms = "'Demo.t' depends on axioms: [propext, sorryAx]"
    monkeypatch.setattr(U, "compile_lean_snippet", _fake_compile(True, stdout=axioms))
    res = verify_lean("import Mathlib\ntheorem t : True := trivial", expect="proof")
    assert not res.ok and "sorryAx" in res.reason


def test_proof_sorry_warning_rejected(monkeypatch):
    warn = "Main.lean:2:8: warning: declaration uses 'sorry'"
    monkeypatch.setattr(U, "compile_lean_snippet", _fake_compile(True, stdout=warn))
    # Aliased sorry that slips past the regex would still be caught by the warning.
    res = verify_lean("import Mathlib\ntheorem t : True := by exact?", expect="proof")
    assert not res.ok and "sorry" in res.reason


def test_statement_with_sorry_accepted(monkeypatch):
    monkeypatch.setattr(U, "compile_lean_snippet", _fake_compile(True))
    res = verify_lean("import Mathlib\ntheorem t : True := by\n  sorry", expect="statement")
    assert res.ok


def test_statement_with_native_decide_rejected(monkeypatch):
    monkeypatch.setattr(U, "compile_lean_snippet", _fake_compile(True))
    res = verify_lean("import Mathlib\ntheorem t : 2=2 := by native_decide", expect="statement")
    assert not res.ok


def test_parse_axioms():
    assert _parse_axioms("'x' depends on axioms: [propext, Quot.sound]") == ["propext", "Quot.sound"]
    assert _parse_axioms("'x' does not depend on any axioms") == []
