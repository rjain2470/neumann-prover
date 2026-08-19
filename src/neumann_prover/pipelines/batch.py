"""Batch orchestrator: `run_pipeline` runs the full cascade over many inputs,
plus a headless `neumann-prover` CLI.

Each input is a string (informal text) or a dict with any of `informal_text`,
`informal_proof`, `pseudocode`, `formal_statement`, `formal_proof`. Missing
pieces are generated (subject to the output_* toggles). Formal artifacts are
*verified* (sound: no sorry/native_decide, whitelisted axioms), not merely
compiled; the verified formal statement is threaded into the proof stage so the
proof targets the theorem that was checked.
"""
from __future__ import annotations

import time
from typing import Any, Optional

from neumann_prover import stages
from neumann_prover.pipelines.informal import informal_proof_generator, lean_pseudocode_generator
from neumann_prover.pipelines.formal_statement import formal_statement_generator
from neumann_prover.pipelines.formal_proof import formal_proof_generator
from neumann_prover.correction import (
    formal_statement_until_compiles,
    try_formal_proof_until_compiles,
)
from neumann_prover.utils import extract_lean_code, ensure_import_mathlib, verify_lean


def _block(code: str, expect: str) -> dict[str, Any]:
    """Verify one Lean snippet and package the diagnostics."""
    text = ensure_import_mathlib(extract_lean_code(code))
    res = verify_lean(text, expect=expect)
    return {
        "text": text,
        "compiled": res.ok,          # sound success, not bare exit code
        "stdout": res.stdout,
        "stderr": res.stderr,
        "reason": res.reason,
    }


def _block_from_loop(loop: dict[str, Any]) -> dict[str, Any]:
    """Package the result of a correction loop into a record block."""
    attempts = loop.get("attempts") or [{}]
    last = attempts[-1]
    return {
        "text": loop.get("final_code") or last.get("lean_code", ""),
        "compiled": bool(loop.get("success")),
        "stdout": last.get("stdout", ""),
        "stderr": last.get("stderr", ""),
        "reason": last.get("reason", ""),
    }


def _proof_text(obj: Any) -> str:
    if isinstance(obj, dict):
        return obj.get("lean_code", "") or ""
    return str(obj or "")


def run_pipeline(
    *,
    informal_inputs: list[Any],
    output_informal_proofs: bool = True,
    output_formal_statements: bool = True,
    output_pseudocode: bool = True,
    model_informal: Optional[str] = None,
    model_statement: Optional[str] = None,
    model_proof: Optional[str] = None,
    num_statement_iters: int = 3,
    num_proof_iters: int = 4,
    # accepted for API stability; this path is headless
    interactive: bool = False,
    run_full_pipeline: Optional[bool] = None,
) -> dict[str, Any]:
    model_informal = model_informal or stages.default_model_for("informal_proof")
    model_statement = model_statement or stages.default_model_for("formal_statement")
    model_proof = model_proof or stages.default_model_for("formal_proof")

    print(f"Informal proofs: {model_informal} | statements: {model_statement} | proofs: {model_proof}")

    items: list[dict[str, Any]] = []
    stmt_ok = proof_ok = 0
    t_start = time.perf_counter()

    for raw in informal_inputs:
        entry = {"informal_text": raw} if isinstance(raw, str) else dict(raw)
        informal_text = str(entry.get("informal_text", "")).strip()
        rec: dict[str, Any] = {"input": informal_text or entry}

        # 1) Informal proof
        if entry.get("informal_proof") is not None:
            rec["informal_proof"] = {"text": str(entry["informal_proof"])}
        elif output_informal_proofs and informal_text:
            rec["informal_proof"] = {"text": informal_proof_generator(informal_text, model=model_informal)}
        else:
            rec["informal_proof"] = None
        inf_proof = rec["informal_proof"]["text"] if rec["informal_proof"] else None

        # 2) Pseudocode (from the informal proof, not the raw statement)
        if entry.get("pseudocode") is not None:
            rec["pseudocode"] = {"text": str(entry["pseudocode"])}
        elif output_pseudocode and inf_proof:
            rec["pseudocode"] = {"text": lean_pseudocode_generator(inf_proof, model=model_informal)}
        else:
            rec["pseudocode"] = None
        pseudo = rec["pseudocode"]["text"] if rec["pseudocode"] else None

        # 3) Formal statement (verify; generate/correct if missing or unsound)
        stmt_block = None
        provided_stmt = entry.get("formal_statement")
        if provided_stmt is not None:
            stmt_block = _block(str(provided_stmt), "statement")
            if not stmt_block["compiled"] and output_formal_statements and num_statement_iters > 1 and informal_text:
                stmt_block = _block(
                    formal_statement_until_compiles(informal_text, model=model_statement, max_iters=num_statement_iters),
                    "statement",
                )
        elif output_formal_statements and informal_text:
            if num_statement_iters > 1:
                gen = formal_statement_until_compiles(informal_text, model=model_statement, max_iters=num_statement_iters)
            else:
                gen = formal_statement_generator(informal_text, model=model_statement)
            stmt_block = _block(gen, "statement")

        rec["formal_statement"] = stmt_block
        stmt_ok += bool(stmt_block and stmt_block["compiled"])
        # Thread the verified statement into the proof stage (source of truth).
        stmt_text = stmt_block["text"] if stmt_block else provided_stmt

        # 4) Formal proof
        proof_block = None
        provided_proof = entry.get("formal_proof")
        if provided_proof is not None:
            proof_block = _block(_proof_text(provided_proof), "proof")
            if not proof_block["compiled"] and num_proof_iters > 1 and informal_text:
                proof_block = _block_from_loop(try_formal_proof_until_compiles(
                    informal_statement=informal_text, informal_proof=inf_proof,
                    pseudocode=pseudo, formal_statement=stmt_text,
                    model=model_proof, max_iters=num_proof_iters,
                ))
        elif informal_text:
            if num_proof_iters > 1:
                proof_block = _block_from_loop(try_formal_proof_until_compiles(
                    informal_statement=informal_text, informal_proof=inf_proof,
                    pseudocode=pseudo, formal_statement=stmt_text,
                    model=model_proof, max_iters=num_proof_iters,
                ))
            else:
                gen = formal_proof_generator(
                    informal_text, informal_proof=inf_proof, pseudocode=pseudo,
                    formal_statement=stmt_text, model=model_proof,
                )
                proof_block = _block(gen["lean_code"], "proof")

        rec["formal_proof"] = proof_block
        proof_ok += bool(proof_block and proof_block["compiled"])
        items.append(rec)

    summary = {
        "n_items": len(items),
        "statements_verified": stmt_ok,
        "proofs_verified": proof_ok,
        "elapsed_sec": round(time.perf_counter() - t_start, 3),
    }
    print(f"[run_pipeline] Done. items={summary['n_items']} "
          f"statements_verified={stmt_ok} proofs_verified={proof_ok}")

    return {
        "items": items,
        "config": {
            "output_informal_proofs": output_informal_proofs,
            "output_formal_statements": output_formal_statements,
            "output_pseudocode": output_pseudocode,
            "model_informal": model_informal,
            "model_statement": model_statement,
            "model_proof": model_proof,
            "num_statement_iters": num_statement_iters,
            "num_proof_iters": num_proof_iters,
            "interactive": interactive,
            "run_full_pipeline": run_full_pipeline,
        },
        "summary": summary,
    }


# --------------------------------------------------------------------------
# CLI entry point
# --------------------------------------------------------------------------

def cli_main() -> None:
    import argparse, json, pathlib

    p = argparse.ArgumentParser(description="Neumann-prover: headless batch runner")
    p.add_argument("--inputs", required=True, help="JSONL file; one problem per line")
    p.add_argument("--outdir", required=True, help="Directory for outputs")
    p.add_argument("--num-statement-iters", type=int, default=3)
    p.add_argument("--num-proof-iters", type=int, default=4)
    args = p.parse_args()

    samples: list[Any] = []
    with open(args.inputs) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                samples.append(json.loads(line))
            except json.JSONDecodeError:
                samples.append(line)

    outdir = pathlib.Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    result = run_pipeline(
        informal_inputs=samples,
        num_statement_iters=args.num_statement_iters,
        num_proof_iters=args.num_proof_iters,
    )

    with open(outdir / "records.jsonl", "w") as g:
        for it in result["items"]:
            g.write(json.dumps(it) + "\n")
    (outdir / "summary.json").write_text(json.dumps(result["summary"], indent=2))
    (outdir / "config.json").write_text(json.dumps(result["config"], indent=2))
