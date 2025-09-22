
'''
src/neumann_prover/pipelines/batch.py

This module defines a single entry point `run_pipeline` that orchestrates the
entire autoformalization process. It can be run with defaults, or interactively
configured in a Colab/REPL setting to decide which artifacts to generate, which
models to use, and how many correction iterations to allow.

Helper functions:
- _ask_yes_no(prompt: str, default: bool) -> bool
  Interactive yes/no prompt with default choice.
- _ask_int(prompt: str, default: int) -> int
  Interactive integer prompt with default fallback.
- _ask_str(prompt: str, default: str) -> str
  Interactive string prompt with default fallback.
- _compile_mark(code: str) -> dict
  Normalize Lean code, run compilation, and return text, compiled flag, stdout, stderr.
- _ensure_proof_text(obj: Any) -> str
  Extract Lean proof text from either a raw string or dict returned by generator.

Main function:

run_pipeline(
    informal_inputs: List[str],
    output_informal_proofs: bool = True,
    output_formal_statements: bool = True,
    output_pseudocode: bool = True,
    input_custom_models: bool = False,
    model_informal: Optional[str] = None,
    model_statement: Optional[str] = None,
    model_proof: Optional[str] = None,
    num_statement_iters: int = 3,
    num_proof_iters: int = 4,
    interactive: bool = True,
    run_full_pipeline: Optional[bool] = None,
) -> dict

Inputs:
  - informal_inputs: list of informal statements to process.
  - output_* flags: which artifacts to generate (informal proofs, formal statements, pseudocode).
  - input_custom_models: whether to ask for custom model ids interactively.
  - model_informal / model_statement / model_proof: optional model overrides; defaults from stages.py.
  - num_statement_iters / num_proof_iters: max correction attempts for statements/proofs.
  - interactive: if True, ask the user questions in Colab/REPL.
  - run_full_pipeline: if True, run defaults and skip questions.

Behavior:
  - Resolves defaults for outputs, models, and iteration limits.
  - If interactive, prompts the user unless run_full_pipeline is set.
  - Announces which stages will run and which models will be used.
  - For each input: optionally generate informal proof, pseudocode,
    formal statement (with correction), and formal proof (with correction).
  - Compiles statements and proofs, counting how many succeed.

Returns:
  {
    "items": [
       {
         "input": <str>,
         "informal_proof": {"text": str} | None,
         "pseudocode": {"text": str} | None,
         "formal_statement": {"text": str, "compiled": bool, "stdout": str, "stderr": str} | None,
         "formal_proof": {"text": str, "compiled": bool, "stdout": str, "stderr": str} | None,
       }, ...
    ],
    "config": {...},   # resolved config used for this run
    "summary": {...},  # item counts and compile counts
  }
'''

from __future__ import annotations
from typing import Any, Dict, List, Optional
import time

from neumann_prover import stages
from neumann_prover.pipelines.informal import informal_proof_generator, lean_pseudocode_generator
from neumann_prover.pipelines.formal_statement import formal_statement_generator
from neumann_prover.pipelines.formal_proof import formal_proof_generator
from neumann_prover.correction import (
    formal_statement_until_compiles,
    try_formal_proof_until_compiles,
)
from neumann_prover.utils import extract_lean_code, ensure_import_mathlib, compile_lean_snippet


_STAGE_ALIAS = {
    "informal_proof": "informal_proof",
    "formal_statement": "formal_statement_draft",
    "formal_proof": "formal_proof_draft",
}

def _stage(name: str) -> str:
    return _STAGE_ALIAS.get(name, name)


def _ask_yes_no(prompt: str, default: bool) -> bool:
    d = "Y/n" if default else "y/N"
    ans = input(f"{prompt} ({d}): ").strip().lower()
    if not ans:
        return default
    return ans in {"y", "yes"}

def _ask_int(prompt: str, default: int) -> int:
    ans = input(f"{prompt} (default {default}): ").strip()
    if not ans:
        return default
    try:
        return int(ans)
    except ValueError:
        print("  Invalid integer; using default.")
        return default

def _ask_str(prompt: str, default: str) -> str:
    ans = input(f"{prompt} (default '{default}'): ").strip()
    return ans or default


# ---------------------------
# Small utilities
# ---------------------------
def _compile_mark(code: str) -> Dict[str, Any]:
    """Normalize Lean code, compile, and return diagnostics."""
    prepared = ensure_import_mathlib(extract_lean_code(code))
    ok, stdout, stderr = compile_lean_snippet(prepared)
    return {
        "text": prepared,
        "compiled": bool(ok),
        "stdout": stdout,
        "stderr": stderr,
    }

def _ensure_proof_text(obj: Any) -> str:
    """Accept either a raw Lean string or the dict from formal_proof_generator."""
    if isinstance(obj, str):
        return obj
    if isinstance(obj, dict):
        return obj.get("lean_code", "") or ""
    return str(obj or "")


# ---------------------------
# Main function:

def run_pipeline(
    *,
    informal_inputs: List[Any],   # each item may be a str or a dict with fields below
    # Generation toggles (used only for missing components)
    output_informal_proofs: bool = True,
    output_formal_statements: bool = True,
    output_pseudocode: bool = True,
    # Models (leave None to use stage defaults)
    model_informal: Optional[str] = None,
    model_statement: Optional[str] = None,
    model_proof: Optional[str] = None,
    # Iteration limits
    num_statement_iters: int = 3,
    num_proof_iters: int = 4,
    # Interactivity flags (kept for API stability; not used by this headless path)
    interactive: bool = False,
    run_full_pipeline: Optional[bool] = None,
) -> Dict[str, Any]:
    """
    Accepts a list where each item is either:
      - a string: interpreted as 'informal_text', or
      - a dict with any of the keys:
          'informal_text', 'informal_proof', 'pseudocode',
          'formal_statement', 'formal_proof'
    For any missing component, the pipeline will generate it (subject to the
    output_* toggles). For any provided formal code, we compile it; if it fails
    and there are correction iterations, we may attempt a corrective run.
    """

    # Resolve default models once
    if not model_informal:
        model_informal = stages.default_model_for(_stage("informal_proof"))
    if not model_statement:
        model_statement = stages.default_model_for(_stage("formal_statement"))
    if not model_proof:
        model_proof = stages.default_model_for(_stage("formal_proof"))


    # Announce plan minimally
    if output_informal_proofs:
        print(f"Will generate missing informal proofs with {model_informal}.")
    if output_pseudocode:
        print(f"Will generate missing pseudocode with {model_informal}.")
    if output_formal_statements:
        print(f"Will generate/correct missing formal statements with {model_statement}.")
    print(f"Will generate/correct missing formal proofs with {model_proof}.")

    items: List[Dict[str, Any]] = []
    stmt_compiled = 0
    proof_compiled = 0
    t_start = time.perf_counter()

    # Normalize inputs into dicts
    norm_inputs: List[Dict[str, Any]] = []
    for it in informal_inputs:
        if isinstance(it, str):
            norm_inputs.append({"informal_text": it})
        elif isinstance(it, dict):
            # shallow copy to avoid mutating caller data
            norm_inputs.append({k: v for k, v in it.items()})
        else:
            norm_inputs.append({"informal_text": str(it)})

    for entry in norm_inputs:
        rec: Dict[str, Any] = {}
        informal_text: str = entry.get("informal_text", "").strip()
        rec["input"] = informal_text if informal_text else entry

        # 1) Informal proof
        if entry.get("informal_proof") is not None:
            rec["informal_proof"] = {"text": str(entry["informal_proof"])}
        elif output_informal_proofs and informal_text:
            rec["informal_proof"] = {"text": informal_proof_generator(informal_text, model=model_informal)}
        else:
            rec["informal_proof"] = None

        # 2) Pseudocode
        if entry.get("pseudocode") is not None:
            rec["pseudocode"] = {"text": str(entry["pseudocode"])}
        elif output_pseudocode and informal_text:
            rec["pseudocode"] = {"text": lean_pseudocode_generator(informal_text, model=model_informal)}
        else:
            rec["pseudocode"] = None

        # 3) Formal statement (text + compile + (optional) correction)
        #    If provided: compile it. If missing and toggled on: generate+correct.
        stmt_block = None
        provided_stmt = entry.get("formal_statement")
        if provided_stmt is not None:
            stmt_mark = _compile_mark(str(provided_stmt))
            # If provided statement fails and we have correction budget, try loop
            if (not stmt_mark["compiled"]) and output_formal_statements and num_statement_iters > 1 and informal_text:
                gen_stmt = formal_statement_until_compiles(informal_text, model=model_statement, max_iters=num_statement_iters)
                stmt_mark = _compile_mark(gen_stmt)
            stmt_block = stmt_mark
        elif output_formal_statements and informal_text:
            if num_statement_iters > 1:
                gen_stmt = formal_statement_until_compiles(informal_text, model=model_statement, max_iters=num_statement_iters)
            else:
                gen_stmt = formal_statement_generator(informal_text, model=model_statement)
            stmt_block = _compile_mark(gen_stmt)

        rec["formal_statement"] = stmt_block
        if stmt_block and stmt_block.get("compiled"):
            stmt_compiled += 1

        # 4) Formal proof (text + compile + (optional) correction)
        proof_block = None
        provided_proof = entry.get("formal_proof")
        if provided_proof is not None:
            proof_mark = _compile_mark(_ensure_proof_text(provided_proof))
            # If provided proof fails and we have correction budget, try loop
            if (not proof_mark["compiled"]) and num_proof_iters > 1 and informal_text:
                gen_proof_obj = try_formal_proof_until_compiles(informal_text, model=model_proof, max_iters=num_proof_iters)
                gen_proof_text = _ensure_proof_text(gen_proof_obj)
                proof_mark = _compile_mark(gen_proof_text)
            proof_block = proof_mark
        else:
            # No provided proof: attempt generation/correction if we have an input
            if informal_text:
                if num_proof_iters > 1:
                    gen_proof_obj = try_formal_proof_until_compiles(informal_text, model=model_proof, max_iters=num_proof_iters)
                    gen_proof_text = _ensure_proof_text(gen_proof_obj)
                else:
                    gen_proof_text = _ensure_proof_text(formal_proof_generator(informal_text, model=model_proof))
                proof_block = _compile_mark(gen_proof_text)

        rec["formal_proof"] = proof_block
        if proof_block and proof_block.get("compiled"):
            proof_compiled += 1

        items.append(rec)

    summary = {
        "n_items": len(items),
        "statements_compiled": stmt_compiled,
        "proofs_compiled": proof_compiled,
        "elapsed_sec": round(time.perf_counter() - t_start, 3),
    }

    print("[run_pipeline] Done.")
    print(f"  Items: {summary['n_items']}")
    print(f"  Formal statements compiled: {summary['statements_compiled']}")
    print(f"  Formal proofs compiled:     {summary['proofs_compiled']}")

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

# CLI entry point
# ---------------------------

def cli_main():
    import argparse, json, pathlib

    p = argparse.ArgumentParser(description="Neumann-prover: headless batch runner")
    p.add_argument("--inputs", required=True, help="JSONL file; one problem per line")
    p.add_argument("--outdir", required=True, help="Directory for outputs")
    p.add_argument("--run-full-pipeline", action="store_true", default=False)
    p.add_argument("--interactive", default="false")
    p.add_argument("--num-statement-iters", type=int, default=1)
    p.add_argument("--num-proof-iters", type=int, default=1)
    args = p.parse_args()

    # Allow either JSONL objects with {"informal_text": "..."} or raw lines
    samples: List[str] = []
    with open(args.inputs) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
                samples.append(obj)  # pass the whole object (may include proofs, etc.)
            except json.JSONDecodeError:
                samples.append(line)

    outdir = pathlib.Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    result = run_pipeline(
        informal_inputs=samples,
        interactive=(args.interactive.lower() == "true"),
        run_full_pipeline=args.run_full_pipeline,
        num_statement_iters=args.num_statement_iters,
        num_proof_iters=args.num_proof_iters,
    )

    # 1) Detailed records (JSONL)
    with open(outdir / "records.jsonl", "w") as g:
        for it in result["items"]:
            g.write(json.dumps(it) + "\n")

    # 2) Machine-readable summaries
    (outdir / "summary.json").write_text(json.dumps(result.get("summary", {}), indent=2))
    (outdir / "config.json").write_text(json.dumps(result.get("config", {}), indent=2))

    # 3) Human-readable summary.txt
    s = result.get("summary", {})
    lines = [
        f"Items: {s.get('n_items', 0)}",
        f"Formal statements compiled: {s.get('statements_compiled', 0)}",
        f"Formal proofs compiled:     {s.get('proofs_compiled', 0)}",
        f"Elapsed (sec):              {s.get('elapsed_sec', 'NA')}",
    ]
    (outdir / "summary.txt").write_text("\n".join(lines) + "\n")
