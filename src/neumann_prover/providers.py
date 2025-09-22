"""
src/neumann_prover/providers.py

Provider adapters and provider inference. Each adapter calls its vendor SDK
and returns plain text. No notebook-only dependencies at import time.

Functions:

_provider_for(model: str) -> Literal["openai","anthropic","together"]
    Infer provider name from a model identifier.

_ask_openai(model: str, text: str, temperature: float = 0.2) -> str
_ask_anthropic(model: str, text: str, temperature: float = 0.2) -> str
_ask_together(model: str, text: str, temperature: float = 0.2) -> str
"""

import os
from typing import Literal, Optional

from openai import OpenAI
import anthropic
from together import Together


# ------------------------ secrets helpers ------------------------

def _get_secret(name: str) -> Optional[str]:
    """Read API key from environment; optionally fall back to Colab userdata."""
    val = os.getenv(name)
    if val:
        return val
    try:
        import google.colab.userdata as _ud  # optional; safe elsewhere
        return _ud.get(name)
    except Exception:
        return None


def _require_key(name: str) -> str:
    key = _get_secret(name)
    if not key:
        raise RuntimeError(
            f"{name} is not set. Export {name}=... in your shell "
            f"(or store it in Colab userdata) before running."
        )
    return key


# ------------------------ provider adapters ------------------------

def _ask_openai(model: str, text: str, temperature: float = 1.0) -> str:
    client = OpenAI(api_key=_require_key("OPENAI_API_KEY"))
    r = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": text}],
        temperature=temperature,
    )
    return r.choices[0].message.content


def _ask_anthropic(model: str, text: str, temperature: float = 0.5) -> str:
    client = anthropic.Anthropic(api_key=_require_key("ANTHROPIC_API_KEY"))
    r = client.messages.create(
        model=model,
        max_tokens=2048,
        temperature=temperature,
        messages=[{"role": "user", "content": text}],
    )
    # Concatenate text blocks; ignore tool blocks, etc.
    return "".join(
        b.text for b in getattr(r, "content", []) if getattr(b, "type", None) == "text"
    )


def _ask_together(model: str, text: str, temperature: float = 1.0) -> str:
    client = Together(api_key=_require_key("TOGETHER_API_KEY"))
    r = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": text}],
        temperature=temperature,
    )
    return r.choices[0].message.content


# ------------------------ provider inference ------------------------

def _provider_for(model: str) -> Literal["openai", "anthropic", "together"]:
    m = model.lower()
    if m.startswith("gpt-"):
        return "openai"
    if m.startswith("sonnet") or m.startswith("opus") or "claude" in m:
        return "anthropic"
    return "together"
