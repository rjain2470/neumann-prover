"""Provider adapters and provider inference.

Each adapter calls its vendor SDK and returns plain text. SDKs are imported
lazily inside each adapter so the package imports without all three installed
(and so tests can run with none of them).

Temperature policy: many current models reject `temperature` — gpt-5 reasoning
models and Claude Opus 4.7/4.8 return a 400 if it is sent. `temperature` is
therefore optional everywhere and only forwarded when the caller sets it *and*
the target model accepts it (`_accepts_temperature`).
"""
from __future__ import annotations

import os
from typing import Literal, Optional

Provider = Literal["openai", "anthropic", "together"]

# Generous ceiling so long proofs are not truncated (well under the
# non-streaming HTTP-timeout limit).
_MAX_TOKENS = 16000


# ------------------------ secrets helpers ------------------------

def _get_secret(name: str) -> Optional[str]:
    """Read an API key from the environment, falling back to Colab userdata."""
    val = os.getenv(name)
    if val:
        return val
    try:
        import google.colab.userdata as _ud  # type: ignore
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


# ------------------------ provider inference ------------------------

def _provider_for(model: str) -> Provider:
    """Infer the provider from a model id. Together is the catch-all for the
    open-source models it hosts (DeepSeek, Qwen, Meta, ...)."""
    m = model.lower()
    if m.startswith(("gpt-", "o1", "o3", "o4", "chatgpt")):
        return "openai"
    if "claude" in m or m.startswith(("opus", "sonnet", "haiku")):
        return "anthropic"
    return "together"


def _accepts_temperature(model: str) -> bool:
    """gpt-5 reasoning models and Claude Opus 4.7/4.8 reject `temperature`."""
    m = model.lower()
    if m.startswith("gpt-5") or m.startswith(("o1", "o3", "o4")):
        return False
    if "opus-4-7" in m or "opus-4-8" in m:
        return False
    return True


# ------------------------ provider adapters ------------------------

def _ask_openai(model: str, text: str, temperature: Optional[float] = None) -> str:
    from openai import OpenAI

    client = OpenAI(api_key=_require_key("OPENAI_API_KEY"))
    kwargs: dict = {}
    if temperature is not None and _accepts_temperature(model):
        kwargs["temperature"] = temperature
    r = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": text}],
        **kwargs,
    )
    return r.choices[0].message.content or ""


def _ask_anthropic(model: str, text: str, temperature: Optional[float] = None) -> str:
    import anthropic

    client = anthropic.Anthropic(api_key=_require_key("ANTHROPIC_API_KEY"))
    kwargs: dict = {}
    if temperature is not None and _accepts_temperature(model):
        kwargs["temperature"] = temperature
    else:
        # Adaptive thinking is the recommended mode for Claude 4.6+ and helps
        # markedly on Lean proofs; it is incompatible with `temperature`.
        kwargs["thinking"] = {"type": "adaptive"}
    r = client.messages.create(
        model=model,
        max_tokens=_MAX_TOKENS,
        messages=[{"role": "user", "content": text}],
        **kwargs,
    )
    # Concatenate text blocks; ignore thinking / tool blocks.
    return "".join(
        b.text for b in getattr(r, "content", []) if getattr(b, "type", None) == "text"
    )


def _ask_together(model: str, text: str, temperature: Optional[float] = None) -> str:
    from together import Together

    client = Together(api_key=_require_key("TOGETHER_API_KEY"))
    kwargs: dict = {}
    if temperature is not None:
        kwargs["temperature"] = temperature
    r = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": text}],
        **kwargs,
    )
    return r.choices[0].message.content or ""
