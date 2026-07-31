"""Thin client for the AXLE (Axiom Lean Engine) HTTP API.

AXLE runs Lean 4 + Mathlib cloud-side, per environment (e.g. "lean-4.32.0"), and is
used here as the INDEPENDENT verification leg of the triple-verification PROVED gate
(spec 2A). Never trust an engine's own success report blindly — this normalizes the
raw response to a strict `verified` boolean derived from the actual Lean messages.

Requires AXLE_API_KEY in the environment.
Docs: https://axle.axiommath.ai/v1/docs/
"""
from __future__ import annotations

import json
import os
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from typing import Any

AXLE_BASE = os.environ.get("AXLE_BASE_URL", "https://axle.axiommath.ai/api/v1")
DEFAULT_ENV = os.environ.get("AXLE_ENV", "lean-4.32.0")


class AxleError(RuntimeError):
    pass


@dataclass
class AxleResult:
    verified: bool
    environment: str
    errors: list[str] = field(default_factory=list)
    failed_declarations: list[str] = field(default_factory=list)
    raw: dict[str, Any] = field(default_factory=dict)


def _post(tool: str, payload: dict[str, Any], timeout: int = 120) -> dict[str, Any]:
    key = os.environ.get("AXLE_API_KEY")
    if not key:
        raise AxleError("AXLE_API_KEY not set in environment")
    url = f"{AXLE_BASE}/{tool}"
    data = json.dumps(payload).encode()
    req = urllib.request.Request(
        url,
        data=data,
        headers={
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="replace")
        raise AxleError(f"AXLE {tool} HTTP {e.code}: {body[:500]}") from e
    except urllib.error.URLError as e:
        raise AxleError(f"AXLE {tool} network error: {e}") from e


def _verdict_from_check(resp: dict[str, Any], environment: str) -> AxleResult:
    lean_msgs = resp.get("lean_messages") or {}
    errors = list(lean_msgs.get("errors") or [])
    warnings = list(lean_msgs.get("warnings") or [])
    failed = list(resp.get("failed_declarations") or [])
    okay = bool(resp.get("okay", False))
    # A `sorry` is a WARNING, not an error, so `okay` alone would pass it. Treat any
    # sorry/admit warning as a hard failure — a proof with a hole is never verified.
    sorry_hit = [w for w in warnings
                 if "sorry" in str(w).lower() or "admit" in str(w).lower()]
    if sorry_hit:
        errors = errors + [f"contains sorry/admit: {str(sorry_hit[0])[:120]}"]
    verified = okay and not errors and not failed and not sorry_hit
    return AxleResult(
        verified=verified,
        environment=(resp.get("info") or {}).get("environment", environment),
        errors=[str(e) for e in errors],
        failed_declarations=[str(f) for f in failed],
        raw=resp,
    )


def check(content: str, env: str = DEFAULT_ENV, timeout: int = 120) -> AxleResult:
    """Strict check that `content` compiles cleanly in the given AXLE environment."""
    resp = _post("check", {"content": content, "environment": env}, timeout=timeout)
    return _verdict_from_check(resp, env)


def verify_proof(
    candidate: str, statements: str, env: str = DEFAULT_ENV, timeout: int = 180
) -> AxleResult:
    """Verify `candidate` proves the theorems declared in `statements` (statement
    fidelity + validity). Falls back to the documented field names; normalizes to the
    same strict verdict shape as `check`."""
    resp = _post(
        "verify_proof",
        {"candidate": candidate, "statements": statements, "environment": env},
        timeout=timeout,
    )
    # verify_proof returns an `okay`/messages shape analogous to check; if it exposes a
    # dedicated match flag, require it too.
    result = _verdict_from_check(resp, env)
    if "verified" in resp:
        result.verified = result.verified and bool(resp["verified"])
    if resp.get("statement_mismatch"):
        result.verified = False
        result.errors.append("statement_mismatch")
    return result


if __name__ == "__main__":
    import sys

    src = sys.stdin.read() if len(sys.argv) < 2 else open(sys.argv[1]).read()
    r = check(src)
    print(json.dumps({"verified": r.verified, "environment": r.environment,
                      "errors": r.errors, "failed_declarations": r.failed_declarations}, indent=2))
    sys.exit(0 if r.verified else 1)
