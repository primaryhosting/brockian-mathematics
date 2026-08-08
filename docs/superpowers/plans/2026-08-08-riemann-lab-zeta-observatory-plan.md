# Riemann Lab — Zeta Observatory Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the Zeta Observatory (`/observatory`) on torus.riemannlab.com — one crown-jewel experience with three depth layers (Surface cinema / Explore live compute / Rigor provenance) — in three published, eyes-on-verified increments.

**Architecture:** Local Python groundwork (dataset fetch + fleet push) lives in this repo (`~/Projects/brockian-mathematics`); all site code is built by the Lovable agent in project `dd8308ac-0860-42ae-908c-41b306b58858` via `mcp__claude_ai_Lovable__send_message` prompts with explicit file scope. Compute runs in the visitor's browser (TS + Web Worker kernel); proof authority is the sanitized `/verified-registry.json` (owned by the adjacent AI — never written by us); the Solver Fleet panel reads a Supabase row pushed by the existing solver-watch LaunchAgent.

**Tech Stack:** React + TS + Vite + Tailwind + shadcn (Lovable), react-three-fiber, Web Workers, Vitest (sandbox), Python 3 + pytest (local), Supabase (already enabled on the project), Lovable MCP tools.

**Spec:** `docs/superpowers/specs/2026-08-08-riemann-lab-zeta-observatory-platform-design.md` — read it before starting. Honesty invariants (§5) are hard requirements.

---

## Operating protocol (read once, applies to every Lovable task)

- **Sending work:** `mcp__claude_ai_Lovable__send_message` with `project_id: dd8308ac-0860-42ae-908c-41b306b58858`, `wait: false`. Then poll `get_message(message_id, thread_id: "main")` every ~60s until the agent's reply is complete (never `wait: true` — 300s MCP timeout).
- **Concurrent editor:** the builder-prover AI edits this project continuously. Before EVERY `send_message` that touches a shared file: call `list_edits(limit: 3)`, take the entry with max `created_at` (ordering is unreliable), and `read_file` the current version of any shared file you are about to have edited. Shared-file watchlist (the ONLY pre-existing files we edit): `src/site-registry.ts`, the primary nav component, the router file. Everything else we create new. NEVER touch `/public/verified-registry.json`, `/labs/riemann-gate1-operator`, or the adjacent AI's ledger/audit pages.
- **Verification per build:** (1) ask the Lovable agent in-message to run the Vitest suite and report output; (2) `read_file` spot-checks of created files; (3) in-sandbox crawl of `/observatory` — 0 console errors; (4) **EYES-ON GATE**: show the user the rendered result (preview URL + pinned-commit screenshot) and wait for explicit approval; (5) **PUBLISH GATE**: only after eyes-on approval, publish via `deploy_project` (or ask user to click Publish if the tool fails). Never ship on headless verification alone.
- **Preview lag** is ~5–10 min after a commit; don't declare a rendering bug until the preview has caught up.
- **Commits (local repo):** explicit paths only, never `git add -A`; `git commit --no-verify`; trailer `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>`.
- **Secrets:** never print or commit values of `RIEMANN_SUPABASE_SERVICE_KEY` or any vault var. Scripts read them from the environment (the LaunchAgent wrapper sources `~/.openclaw/vault-bridges.env` with `set -a`).

---

## Chunk 1: Dataset groundwork (local repo)

### Task 1: `scripts/fetch_zeta_zeros.py` — parse/convert core (TDD)

**Files:**
- Create: `scripts/fetch_zeta_zeros.py`
- Test: `tests/test_fetch_zeta_zeros.py` (create `tests/` if absent; check for an existing pytest layout first and follow it)

The script downloads Odlyzko's table of the first 100,000 zeta zeros (imaginary parts, one decimal per line, accurate to ~3e-9), converts to little-endian float64, cross-checks two ways (published literature values + mpmath — spec §4.3's "second independent source" requirement), and writes the dataset + provenance sidecar (the Lovable `manifest.json` is authored later, in Task 4). Network and mpmath work live in `main()`; parsing/validation/encoding are pure functions so tests need no network. Note: spec §4.3 says spot-verify "to 1e-9", but the source itself is only accurate to ~3e-9, so the achievable tolerance is 1e-8 — a deliberate deviation, recorded honestly in the sidecar.

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_fetch_zeta_zeros.py
import struct
import pytest
from scripts.fetch_zeta_zeros import parse_zeros_text, validate_zeros, encode_f64le

SAMPLE = """14.134725141734693790
21.022039638771554993
25.010857580145688763
"""

def test_parse_zeros_text():
    zeros = parse_zeros_text(SAMPLE)
    assert zeros == pytest.approx(
        [14.134725141734694, 21.022039638771555, 25.010857580145689], abs=1e-12)

def test_parse_skips_blank_lines():
    assert len(parse_zeros_text("14.1\n\n21.0\n")) == 2

def test_validate_accepts_increasing_positive():
    # first value must be the real first zero — validate_zeros checks it to 1e-6
    validate_zeros([14.134725141734693, 21.02, 25.01], expected_count=3)  # no raise

def test_validate_rejects_wrong_count():
    with pytest.raises(ValueError, match="expected 5"):
        validate_zeros([14.13, 21.02], expected_count=5)  # count check fires first

def test_validate_rejects_non_increasing():
    with pytest.raises(ValueError, match="increasing"):
        validate_zeros([14.134725141734693, 14.134725141734693, 25.01],
                       expected_count=3)

def test_validate_rejects_bad_first_zero():
    with pytest.raises(ValueError, match="first zero"):
        validate_zeros([1.0, 2.0], expected_count=2)

def test_encode_f64le_roundtrip():
    vals = [14.134725141734694, 21.022039638771555]
    blob = encode_f64le(vals)
    assert len(blob) == 16
    assert list(struct.unpack("<2d", blob)) == vals
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd ~/Projects/brockian-mathematics && python3 -m pytest tests/test_fetch_zeta_zeros.py -v`
Expected: FAIL / collection error — `ModuleNotFoundError: scripts.fetch_zeta_zeros` (add an empty `scripts/__init__.py` and `tests/__init__.py` if pytest needs them).

- [ ] **Step 3: Write the implementation**

```python
#!/usr/bin/env python3
"""Fetch the first 100k zeta-zero imaginary parts from Odlyzko's published
tables, verify, and emit datasets/zeta-zeros-100k.f64 (+ provenance sidecar).

Zero computation deliberately stays OFF this machine: we download published
values and only spot-check the first 100 with mpmath (seconds of work).
"""
import datetime
import hashlib
import json
import struct
import sys
import urllib.request
from pathlib import Path

SOURCE_URL = "https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1"
EXPECTED_COUNT = 100_000
FIRST_ZERO = 14.134725141734693
OUT_DIR = Path(__file__).resolve().parent.parent / "datasets"
SPOT_CHECK_N = 100
SPOT_CHECK_TOL = 1e-8  # source is accurate to ~3e-9; 1e-9 unachievable (documented deviation)
# Second independent source (spec §4.3): first 10 zeros as published in the
# literature / LMFDB, to full double precision.
KNOWN_FIRST_TEN = [
    14.134725141734693, 21.022039638771554, 25.010857580145688,
    30.424876125859513, 32.935061587739189, 37.586178158825671,
    40.918719012147495, 43.327073280914999, 48.005150881167159,
    49.773832477672302,
]


def parse_zeros_text(text: str) -> list[float]:
    return [float(line) for line in text.splitlines() if line.strip()]


def validate_zeros(zeros: list[float], expected_count: int) -> None:
    if len(zeros) != expected_count:
        raise ValueError(f"expected {expected_count} zeros, got {len(zeros)}")
    if abs(zeros[0] - FIRST_ZERO) > 1e-6:
        raise ValueError(f"first zero {zeros[0]} != {FIRST_ZERO}")
    for i in range(1, len(zeros)):
        if zeros[i] <= zeros[i - 1]:
            raise ValueError(f"zeros not strictly increasing at index {i}")


def encode_f64le(zeros: list[float]) -> bytes:
    return struct.pack(f"<{len(zeros)}d", *zeros)


def spot_check_literature(zeros: list[float], tol: float) -> float:
    worst = max(abs(a - b) for a, b in zip(KNOWN_FIRST_TEN, zeros))
    if worst > tol:
        raise ValueError(f"literature spot-check failed: worst diff {worst} > {tol}")
    return worst


def spot_check_mpmath(zeros: list[float], n: int, tol: float) -> float:
    from mpmath import mp, zetazero
    mp.dps = 20
    worst = 0.0
    for k in range(1, n + 1):
        ref = float(zetazero(k).imag)
        worst = max(worst, abs(ref - zeros[k - 1]))
    if worst > tol:
        raise ValueError(f"mpmath spot-check failed: worst diff {worst} > {tol}")
    return worst


def _git_rev() -> str:
    try:
        import subprocess
        return subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"], capture_output=True,
            text=True, cwd=Path(__file__).parent, timeout=10,
        ).stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def main() -> int:
    print(f"downloading {SOURCE_URL} ...")
    text = urllib.request.urlopen(SOURCE_URL, timeout=120).read().decode()
    zeros = parse_zeros_text(text)
    validate_zeros(zeros, EXPECTED_COUNT)
    worst_lit = spot_check_literature(zeros, SPOT_CHECK_TOL)
    print(f"literature spot-check OK (first 10, worst diff {worst_lit:.2e})")
    worst = spot_check_mpmath(zeros, SPOT_CHECK_N, SPOT_CHECK_TOL)
    print(f"mpmath spot-check OK (first {SPOT_CHECK_N}, worst diff {worst:.2e})")

    blob = encode_f64le(zeros)
    sha = hashlib.sha256(blob).hexdigest()
    OUT_DIR.mkdir(exist_ok=True)
    (OUT_DIR / "zeta-zeros-100k.f64").write_bytes(blob)
    provenance = {
        "dataset": "zeta-zeros-100k.f64",
        "content": "imaginary parts of the first 100000 nontrivial zeta zeros",
        "format": "float64 little-endian, strictly increasing",
        "count": EXPECTED_COUNT,
        "sha256": sha,
        "source_url": SOURCE_URL,
        "source_accuracy": "~3e-9 (per Odlyzko's table notes)",
        "retrieved_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "cross_checks": [
            {"method": "published literature/LMFDB values, first 10 zeros",
             "tolerance": SPOT_CHECK_TOL, "worst_diff": worst_lit},
            {"method": f"mpmath zetazero(1..{SPOT_CHECK_N}) at dps=20",
             "tolerance": SPOT_CHECK_TOL, "worst_diff": worst},
        ],
        "tolerance_note": "spec asked 1e-9; source accuracy is ~3e-9, so 1e-8 is the honest achievable bound",
        "generator": f"scripts/fetch_zeta_zeros.py@{_git_rev()}",
    }
    (OUT_DIR / "zeta-zeros-100k.provenance.json").write_text(
        json.dumps(provenance, indent=2))
    print(f"wrote {len(blob)} bytes, sha256={sha}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/test_fetch_zeta_zeros.py -v`
Expected: 7 passed.

- [ ] **Step 5: Commit**

```bash
cd ~/Projects/brockian-mathematics
git add scripts/fetch_zeta_zeros.py tests/test_fetch_zeta_zeros.py scripts/__init__.py tests/__init__.py
git commit --no-verify -m "feat: fetch_zeta_zeros — download+verify Odlyzko 100k zeros to f64le

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

### Task 2: Generate the dataset for real

**Files:**
- Create: `datasets/zeta-zeros-100k.f64` (~800,000 bytes)
- Create: `datasets/zeta-zeros-100k.provenance.json`

- [ ] **Step 1: Ensure mpmath is available**

Run: `python3 -c "import mpmath; print(mpmath.__version__)"`
If missing: `python3 -m pip install --user mpmath` (do NOT install anything heavier).
Also precheck disk (standing gotcha — the Mini runs chronically tight): `df -g / | tail -1` — need ≥ 2 GB free before downloading; if under, STOP and surface to the user.

- [ ] **Step 2: Run the fetch**

Run: `cd ~/Projects/brockian-mathematics && python3 scripts/fetch_zeta_zeros.py`
Expected: `literature spot-check OK`, `mpmath spot-check OK`, `wrote 800000 bytes, sha256=<hex>`. Record the sha256 — it is pinned into the Lovable `manifest.json` in Task 4.
If the Odlyzko URL 404s/moves: try `http://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1`; if both fail, STOP and surface to the user (do not substitute a non-authoritative source silently).

- [ ] **Step 3: Sanity-check the binary**

Run: `python3 -c "
import struct
b = open('datasets/zeta-zeros-100k.f64','rb').read()
assert len(b) == 800000, len(b)
z = struct.unpack('<3d', b[:24])
print(z)"`
Expected: `(14.134725142, 21.022039639, 25.01085758)` — the source publishes ~9 decimals, so the stored doubles round-trip at that precision. Differences from the full-precision references (14.134725141734693, …) of up to ~1e-8 are expected and fine; that is exactly the tolerance the spot-checks enforce.

- [ ] **Step 4: Commit dataset + sidecar**

```bash
git add datasets/zeta-zeros-100k.f64 datasets/zeta-zeros-100k.provenance.json
git commit --no-verify -m "data: first 100k zeta zeros (Odlyzko), f64le + provenance

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

## Chunk 2: Build 1 — Compute (Lovable)

### Task 3: Pre-flight sync with the concurrent editor

- [ ] **Step 1:** `list_edits(project_id, limit: 3)` — note the max-`created_at` entry (what the adjacent AI last did).
- [ ] **Step 2:** `list_files(project_id)` (or `read_file` on likely paths) to pin down the exact paths of the three shared files: `src/site-registry.ts`, the nav component, the router file (likely `src/App.tsx`). Record the actual paths — all later tasks use them.
- [ ] **Step 3:** `read_file` each of the three; save their current relevant content (registry entry shape, nav item shape, route registration shape) into your working notes so build messages can quote the exact existing patterns.
- [ ] **Step 4:** `read_file` on `src/lib/verified-registry.ts` and the existing `ProofDrawer` component — record their exported interfaces for Task 12.

### Task 4: Upload the dataset into the Lovable repo

**Files (Lovable):**
- Create: `public/datasets/zeta-zeros-100k.f64`, `public/datasets/zeta-zeros-100k.provenance.json`, `public/datasets/manifest.json`

- [ ] **Step 1: Write the manifest locally** (scratchpad), pinning the sha256 from Task 2:

```json
{
  "zeta-zeros-100k": {
    "url": "/datasets/zeta-zeros-100k.f64",
    "count": 100000,
    "format": "f64le",
    "sha256": "<SHA256_FROM_TASK_2>",
    "provenance": "/datasets/zeta-zeros-100k.provenance.json"
  }
}
```

- [ ] **Step 2: Upload all three files:** for each, `get_file_upload_url` → HTTP `PUT` the bytes (use `curl -T <file> "<upload_url>"` from Bash for the binary) → collect the file references.
- [ ] **Step 3: Send the placement message** (`send_message`, `files: [the three refs]`):

> Place the three attached files VERBATIM (no transformation, no re-encoding — the .f64 file is a binary dataset) at: `public/datasets/zeta-zeros-100k.f64`, `public/datasets/zeta-zeros-100k.provenance.json`, `public/datasets/manifest.json`. Do not modify any other file. Confirm the byte size of the .f64 file after placement (must be exactly 800000).

- [ ] **Step 4: Verify integrity from the outside:** wait for preview rebuild, then locally:

Run: `curl -s https://<preview-domain>/datasets/zeta-zeros-100k.f64 | shasum -a 256`
Expected: exactly the pinned sha256. Also `curl -s .../datasets/manifest.json` and check the JSON round-trips.
**Fallback if the hash mismatches or the file is corrupted:** upload the binary to the project's Supabase Storage instead (public bucket `datasets`) via a `send_message` asking the agent to create the bucket and you `PUT` to its public upload URL — then edit `manifest.json`'s `url` to the Storage public URL AND delete the corrupted in-repo `public/datasets/zeta-zeros-100k.f64` (no bad copy may remain — Task 5's node-fs test resolves the local path via the manifest and must not validate against corrupt bytes). Re-verify with the same checksum command against the Storage URL.

### Task 5: Kernel modules + golden tests

**Files (Lovable):** Create: `src/kernel/zeta.ts`, `src/kernel/explicit.ts`, `src/kernel/sieve.ts`, `src/kernel/spectra.ts`, `src/kernel/worker.ts`, `src/kernel/client.ts`, `src/kernel/types.ts`, `src/kernel/__tests__/kernel.golden.test.ts`

- [ ] **Step 1: Extract the five-point-spectrum ground truth from the registry.** Locally: `python3 - <<'EOF'` over `registry/theorems.json` — find the constellation-sieve five-point structure theorem (spectrum {2−√2, 1, 2, 3, 2+√2}); record its exact theorem name, the graph/operator definition, and register. If the graph definition isn't recoverable from the registry entry, read the Lean source it points to. STOP and ask the user if the definition can't be found — do not guess the graph.
- [ ] **Step 2: Send the kernel message** (one message; no shared files touched). Message content:

> Create a browser compute kernel under `src/kernel/` — pure TypeScript, no DOM access in the math modules, everything below is NEW files only. Do not modify any existing file.
>
> `types.ts`: `type Register = 'COMPUTATION'`; `interface KernelProvenance { method: string; params: Record<string, unknown>; precision: string; elapsedMs: number; register: Register }`; `interface KernelResult<T> { data: T; provenance: KernelProvenance }`; task name union `KernelTask = 'zeros.scan' | 'zeta.Z' | 'zeta.gridAbs' | 'explicit.psi' | 'sieve.primes' | 'spectra.fivePoint' | 'spectra.gueSample' | 'explicit.frames'`.
>
> `zeta.ts`: Riemann–Siegel Z(t) with two branches. (a) For 10 ≤ t ≤ 200 compute ζ(1/2+it) by Euler–Maclaurin with ADAPTIVE truncation N = max(60, ⌈2t⌉) terms and Bernoulli corrections through B8 (N must grow with t — a fixed N=60 collapses to ~1e-4 error near t=200; N = 2t drives the first omitted term to ~1e-11, making the ≲1e-9 precision claim comfortably true) and return Z(t) = Re(e^{iθ(t)}·ζ(1/2+it)) — this branch is the high-accuracy one used for the first zeros. Also `gridAbs(reMin, reMax, imMin, imMax, nx, ny)` — coarse |ζ(s)| magnitude grid for Surface Ch. 1 (task 'zeta.gridAbs'): for Re(s) ≥ 1/2 use the Euler–Maclaurin core directly; for Re(s) < 1/2 compute via the functional equation ζ(s) = χ(s)ζ(1−s) with χ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s) (use a Lanczos Γ implementation) so ~1e-6 accuracy holds everywhere off the pole; GUARD the s=1 pole — skip/offset any grid point within 1e-6 of s=1 and clamp |ζ| to a max terrain height so the pole renders as a finite spike, never NaN/Infinity. (b) For t > 200 use the Riemann–Siegel main sum Z(t) = 2·Σ_{n≤⌊√(t/2π)⌋} cos(θ(t) − t·ln n)/√n + remainder with Gabcke correction terms C0–C3. θ(t) via the asymptotic series θ(t) = t/2·ln(t/2π) − t/2 − π/8 + 1/(48t) + 7/(5760t³) + 31/(80640t⁵) (document: valid t ≥ 10; zero-finding domain is t ∈ [10, 10⁷]). `findZeros(tMin, tMax, opts)`: sign-change scan on Z with adaptive step (≤ half the local average zero spacing 2π/ln(t/2π)), then bisection to |Δt| < 1e-10; supports progress callback + early abort; returns partial results on abort/timeout.
>
> `sieve.ts`: wheel or plain Eratosthenes sieve up to 10⁷: `primesUpTo(n)`, `piTable(n)`, `psi(x)` (Chebyshev ψ via sum of ln p over prime powers ≤ x, x ≤ 10⁶).
>
> `explicit.ts`: explicit-formula partial sum using zeros γ_k supplied as Float64Array: `psiApprox(x, gammas, N) = x − Σ_{k<N} 2√x·(0.5·cos(γ_k ln x) + γ_k·sin(γ_k ln x))/(0.25 + γ_k²) − ln(2π) − 0.5·ln(1 − x⁻²)`. Also `psiFrames(xGrid, gammas, Nsteps)` returning frames for the Surface Ch.3 animation.
>
> `spectra.ts`: [INSERT the exact graph/operator definition + closed forms extracted in Step 1, with the registry theorem name in a comment]. `fivePointSpectrum()` returns both the exact closed forms and a numerically-diagonalized check (plain Jacobi eigenvalue iteration is fine at this size). `gueWignerPdf(s) = (32/π²)·s²·e^{−4s²/π}` and `sampleGueSpacings(n, rng)` (accept a seedable RNG parameter; never Math.random directly in the math path).
>
> `worker.ts` + `client.ts`: Worker protocol `kernel.run(task, params, { onProgress, signal }): Promise<KernelResult>` — message-id correlated request/response, AbortSignal cancels (worker checks a cancellation flag between batches), 10s default timeout returning partial results where supported (`zeros.scan`, `explicit.frames`) and a `KernelTimeoutError` otherwise. On worker hard-crash (error event): reject ALL pending promises with `KernelCrashError`, respawn the worker once, surface the error to callers thereafter. Every result carries provenance with register 'COMPUTATION' and honest `precision` strings (e.g. "|Z| abs err ≲ 1e-9 (EM branch, t≤200); ≲ 1e-6 (RS branch)").
>
> Vitest golden tests in `src/kernel/__tests__/kernel.golden.test.ts` (test the math modules directly, not through the worker): (1) first 10 zeros found in [10, 51] match [14.134725141734693, 21.022039638771554, 25.010857580145688, 30.424876125859513, 32.935061587739189, 37.586178158825671, 40.918719012147495, 43.327073280914999, 48.005150881167159, 49.773832477672302] to 1e-8; (2) `piTable` gives π(10⁴)=1229, π(10⁵)=9592, π(10⁶)=78498; (3) `psi(10)` equals the definitional sum over prime powers {2,3,4,5,7,8,9} → 3ln2+2ln3+ln5+ln7, to 1e-12; plus a labeled SANITY (not golden) bound |psi(10⁶) − 10⁶| < 2000 (PNT-scale check catching prime-power enumeration bugs at scale); (4) `psiApprox(1000, zeros, N)` error vs `psi(1000)` shrinks by at least 2× at each step N = 10 → 100 → 1000 — load the zeros in the test from the local dataset file via node `fs`, resolving the path from `public/datasets/manifest.json`; if the local .f64 is absent (Storage fallback in effect, Task 4), skip this test with a loud console warning naming the reason; (5) `fivePointSpectrum()` numeric eigenvalues match the closed forms to 1e-12; (6) mean of 10⁵ Wigner-surmise samples ∈ [0.98, 1.02] with a FIXED seed; (7) `gridAbs` goldens: |ζ(2)| = π²/6 to 1e-9 (EM side) and |ζ(−1)| = 1/12 to 1e-9 (functional-equation side). Run `npx vitest run src/kernel` and report the full output in your reply. If the 1e-8 zero tolerance fails, report the achieved accuracy honestly — do not loosen the test without saying so.

- [ ] **Step 3: Poll to completion; read the reported Vitest output.** Expected: all tests pass. If the agent reports failures, iterate with focused follow-up messages until green (surface to user after 3 failed iterations).
- [ ] **Step 4:** `read_file` on `src/kernel/client.ts` and `zeta.ts` — verify the protocol shape matches the spec (§4.2) and precision strings are honest.

### Task 6: DepthShell + `/observatory` route + Zero Explorer

**Files (Lovable):** Create: `src/components/depth/DepthShell.tsx`, `src/observatory/ObservatoryPage.tsx`, `src/observatory/explore/ZeroExplorer.tsx`, `src/observatory/explore/ProvenanceStrip.tsx`, `src/observatory/explore/PanelErrorBoundary.tsx`. Modify (shared — re-read first per protocol): `src/site-registry.ts`, router file, nav component.

- [ ] **Step 1:** Re-run the Task 3 pre-flight (list_edits + read_file the three shared files) — the adjacent AI may have moved them since.
- [ ] **Step 2: Send the message:**

> Create the Zeta Observatory flagship route. NEW files: (1) `src/components/depth/DepthShell.tsx` — props `{ surface, explore, rigor: ReactNode; defaultDepth?: 'surface'|'explore'|'rigor'; labSlug: string }`; renders a persistent top-right 3-way depth switcher; active depth from `?depth=` URL param > localStorage key `depth:<labSlug>` > defaultDepth; writes both on change; lazy-mounts ONLY the active layer (each layer arrives as a React.lazy chunk); no math/content knowledge whatsoever. (2) `src/observatory/ObservatoryPage.tsx` — mounts DepthShell with labSlug "observatory", defaultDepth 'explore' (Build 2 will flip to 'surface'); Surface and Rigor layers render an honest "under construction — arriving in the next build" placeholder (first-class empty state, no fake content). (3) `src/observatory/explore/ZeroExplorer.tsx` — panel using the kernel client (`zeros.scan`): user picks a t-window (default [10, 100], guard t ∈ [10, 10⁷] with the guard explained in-UI — a deliberate tightening of spec §3.2's (0, 10⁷]: the θ asymptotic series needs t ≥ 10 and the first zero sits at 14.13, so nothing is lost; UI copy states the domain as [10, 10⁷]), live-plots Z(t), marks found zeros, click-to-zoom, running list of zeros with residual |Z(t₀)|; progress bar during scan; cancel button (AbortSignal); on timeout show "computation budget reached — narrow the range" with partial results. (4) `ProvenanceStrip.tsx` — renders a KernelResult's provenance: method, params, precision, elapsedMs, and a COMPUTATION register badge visually distinct from the site's PROVED styling. (5) `PanelErrorBoundary.tsx` — per-panel boundary with retry; a panel crash must never take down the page. SHARED-FILE EDITS (minimal, exactly these): add an `/observatory` entry to `src/site-registry.ts` following the existing flagship-tier entry shape; add the route to [router file]; do NOT add the nav link yet (that's Build 3). Current content of those files is: [PASTE the read_file contents from Step 1]. Make no other modification to them.

- [ ] **Step 3:** Poll; then in-sandbox check: ask the agent (follow-up message) to load `/observatory?depth=explore`, run a zero scan over [10, 60], and report console errors (must be 0) + the zeros found (must start 14.1347…, 21.0220…, 25.0108…).
- [ ] **Step 4:** `get_diff` — confirm the shared-file diffs are exactly the two minimal registrations.

### Task 7: Remaining Explore panels

**Files (Lovable):** Create: `src/observatory/explore/ExplicitFormulaLab.tsx`, `src/observatory/explore/SpacingStatistics.tsx`, `src/observatory/explore/OperatorBridge.tsx`, `src/observatory/lib/useZerosDataset.ts`

- [ ] **Step 1: Send the message:**

> Add three Explore panels + the dataset hook to the Zeta Observatory. NEW files only; wire the panels into `ObservatoryPage.tsx`'s Explore layer next to ZeroExplorer, each wrapped in PanelErrorBoundary. (1) `src/observatory/lib/useZerosDataset.ts` — loads `/datasets/manifest.json`, fetches the pinned `url`, VERIFIES sha256 of the received bytes against the manifest's pinned hash (Web Crypto), parses Float64Array; caches in module scope; on hash mismatch or fetch failure returns `{ status: 'unavailable' }` — callers then fall back to kernel-computed zeros for the first ~10³ with an in-UI notice, or show an honest unavailable state. (2) `ExplicitFormulaLab.tsx` — slider N (zeros used, 1..10⁴ log scale) → kernel `explicit.psi` partial sum plotted against the true ψ(x) staircase (kernel `sieve` live, x ≤ 10⁶, default window [2, 1000]); ProvenanceStrip on both series. (3) `SpacingStatistics.tsx` — gap histogram of the first N dataset zeros normalized with LOCAL unfolding: s_k = (γ_{k+1} − γ_k) · ln(γ_k / 2π) / (2π), i.e. gap × local zero density (do NOT normalize by a global mean spacing — the density varies ~10× across the dataset and a global mean smears the histogram into disagreement with GUE); overlay the Wigner-surmise curve (`gueWignerPdf`) and a live sampled overlay; copy MUST frame this as empirical agreement, register COMPUTATION — no claim that RH or GUE-universality is proven. (4) `OperatorBridge.tsx` — five-point spectrum {2−√2, 1, 2, 3, 2+√2} from kernel `spectra.fivePoint`: show the graph, the exact closed forms, and the numeric check side-by-side; label the finite structure theorem as PROVED (name: [THEOREM NAME from Task 5 Step 1]) and the connection to zeta spectra as CONJECTURE/program framing, in visibly different styling. Every panel output carries a ProvenanceStrip. Run `npx vitest run` and report output.

- [ ] **Step 2:** Poll; verify reported tests green; `read_file` on `useZerosDataset.ts` (hash verification present — honesty invariant).

### Task 8: Build 1 verification + EYES-ON + publish

- [ ] **Step 1:** Follow-up message: run the FULL Vitest suite (`npx vitest run` — including the existing registry-consistency gate, which must stay green after the `site-registry.ts` edit) and report output; then crawl `/observatory?depth=explore`, exercise all four panels, report console errors (0 required) and a screenshot of each panel.
- [ ] **Step 2:** Local outside check: `curl -s -o /dev/null -w "%{http_code}" https://<preview>/observatory` → 200; dataset sha256 check still passes.
- [ ] **Step 3: EYES-ON GATE** — present preview URL + screenshots to the user; wait for explicit approval.
- [ ] **Step 4: PUBLISH GATE** — on approval, `deploy_project`; verify prod `/observatory` renders (repeat Step 2 against torus.riemannlab.com).
- [ ] **Step 5:** Local commit of any notes/state in this repo if created; update nothing else.

---

## Chunk 3: Build 2 — Cinema (Lovable)

### Task 9: Surface chapters 1–2

**Files (Lovable):** Create: `src/observatory/surface/SurfaceJourney.tsx`, `src/observatory/surface/ChapterLandscape.tsx`, `src/observatory/surface/ChapterSpectrum.tsx`, `src/observatory/surface/chapterScaffold.tsx` (shared chapter chrome: narration text block, next/prev, scroll advance, reduced-motion/still fallback plumbing)

- [ ] **Step 1: Send the message:**

> Build the first half of the Zeta Observatory Surface layer (react-three-fiber; add `three`/`@react-three/fiber`/`@react-three/drei` if not present). NEW files only. `SurfaceJourney.tsx` — chapter container: chapters advance by scroll snap or explicit next/prev buttons; each chapter = full-viewport R3F scene + short narration text (2–4 sentences, museum-caption register, honest: no claim beyond what's on the Rigor ledger); mounts into ObservatoryPage's Surface slot replacing the placeholder. `chapterScaffold.tsx` — shared chrome + fallback logic: if `prefers-reduced-motion` or WebGL unavailable, render a static still (a pre-styled SVG/canvas snapshot per chapter, NOT a live scene) + full narration; on WebGL context loss, swap to the still; additionally honor a `?forceStills=1` query flag that forces the still branch (verification hook — lets us exercise the no-WebGL path on demand). DPR capped at 2; particle/geometry counts scale down on mobile. Ch. 1 `ChapterLandscape.tsx` — flyover of the |ζ(s)| landscape over the complex plane: compute a ~100×100 |ζ| magnitude mesh ONCE, lazily, in the kernel worker via the `zeta.gridAbs` task (never on the main thread), cache it in module scope, and build the terrain from it; critical strip highlighted, pole at s=1 and trivial zeros visible as terrain. Ch. 2 `ChapterSpectrum.tsx` — the critical line rotates to vertical and the first ~100 zeros from `useZerosDataset` render as emission-spectrum lines (fallback: kernel zeros if dataset unavailable). Target 60fps desktop / 30fps mobile. No console errors.

- [ ] **Step 2:** Poll; ask for in-sandbox screenshots of both chapters + console check (0 errors) including with `prefers-reduced-motion` emulated.

### Task 10: Surface chapters 3–4 + depth default flip

**Files (Lovable):** Create: `src/observatory/surface/ChapterMusic.tsx`, `src/observatory/surface/ChapterOperatorDream.tsx`. Modify: `src/observatory/ObservatoryPage.tsx` (defaultDepth → 'surface')

- [ ] **Step 1: Send the message:**

> Complete the Surface layer. Ch. 3 `ChapterMusic.tsx` — "The Music of the Primes": animated explicit-formula reconstruction; on chapter mount, request `explicit.frames` from the kernel worker (zeros from useZerosDataset; grid x ∈ [2, 500]; ~60 frames as N steps up); animate the ψ(x) partial sum converging onto the true staircase, one zero-term chorus at a time; caption links the idea to the interactive ExplicitFormulaLab in Explore. Ch. 4 `ChapterOperatorDream.tsx` — the Hilbert–Pólya idea and the Brockian operator program, honestly framed: a visual of the five-point spectrum (reuse spectra closed forms), narration that states plainly which pieces are PROVED — the five-point structure theorem ([THEOREM NAME from Task 5 Step 1]) and the ξ-bridge/spectral-scaffold theorems: read `/public/verified-registry.json` and copy each theorem name VERBATIM from it (never invent or paraphrase a theorem name; if you cannot find an entry, omit the claim rather than guess) — and that RH itself and the operator realization are OPEN, with `RH_of_BrockianSystem` CONDITIONAL; small register badges inline in the narration; a "see the proofs" affordance that switches depth to Rigor. Also: flip `defaultDepth` to 'surface' in ObservatoryPage.tsx (first-time visitors now land on the cinema; returning visitors keep their localStorage choice). Both chapters get the chapterScaffold fallbacks. Report console output and screenshots of all four chapters.

- [ ] **Step 2:** Poll; verify screenshots + 0 console errors across: normal render, reduced-motion emulated, and `?forceStills=1` (which must show the still-image branch for every chapter — this is how the no-WebGL path gets exercised before publish).

### Task 11: Performance budget + EYES-ON + publish

- [ ] **Step 1:** Follow-up message: report the production build chunk sizes (`npx vite build` output): the initial `/observatory` route chunk must be < 500 KB gz with kernel, three.js, and datasets all in lazy chunks. If over budget, move imports until it passes and report the new numbers.
- [ ] **Step 2:** Confirm interactivity + frame health: agent runs a kernel scan in Explore then switches to Surface — UI stays responsive; agent reports rAF frame-time stats (avg/max ms) per chapter and flags visible jank (soft check against the 60/30 fps target — the eyes-on gate is the authoritative judgment, but this catches gross misses early).
- [ ] **Step 3:** Full sandbox crawl per the operating protocol: `/observatory` at all three depths (Surface is now default) — 0 console errors each; full `npx vitest run` still green.
- [ ] **Step 4: EYES-ON GATE** — user reviews the cinema (all four chapters) on preview; explicit approval.
- [ ] **Step 5: PUBLISH GATE** — `deploy_project`; spot-check prod.

---

## Chunk 4: Build 3 — Rigor + fleet pipeline

### Task 12: Claim Ledger + ProofChips + RH banner

**Files (Lovable):** Create: `src/observatory/claims.ts`, `src/observatory/rigor/RigorPanel.tsx`, `src/observatory/rigor/ClaimLedger.tsx`, `src/observatory/rigor/ProofChip.tsx`, `src/observatory/rigor/RhStatusBanner.tsx`, `src/observatory/__tests__/claims.integrity.test.ts`

- [ ] **Step 1:** Enumerate the claims: locally list every mathematical claim made in Surface narration + Explore copy (read them via `read_file` — Ch.1–4 narration, panel copy). Draft the `claims.ts` rows: `{ id, text, register: 'PROVED'|'COMPUTATION'|'CONDITIONAL'|'CONJECTURE'|'OPEN', theoremName? }` — PROVED rows must carry the exact registry theorem name (verify each against `/verified-registry.json` content via `read_file` or the live site fetch). Include at minimum: the five-point structure theorem (PROVED), zero computations & GUE agreement (COMPUTATION), `RH_of_BrockianSystem` (CONDITIONAL, with its exact hypothesis in the text), RH + Hilbert–Pólya realization + zeta–Brockian bridge (OPEN/CONJECTURE).
- [ ] **Step 2: Send the message** (include the full drafted claims array):

> Build the Rigor layer. NEW files only; mount RigorPanel into ObservatoryPage's Rigor slot replacing the placeholder. `src/observatory/claims.ts` — this exact typed array: [PASTE claims array]. `ClaimLedger.tsx` — enumerated table of all claims with register badges (reuse the site's existing register badge styling); PROVED rows render a `ProofChip`. `ProofChip.tsx` — small chip (theorem name + register) that on click opens the EXISTING ProofDrawer ([interface recorded in Task 3 Step 4]) resolved via `src/lib/verified-registry.ts`; if the registry fetch fails, render as a plain badge with a "registry unreachable" tooltip — the ledger itself still renders from claims.ts. `RhStatusBanner.tsx` — prominent banner: RH is OPEN, this site claims no progress on it; `RH_of_BrockianSystem` is CONDITIONAL on [exact hypothesis]. `RhStatusBanner`'s `RH_of_BrockianSystem` hypothesis text: copy VERBATIM from its entry in `public/verified-registry.json` — never paraphrase a hypothesis. Also update Surface/Explore copy ONLY where needed so every on-screen mathematical claim references a claims.ts id (no claim without a ledger row — spec §5.2); references go through a tiny `<ClaimRef id="…"/>` component (renders a small superscript marker linking to the ledger row), so references are statically detectable. Vitest `claims.integrity.test.ts`: (a) every PROVED claim's theoremName resolves to a real entry in `public/verified-registry.json` (load via node fs); (b) scan `src/observatory/**/*.tsx` via node fs with the regex `/<ClaimRef\s+id="([^"]+)"/g` and assert every referenced id exists in claims.ts. Links-out section in RigorPanel: /ledger, /targets, /explore/lean-registry, the GitHub repo. Run `npx vitest run` and report output.

- [ ] **Step 3:** Poll; tests green; `read_file` claims.ts — verify no PROVED row lacks a theoremName and the registers match Step 1's draft.

### Task 13: Supabase table via `query_database`

- [ ] **Step 1:** Run the migration with `mcp__claude_ai_Lovable__query_database` (project `dd8308ac-…`):

```sql
create table if not exists public.solver_fleet_snapshot (
  id integer primary key,
  generated_at timestamptz not null,
  running jsonb not null default '[]'::jsonb,
  recent_verdicts jsonb not null default '[]'::jsonb,
  domain_counts jsonb not null default '{}'::jsonb,
  updated_at timestamptz not null default now()
);
alter table public.solver_fleet_snapshot enable row level security;
drop policy if exists "public read fleet snapshot" on public.solver_fleet_snapshot;
create policy "public read fleet snapshot" on public.solver_fleet_snapshot
  for select to anon, authenticated using (true);
-- Supabase default privileges grant ALL (incl. TRUNCATE/REFERENCES/TRIGGER) on new
-- public tables to anon/authenticated. Revoke everything FIRST, then grant back
-- SELECT only — this order matters (a later revoke-all would wipe the grant).
revoke all on public.solver_fleet_snapshot from anon, authenticated;
grant select on public.solver_fleet_snapshot to anon, authenticated;
```

- [ ] **Step 2:** Verify: `query_database` → `select * from public.solver_fleet_snapshot;` returns 0 rows, no error; then `select grantee, privilege_type from information_schema.role_table_grants where table_name='solver_fleet_snapshot' and grantee in ('anon','authenticated');` — SELECT only for both (the explicit revoke above is what makes this expectation hold on Supabase).

### Task 14: `push_fleet_snapshot.py` (local, TDD)

**Files:**
- Create: `aristotle/push_fleet_snapshot.py`
- Test: `tests/test_push_fleet_snapshot.py`
- Modify: `aristotle/solver_watch.py` (end-of-cycle hook — the wrapper `exec`s the watcher, so the push must be called from inside it)

- [ ] **Step 1: Write the failing tests**

**Data-contract note (verified against the real files):** `solver_manifest.json`'s top level is `{"generated", "count", "solvers": [...]}` — the record list key is **`solvers`**, not `jobs` — and each record carries exactly `{id, account, name, status, verdict, created}` — there is NO `domain` field and NO `finished_at` field, and `created` is a fuzzy string ("2 days ago"), not sortable. So: (a) `domain` is DERIVED deterministically from the job-name prefix by `classify_domain()` below (transparent derivation, documented in code and labeled as derived in the panel — never presented as recorded metadata); (b) `finished_at` is stamped by `solver_watch.py` at the RUNNING→IDLE transition from Task 15 onward (records finished before that wiring simply lack it and sort last); (c) verdict values include `BASELINE` (finished before the watch existed) — `recent_verdicts` must include ONLY `PROVED`/`STOPPED`. Before writing the tests, still open the real `aristotle/solver_manifest.json` once to confirm the top-level shape matches the fixture; mirror reality, never invent fields.

```python
# tests/test_push_fleet_snapshot.py
import json
from aristotle.push_fleet_snapshot import build_snapshot, classify_domain

MANIFEST = {
    "solvers": [
        {"id": "j1", "name": "Algebra012", "status": "RUNNING",
         "account": "admin", "created": "2 days ago"},
        {"id": "j2", "name": "NTGaps2", "status": "IDLE", "account": "chris",
         "created": "2 days ago", "verdict": "PROVED",
         "finished_at": "2026-08-08T10:00:00Z"},
        {"id": "j3", "name": "Crypto2", "status": "IDLE", "account": "admin",
         "created": "3 days ago", "verdict": "STOPPED",
         "finished_at": "2026-08-07T09:00:00Z"},
        {"id": "j4", "name": "ms-cayley", "status": "IDLE", "account": "admin",
         "created": "9 days ago", "verdict": "BASELINE"},
    ]
}

def test_build_snapshot_shape():
    snap = build_snapshot(MANIFEST, now_iso="2026-08-08T12:00:00Z")
    assert snap["id"] == 1
    assert snap["generated_at"] == "2026-08-08T12:00:00Z"
    assert [j["name"] for j in snap["running"]] == ["Algebra012"]
    # newest first; BASELINE excluded
    assert [v["name"] for v in snap["recent_verdicts"]] == ["NTGaps2", "Crypto2"]
    assert snap["domain_counts"]["Algebra"] == 1

def test_baseline_verdicts_excluded():
    snap = build_snapshot(MANIFEST, now_iso="2026-08-08T12:00:00Z")
    assert all(v["verdict"] in ("PROVED", "STOPPED")
               for v in snap["recent_verdicts"])

def test_classify_domain():
    assert classify_domain("ms-cayley") == "Named theorems"
    assert classify_domain("NumberTheory03") == "Number theory"
    assert classify_domain("TotallyUnknownJob") == "Other"

def test_recent_verdicts_capped_at_20():
    jobs = [{"id": f"j{i}", "name": f"n{i}", "status": "IDLE", "account": "a",
             "created": "1 day ago", "verdict": "PROVED",
             "finished_at": f"2026-08-0{1 + i % 7}T00:00:0{i % 10}Z"}
            for i in range(30)]
    snap = build_snapshot({"solvers": jobs}, now_iso="2026-08-08T12:00:00Z")
    assert len(snap["recent_verdicts"]) == 20

def test_snapshot_size_under_50kb_at_fleet_scale():
    # real fleet is ~191 solvers; exercise the budget at 250
    jobs = [{"id": f"j{i}", "name": f"NumberTheory{i:03d}", "status": "IDLE",
             "account": "admin", "created": "1 day ago",
             "verdict": "PROVED" if i % 3 == 0 else "BASELINE",
             "finished_at": "2026-08-08T00:00:00Z"} for i in range(250)]
    snap = build_snapshot({"solvers": jobs}, now_iso="2026-08-08T12:00:00Z")
    assert len(json.dumps(snap)) < 50_000

def test_build_snapshot_empty_manifest():
    snap = build_snapshot({"solvers": []}, now_iso="2026-08-08T12:00:00Z")
    assert snap["running"] == [] and snap["recent_verdicts"] == []
```

- [ ] **Step 2: Run to verify failure** — `python3 -m pytest tests/test_push_fleet_snapshot.py -v` → import error.
- [ ] **Step 3: Implement**

```python
#!/usr/bin/env python3
"""Condense solver_manifest.json into a single Supabase row for the
Riemann Lab Solver Fleet panel. Called from solver_watch.py at end of
cycle; failure is logged and NEVER fatal to the watcher."""
import datetime
import json
import os
import sys
import urllib.request
from pathlib import Path

MANIFEST_PATH = Path(__file__).resolve().parent / "solver_manifest.json"
MAX_VERDICTS = 20

# Domain is DERIVED from the job-name prefix (the manifest has no domain field).
# Transparent, deterministic, documented; the panel labels it "by area (derived
# from job names)". First match wins; unknown names land in "Other".
DOMAIN_PREFIXES = [
    ("ms-", "Named theorems"), ("qc-", "QC batches"),
    ("Algebra", "Algebra"), ("Analysis", "Analysis"), ("Topology", "Topology"),
    ("SetTheory", "Set theory"), ("Probability", "Probability"),
    ("Combinatorics", "Combinatorics"), ("Geometry", "Geometry"),
    ("NumberTheory", "Number theory"), ("NT", "Number theory"),
    ("CSLogic", "CS & logic"), ("QuantumInfo", "Quantum info"),
    ("PhysicsQM", "Physics"), ("Crypto", "Crypto"), ("InfoTheory", "Info theory"),
    ("Sieve", "Brockian frontier"), ("Spectral", "Brockian frontier"),
    ("Gilbreath", "Brockian frontier"), ("PathSpectrum", "Brockian frontier"),
    ("PentagonSpectrum", "Brockian frontier"), ("KadisonSinger", "Brockian frontier"),
    ("Sensitivity", "Brockian frontier"),
]


def classify_domain(name: str) -> str:
    for prefix, domain in DOMAIN_PREFIXES:
        if name.startswith(prefix):
            return domain
    return "Other"


def build_snapshot(manifest: dict, now_iso: str) -> dict:
    jobs = manifest.get("solvers", [])
    running = [{"name": j["name"], "account": j.get("account", ""),
                "domain": classify_domain(j["name"])}
               for j in jobs if j.get("status") == "RUNNING"]
    # Only real watch-observed outcomes; BASELINE = finished before the watch
    # existed and must not flood the recent list.
    finished = [j for j in jobs if j.get("verdict") in ("PROVED", "STOPPED")]
    # finished_at is stamped by solver_watch at the RUNNING->IDLE transition;
    # older records lack it and sort last ("" < any ISO timestamp, reverse=True).
    finished.sort(key=lambda j: j.get("finished_at", ""), reverse=True)
    verdicts = [{"name": j["name"], "verdict": j["verdict"],
                 "finished_at": j.get("finished_at", ""),
                 "domain": classify_domain(j["name"])}
                for j in finished[:MAX_VERDICTS]]
    counts: dict[str, int] = {}
    for j in jobs:
        d = classify_domain(j["name"])
        counts[d] = counts.get(d, 0) + 1
    return {"id": 1, "generated_at": now_iso, "running": running,
            "recent_verdicts": verdicts, "domain_counts": counts}


def push(snapshot: dict, url: str, service_key: str) -> None:
    req = urllib.request.Request(
        f"{url}/rest/v1/solver_fleet_snapshot",
        data=json.dumps(snapshot).encode(),
        headers={"apikey": service_key,
                 "Authorization": f"Bearer {service_key}",
                 "Content-Type": "application/json",
                 "Prefer": "resolution=merge-duplicates"},
        method="POST")
    urllib.request.urlopen(req, timeout=30).read()


def main() -> int:
    url = os.environ.get("RIEMANN_SUPABASE_URL", "").rstrip("/")
    key = os.environ.get("RIEMANN_SUPABASE_SERVICE_KEY", "")
    if not url or not key:
        print("push_fleet_snapshot: RIEMANN_SUPABASE_* not set; skipping", file=sys.stderr)
        return 0  # non-fatal by contract
    manifest = json.loads(MANIFEST_PATH.read_text())
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    snapshot = build_snapshot(manifest, now)
    snapshot["updated_at"] = now  # merge-duplicates won't touch column defaults
    push(snapshot, url, key)
    print(f"push_fleet_snapshot: pushed at {now}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:  # never crash the caller
        print(f"push_fleet_snapshot: FAILED (non-fatal): {e}", file=sys.stderr)
        sys.exit(0)
```

- [ ] **Step 4: Run tests** — `python3 -m pytest tests/test_push_fleet_snapshot.py -v` → 6 passed.
- [ ] **Step 5: Commit** — `git add aristotle/push_fleet_snapshot.py tests/test_push_fleet_snapshot.py` + commit (`--no-verify`, standard trailer).

### Task 15: Wire the push into the watcher + live verification

- [ ] **Step 1:** Read `aristotle/solver_watch.py` and make TWO changes. (a) Add `finished_at` stamping — **three touch points are required, because the loop rebuilds each entry from scratch every cycle and projects a fixed key tuple into the manifest** (a single stamp would self-erase after one cycle): (a1) in the `just_finished and not first_run` branch (where the verdict is determined), set `entry["finished_at"]` = ISO-8601 UTC now — it persists into `solver_state.json` via `state[pid] = entry`; (a2) in the per-cycle `entry = {...}` rebuild, carry it over from prior state exactly like `verdict`: `"finished_at": prev.get("finished_at")`; (a3) include it in the manifest projection (add `"finished_at"` to the projected key tuple, tolerating None/absent). Records finished before this change simply lack the field and sort last. (b) At the single end-of-cycle point after `solver_manifest.json` is written, add a guarded call:

```python
def _push_fleet_snapshot() -> None:
    try:
        script = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "push_fleet_snapshot.py")
        subprocess.run([sys.executable, script], timeout=60, check=False)
    except Exception as e:
        log(f"fleet snapshot push failed (non-fatal): {e}")
```

(`solver_watch.py` already imports `os`, `subprocess`, and `sys` — do NOT add a pathlib import; adapt `log` to the module's actual logging helper; call `_push_fleet_snapshot()` at the single point where the cycle completes.) The subprocess-with-`check=False` + broad except guarantees the watcher never dies from the push.

- [ ] **Step 2:** Verify vault vars exist WITHOUT printing values: `grep -c "RIEMANN_SUPABASE" ~/.openclaw/vault-bridges.env` → ≥ 2. If the values are placeholders/empty, STOP: ask the user to fill them from the Supabase dashboard (Claude is barred from credential values).
- [ ] **Step 3:** Live push test: `set -a; source ~/.openclaw/vault-bridges.env; set +a; python3 aristotle/push_fleet_snapshot.py` → `pushed at <ts>`. Then verify via anon read (`query_database`): `select generated_at, jsonb_array_length(running) as running, jsonb_array_length(recent_verdicts) as verdicts, domain_counts != '{}'::jsonb as has_domains from solver_fleet_snapshot;` → 1 row, fresh timestamp, and `has_domains` MUST be true (the fleet has ~190 solvers, so empty domain_counts means the snapshot builder read nothing — the empty-payload regression signal; `running`/`verdicts` may legitimately be 0).
- [ ] **Step 4:** Restart the watcher so the wiring goes live: `launchctl kickstart -k gui/$UID/ai.brockian.solver-watch`; after ≤10 min, re-run the Step 3 select → `generated_at` advanced.
- [ ] **Step 5: Commit** — `git add aristotle/solver_watch.py` + commit.

### Task 16: `useSolverFleet` + Fleet panel (Lovable)

**Files (Lovable):** Create: `src/observatory/rigor/useSolverFleet.ts`, `src/observatory/rigor/SolverFleetPanel.tsx`

- [ ] **Step 1: Send the message:**

> Add the live Solver Fleet panel to the Rigor layer. NEW files only. `useSolverFleet.ts` — fetches the single row from the `solver_fleet_snapshot` table via the project's existing Supabase client (anon; SELECT only); refetch every 5 minutes while the Rigor layer is mounted (clear the interval on unmount); returns `{ status: 'ok'|'stale'|'unavailable', snapshot? }` where stale = now − generated_at > 30 min. `SolverFleetPanel.tsx` — renders: jobs running now, recent PROVED/STOPPED verdicts (with timestamps where present — older records may lack them; render those without a time, never a fake one), per-domain counts labeled "by area (derived from job names)" (the domain is a deterministic derivation, not recorded metadata — say so); on 'stale' show the data WITH a prominent staleness banner ("last fleet snapshot: <relative time> — may be out of date"); on 'unavailable' (fetch error or 0 rows) the panel renders NOTHING (unmounts entirely — never synthetic/sample data; spec §5.5). Mount it inside RigorPanel below the Claim Ledger. Report a screenshot of the panel with the live row.

- [ ] **Step 2:** Poll; screenshot shows the real snapshot pushed in Task 15.
- [ ] **Step 3:** Kill-switch test: `query_database` → `delete from solver_fleet_snapshot where id = 1;` → ask the agent to reload Rigor → panel absent, 0 console errors. Then re-run the local push (Task 15 Step 3) to restore the row and confirm the panel returns.

### Task 17: Promotion, final verification, publish, memory

**Files (Lovable):** Modify (shared — re-read first): nav component, home page promotion spot, `src/site-registry.ts` if the nav pulls from it.

- [ ] **Step 1:** Pre-flight sync (list_edits + read_file on nav/home). Send the message:

> Promote the Zeta Observatory: add the nav link (following the existing nav item pattern — current file content: [PASTE]) and a flagship card/link on the home page pointing to `/observatory`. Minimal diffs; no other changes. Then run the full Vitest suite (`npx vitest run`) and report output.

- [ ] **Step 2:** Full three-depth crawl (agent): `/observatory?depth=surface`, `?depth=explore`, `?depth=rigor` — 0 console errors each; all success criteria from spec §1 checked one by one and reported honestly (any miss = fix or surface to user, never overclaim). This sweep IS the spec §10 "polish pass": small visual/copy issues found here get fixed via focused follow-up messages before the eyes-on gate.
- [ ] **Step 3: EYES-ON GATE** — user walks all three depths on preview; explicit approval.
- [ ] **Step 4: PUBLISH GATE** — `deploy_project`; verify prod: route 200, dataset sha256, fleet row fresh, spot-eyeball.
- [ ] **Step 5:** Write/update the memory file `riemann-lab-audit-refactor.md` (or a new `zeta-observatory.md` linked from MEMORY.md): what shipped, commit ids, the claims.ts honesty contract, the fleet pipeline shape, anything deferred. Local commit of plan checkboxes state.
