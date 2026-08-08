# Riemann Lab — Layered Frontier Platform, Crown Jewel 1: The Zeta Observatory

**Date:** 2026-08-08
**Status:** Draft for review
**Target:** Lovable project `dd8308ac-0860-42ae-908c-41b306b58858` (prime-rigor-explorer, prod `torus.riemannlab.com`)
**Program context:** Sub-project 3 (website) of the Brockian serious-math program, building on the Phase 0/1 refactor (site-registry spine, 6-item nav, sanitized `/verified-registry.json` authority, `/ledger`, `/targets`, 173 clean labs).

## 1. Goal

Make Riemann Lab the best platform in existence for frontier mathematics — calculation, visualization, and machine-verified proof — by building it as a **layered-depth platform**: every flagship experience offers three depths in one page:

- **Surface** — museum-grade cinematic visualization for the science-curious public.
- **Explore** — live in-browser computation for students and enthusiasts.
- **Rigor** — full proof provenance for working mathematicians: registers, Lean sources, AXLE certificates, honest open-problem framing, and the live solver fleet.

Strategy: build the platform primitives **inside one crown-jewel experience** (the Zeta Observatory), prove them end-to-end, then replicate the pattern to further jewels in later phases (out of scope here).

**Success criteria (measurable):**
1. `/observatory` live on prod with all three depth layers, 0 console errors, verified by eyes-on render (never headless-only).
2. A visitor computes zeta zeros **live in their browser** (no server), and the first 10 computed zeros match published values to ≤1e-6 on screen. (Golden tests hold the stricter 1e-8 — see §9; the on-screen criterion is deliberately looser to allow display rounding.)
3. Every mathematical claim shown anywhere in the experience appears in the Rigor claim ledger with a register badge; every PROVED claim opens the actual Lean theorem; RH and Hilbert–Pólya are explicitly marked OPEN.
4. The Solver Fleet panel shows real Aristotle/AXLE fleet state no older than 30 minutes (with an honest staleness banner beyond that).
5. Kernel golden-value tests pass in CI (Vitest, in the Lovable sandbox).

## 2. Non-goals / out of scope (this spec)

- Replicating the pattern to other jewels (Constellation Sieve, Goldbach Comb, Operator Spectrum) — Phase 2+.
- Rust/WASM kernel port — kernel v1 is TypeScript + Web Workers (see §4.2 rationale); WASM is an upgrade path only if profiling demands it.
- A "deep compute" job tier (hybrid architecture) — deferred; if ever built, it runs on cloud compute, **not** the Mac Mini (resource-constrained: 16 GB RAM, chronically tight disk). Heavy proof verification already runs off-Mini on Axiom's cloud via AXLE.
- Migrating the 209 allowlisted legacy routes; canonical LabShell sweep; other Phase 2–3 refactor debt.
- Any change to `/verified-registry.json`, the adjacent AI's gate pages (`/labs/riemann-gate1-operator`), or its Audit Reconciliation ledger work.

## 3. The experience: Zeta Observatory (`/observatory`)

A new top-level flagship route (registered in `site-registry.ts`, tier flagship, linked from home + primary nav). The existing `/labs/prime-observatory` is untouched.

The page mounts a `DepthShell` with three layers. Default layer = Surface for first-time visitors, remembered thereafter (`?depth=` URL param overrides, so any state is shareable/linkable).

### 3.1 Surface — the cinematic

Chapter-based R3F (react-three-fiber) journey; chapters advance by scroll or explicit next/prev controls; each chapter has short narration text.

- **Ch. 1 — The Landscape:** flyover of |ζ(s)| over the complex plane; the critical strip emerges; poles/zeros as terrain.
- **Ch. 2 — The Spectrum:** the critical line rotates to vertical; nontrivial zeros render as spectral lines (physical, emission-spectrum styling); the first ~100 zeros from the shipped dataset.
- **Ch. 3 — The Music of the Primes:** animated explicit-formula reconstruction — ψ(x) staircase emerging as zero-terms are added one by one. Frames are computed once on chapter mount in the kernel worker from the shipped zeros dataset (no new precomputed asset; see §4.2 for the load trigger); the *interactive* version lives in Explore.
- **Ch. 4 — The Operator Dream:** Hilbert–Pólya idea + the Brockian operator program, honestly framed: what is PROVED (ξ-bridge, spectral scaffolds — chips link to Rigor), what is OPEN (RH itself, `RH_of_BrockianSystem` conditional).

Fallbacks: `prefers-reduced-motion` and non-WebGL clients get static rendered stills + full narration text; mobile gets the same chapters with simplified scenes (device-pixel-ratio capped, particle counts reduced).

### 3.2 Explore — live computation

Four interactive panels, each wired to the kernel (§4.2), each in its own error boundary:

1. **Zero Explorer** — plot Z(t) (Riemann–Siegel) over a user-chosen window; zeros found live by sign-change scan + bisection; click a zero to zoom; running list of computed zeros with residuals. Range guard: t ∈ (0, 10⁷] (f64 validity, documented in-UI).
2. **Explicit Formula Lab** — slider N (zeros used) → live ψ(x) partial-sum vs the true staircase (sieved live up to x ≤ 10⁶); visibly converges as N grows.
3. **Spacing Statistics** — normalized gap histogram of the first N zeros (dataset) vs GUE Wigner-surmise overlay (sampled live); n.b. framed as *empirical agreement*, register COMPUTATION.
4. **Operator Bridge** — the constellation-sieve five-point spectrum {2−√2, 1, 2, 3, 2+√2} computed live from the actual graph Laplacian (exact closed forms + numeric check), presented as the program's PROVED finite structure theorem, with the connection to zeta spectra explicitly labeled CONJECTURE/program framing.

Every panel's output carries a provenance strip: method, parameters, precision, register **COMPUTATION** — visually distinct from PROVED, always.

### 3.3 Rigor — provenance

- **Claim Ledger:** an enumerated table of every mathematical claim made in Surface + Explore copy, each with a register badge — PROVED / COMPUTATION / CONDITIONAL / CONJECTURE / OPEN. PROVED rows carry a ProofChip opening the ProofDrawer (Lean source + AXLE certificate) resolved from the sanitized registry. This ledger is the honesty contract for the whole experience: **no claim on screen without a ledger row.** Maintained as a typed data file (`src/observatory/claims.ts`); a Vitest test asserts every PROVED row resolves to a real registry theorem.
- **RH status banner:** RH is OPEN; the site claims no progress on it. `RH_of_BrockianSystem` shown as CONDITIONAL with its exact hypothesis.
- **Solver Fleet panel:** live view of the Aristotle/AXLE fleet (§4.4) — jobs running now, recent PROVED/STOPPED verdicts, per-domain counts. Staleness banner if the snapshot is older than 30 min; the panel hides entirely (no fake data) if the feed is unreachable.
- **Links out:** /ledger, /targets, /explore/lean-registry, the GitHub repo.

## 4. Architecture

### 4.1 `DepthShell` (new shared component, `src/components/depth/DepthShell.tsx`)

Props: `{ surface, explore, rigor: ReactNode; defaultDepth?: Depth; labSlug: string }`. Owns the depth switcher UI (persistent, top-right), `?depth=` URL sync, localStorage persistence (`depth:<labSlug>`), and lazy-mounts only the active layer (each layer is a `React.lazy` chunk). No knowledge of math or content — reusable for future jewels as-is.

### 4.2 Compute kernel (`src/kernel/`)

TypeScript + Web Workers. Rationale for TS-not-WASM v1: runs natively in Lovable's Vite build with zero toolchain additions, f64 covers the spec'd ranges, and the worker protocol below is the stable interface — a WASM module can later slot in behind it without touching any panel.

Modules (each independently unit-testable, pure functions, no DOM):
- `zeta.ts` — Riemann–Siegel θ(t) and Z(t) (with the standard remainder term), zero-finding (sign-change scan + bisection). Documented validity: t ≤ 10⁷, |Z| error ≤ ~1e-8 in-range.
- `explicit.ts` — ψ(x) by direct sieve (x ≤ 10⁶) and the explicit-formula partial sum over the first N zeros (zeros supplied from dataset or Zero Explorer output).
- `sieve.ts` — wheel sieve: primes, π(x), gaps, up to 10⁷.
- `spectra.ts` — circulant/path-graph eigenvalues (closed forms, exact where representable), Wigner-surmise/GUE gap sampling.
- `worker.ts` + `client.ts` — the protocol: `kernel.run(task, params, { onProgress, signal }) → Promise<KernelResult>`. `KernelResult = { data, provenance: { method, params, precision, elapsedMs, register: 'COMPUTATION' } }`. Cancellation via AbortSignal; default per-task timeout 10 s, surfaced in-UI as "computation budget reached — narrow the range or raise the budget," returning partial results where the task supports it (zero scan does; eigensolve doesn't).

The kernel is lazy-loaded (dynamic import on first mount of Explore **or** Surface Ch. 3, whichever comes first); nothing kernel-related in the initial route chunk.

### 4.3 Datasets (`public/datasets/`)

- `zeta-zeros-100k.f64` — imaginary parts of the first 100,000 nontrivial zeros as little-endian float64 (~800 KB). **Sourced from published authoritative tables (Odlyzko's zeta tables / LMFDB), not computed locally** — `scripts/fetch_zeta_zeros.py` (brockian-mathematics repo) downloads, converts to f64, and spot-verifies the first 100 zeros against a second independent source plus a seconds-cheap local mpmath check to 1e-9. This keeps compute off the Mac Mini and gives strictly better provenance. A `zeta-zeros-100k.provenance.json` sidecar records source URLs, retrieval date, conversion script version, and cross-check results. Fetched on demand, cached via the browser cache.
- **Transfer into the Lovable repo:** primary channel is the Lovable file-upload API — `get_file_upload_url` → HTTP `PUT` of the binary → `send_message` with `files:[…]` instructing the agent to place both files verbatim at `public/datasets/` (no transformation). Verification: fetch each file from the preview URL and match byte length + SHA-256 against the local originals. Fallback if the upload channel corrupts or can't land binaries: upload to the project's Supabase Storage (public bucket `datasets`) and serve from its public URL instead. The loader resolves dataset URLs from a tiny `public/datasets/manifest.json`, so switching primary → fallback is a one-file edit, not a code change.
- No other precomputed datasets: primes, ψ(x), spectra, and GUE samples are cheap enough to compute live (YAGNI).
- Fallback if the dataset fetch fails at runtime: Explore panels that need zeros fall back to kernel-computed zeros for the first ~10³ (with a notice), or show an honest unavailable state.

### 4.4 Solver Fleet pipeline

- **Provisioning (verified 2026-08-08):** the Lovable project already has Supabase enabled (`get_database_status` → `{enabled: true, stack: "supabase"}`), so no project-level provisioning event and no coordination risk with the adjacent AI. The migration is applied via Lovable `query_database`; the frontend uses the project's existing Lovable-managed Supabase client (URL + anon key already wired).
- **Mac Mini side (this repo, not Lovable):** new `aristotle/push_fleet_snapshot.py`, invoked at the end of each existing `run-solver-watch.sh` cycle (600 s LaunchAgent, already running; the push is I/O-trivial — no meaningful Mini load). It condenses `solver_manifest.json` into a snapshot `{generated_at, running[], recent_verdicts[], domain_counts{}}` (≤50 KB) and upserts a single row into the Supabase table `solver_fleet_snapshot` (id=1). Credentials: `RIEMANN_SUPABASE_URL` + `RIEMANN_SUPABASE_SERVICE_KEY` in `~/.openclaw/vault-bridges.env` (human provisions the values from the Supabase dashboard; never committed; `run-solver-watch.sh` already sources that vault file). Push failure is logged and non-fatal to the watcher.
- **Site side:** migration creates `solver_fleet_snapshot` with anon `SELECT` policy (read-only public; no other anon grants). `useSolverFleet()` hook fetches the row, refetches every 5 min while the Rigor layer is visible. Staleness = `now − generated_at > 30 min` → banner; fetch error → panel unmounts.

### 4.5 Proof provenance (extend existing)

- Reuse `src/lib/verified-registry.ts` (async accessor over the sanitized `/verified-registry.json` — the sole proof authority, owned by the adjacent builder-prover AI, never written by us).
- `ProofChip` (new small component) + existing `ProofDrawer`: chip shows theorem name + register; click opens drawer with Lean source + AXLE certificate metadata from the registry entry.
- `src/observatory/claims.ts`: `Claim = { id, text, register, theoremName? }`. The Claim Ledger renders this; Surface/Explore copy reference claims by id so wording lives in one place.

### 4.6 Data flow summary

```
Aristotle/AXLE fleet ──(existing solver_watch, 600s)──▶ solver_manifest.json
                                              └─(new push)─▶ Supabase solver_fleet_snapshot ─▶ Rigor panel
builder-prover AI ──▶ /verified-registry.json ─▶ verified-registry.ts ─▶ ProofChip/Drawer, Claim Ledger
Published tables (Odlyzko/LMFDB) ─(fetch_zeta_zeros.py, once)─▶ public/datasets/zeta-zeros-100k.f64 ─▶ Surface Ch.2/3, Explore panels
Browser Web Worker kernel ─▶ live results + COMPUTATION provenance ─▶ Explore panels
```

## 5. Honesty invariants (hard requirements)

1. Computed ≠ proved: COMPUTATION provenance strips are visually distinct from PROVED chips everywhere.
2. No mathematical claim on screen without a Claim Ledger row and register.
3. RH, Hilbert–Pólya realization, and the zeta–Brockian bridge are OPEN/CONJECTURE and say so prominently.
4. The sanitized `/verified-registry.json` is the only proof authority; its counts are the only counts displayed.
5. Fleet panel never shows synthetic data: stale → banner, unreachable → absent.
6. Empty/error states are first-class designs, not afterthoughts.

## 6. Coordination constraints (concurrent editors)

- The builder-prover AI edits this Lovable project continuously. This build touches **only new files/routes** plus minimal registrations. The exact shared-file watchlist (the only pre-existing files this build edits): `src/site-registry.ts` (new entry), the primary nav component (one link), and the router file (one route). Re-read each via `read_file` immediately before any message that edits it. Never edit the adjacent AI's gate pages, ledger pages, or `/verified-registry.json`.
- Before each build message: check `list_edits` (limit ≥ 3, pick max `created_at` — ordering is unreliable) and re-sync assumptions if its commits touched shared files.
- Lovable ops: `send_message` with `wait=false` then poll `get_message`; preview lag ~5–10 min after commit — verify via the agent's in-sandbox crawl + pinned-commit screenshot, then re-eyeball preview.

## 7. Error handling

- Per-panel React error boundaries in Explore; a panel crash never takes down the page.
- Kernel: AbortSignal cancellation on unmount/param change; 10 s timeout → partial-result UI (§4.2). Worker hard-crash (script error / OOM termination, distinct from timeout): the client rejects all pending promises, respawns the worker once, and the owning panel's error boundary shows a retry state.
- Dataset fetch failure → fallback or honest unavailable state (§4.3).
- WebGL context loss / absence → static-still fallback per chapter (§3.1).
- Fleet feed failure → panel absent (§4.4). Registry fetch failure → ProofChips render as plain register badges with a "registry unreachable" tooltip; Claim Ledger still renders from `claims.ts`.
- Stale-chunk reloads already handled globally by `installChunkReloadHandler()`.

## 8. Performance budgets

- Initial `/observatory` chunk < 500 KB gz (layers, kernel, datasets all lazy).
- All computation off the main thread; UI stays interactive during any kernel run.
- Surface targets 60 fps desktop / 30 fps mobile; DPR capped at 2; particle/geometry counts scale by device.

## 9. Testing & verification

- **Kernel golden values (Vitest):** first 10 zeros vs published values to 1e-8; ψ(10³..10⁶) vs known values; π(10⁶)=78498; five-point spectrum vs closed forms; GUE sampler moments sanity.
- **Claim Ledger integrity test:** every PROVED claim id resolves against the registry snapshot.
- **Registry-consistency gate** (existing Vitest) stays green; new route registered in `site-registry.ts`.
- **Render verification:** in-sandbox crawl of `/observatory` at all three depths = 0 console errors; then eyes-on the actual render (pinned-commit screenshot / embed) before any publish — never ship on headless verification alone.
- **Fleet pipeline:** local run of `push_fleet_snapshot.py` → row visible via anon fetch; kill-switch test (drop the row → panel absent, no error).

## 10. Build sequence (three visible increments, publish after each verifies)

1. **Build 1 — Compute:** kernel + tests, `/observatory` route with `DepthShell` (Explore default for now) and all four Explore panels; dataset fetched from published tables + transferred via the §4.3 upload channel (checksum-verified). *Visible win: live zero computation in the browser.*
2. **Build 2 — Cinema:** Surface chapters 1–4 with fallbacks; depth default switches to Surface. *Visible win: the museum piece.*
3. **Build 3 — Rigor:** Claim Ledger + ProofChips, RH banner, fleet pipeline (Mini push + Supabase table + panel), nav/home promotion, polish pass. *Visible win: the honesty layer, live fleet.*

Each build: Lovable message(s) with explicit file scope, in-sandbox verification, eyes-on render, then user-approved publish.
