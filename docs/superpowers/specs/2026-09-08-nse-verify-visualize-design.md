# Independent Verification + Visualization of OpenAI's Euler/Navier–Stokes Blowup

**Date:** 2026-09-08
**Status:** Design v2 (incorporates spec-review round 1), pending re-review
**Repo under study:** `github.com/openai/NavierStokesAndEuler` (Apache-2.0)
**Home for our contribution:** Riemann Lab route + Artifact mirror

## 1. Purpose

OpenAI published a Lean 4 formalization of (a) finite-time blowup for the **unforced 3D
incompressible Euler equations** from smooth, compactly-supported, divergence-free data on
ℝ³, and (b) **Navier–Stokes** breakdown (Clay alternatives (C)/(D)) **with smooth forcing**,
for every positive viscosity, on ℝ³ and the torus.

We build two things no other group is pairing:

- **Track A — Independent verification.** Re-run the repo's own independent-kernel checker
  ourselves and add the one check it cannot do — whether the *challenge statements are faithful
  to the accepted mathematics* — then emit a signed attestation.
- **Track B — Visualization.** An interactive, mathematically-faithful explainer of the actual
  blowup *mechanism* (short-wave packet amplification → self-similar cascade → BKM divergence),
  anchored to the specific verified theorem.

Combined deliverable: one published page — an "independently verified" badge atop an
interactive mechanism explainer — with the honest **Euler-not-NS-prize** framing front and
center.

## 2. Honest framing (non-negotiable, appears in the deliverable)

- The **Euler** result is the headline: unforced, whole-space, smooth compactly-supported data,
  genuine finite-time singularity (‖∇u‖ limsup = ⊤ and ∫‖curl u‖ = ⊤ at T\*, Beale–Kato–Majda).
  A long-standing open problem; if the proof holds, a real advance.
- The **Navier–Stokes** result is **not** the Clay Millennium Prize. Its statements are
  `∃ u₀ f, ForceConditionDecay f ∧ ¬(∃ v p, Solution)` — existentially-quantified **forcing**,
  i.e. the Fefferman alternatives **(C)/(D)** (`NavierStokes/ComparatorSolution.lean:16-27`), not
  global regularity. We state this plainly.
- Our verification asserts **exactly** what the Lean says: that a machine-checked, independent
  second kernel confirms each proof is defeq to a faithfully-stated theorem under only the three
  standard axioms. We do not claim the mathematics is "true."

## 3. Grounding facts (verified against the cloned source, read-only)

- 616,276 lines of Lean, 2,482 files (1,839 `Euler/`, 643 `NavierStokes/`).
- Toolchain `leanprover/lean4:v4.34.0-rc2`; Mathlib rev `v4.34.0-rc2`
  (`lake-manifest.json`); Comparator rev `v4.34.0-rc2` (`lakefile.toml`).
- **`sorry`/`admit`: 4 real** occurrences, all intentional challenge placeholders in
  `ComparatorChallenges/{Euler.lean:88,184, NavierStokes.lean:277,284}`. (A naive grep also hits
  a docstring at `NavierStokes.lean:29` — hence grep is a pre-filter only; `#print axioms`, which
  surfaces `sorryAx`, is the authoritative sorry check.)
- The four real declarations are genuine sorry-free proofs:
  - `Euler.euler_breakdown_R3` — `Euler/Solution.lean:33`
  - `Euler.exists_compact_smooth_euler_singularity` — `Euler/Solution.lean:43` (the quantitative
    BKM singularity theorem: `Tstar ≤ 1`, compact support, `velocityC1Norm` limsup `= ⊤`,
    `∫⁻ vorticityNorm = ⊤`)
  - `NavierStokes.Comparator.navier_stokes_breakdown_R3` — `NavierStokes/ComparatorSolution.lean:16`
  - `NavierStokes.Comparator.navier_stokes_breakdown_periodic` — `…:23`
- **Name collision (critical for tooling):** each of the four fully-qualified names exists
  **twice** — sorried in `ComparatorChallenges/` and proved in the solution module. All
  name-based resolution MUST disambiguate by **module path** (`Euler.Solution`,
  `NavierStokes.ComparatorSolution`), never by bare name.
- The solution statements are textually identical to the challenges but resolve their
  identifiers to the solution module's **own** `ComparatorDefinitions`/`SolutionDefinitions`
  (`NavierStokes/ComparatorSolution.lean:8`), NOT the challenge's. Textual match ≠ semantic
  match — see A2.
- Both solution files embed `#print axioms …` for their theorems
  (`Euler/Solution.lean:73,75`; `NavierStokes/ComparatorSolution.lean:31,32`).

## 4. Track A — Independent Verification

### A0. The repo ships its own independent checker — we run it ourselves
`ComparatorChallenges/README.md` + the two JSON configs drive
`lake exe comparator ComparatorChallenges/{Euler,NavierStokes}.json`. Comparator
(`github.com/leanprover/comparator`, the Lean org's tool) exports each solution theorem via
`lean4export` and uses **`nanoda_bin`** — an *independent* Lean kernel reimplementation — under a
`landrun` sandbox to check that the solution theorem's type is **defeq to the Mathlib-only
challenge statement** and that its axioms ⊆ `permitted_axioms` (`{propext, Quot.sound,
Classical.choice}`, per `ComparatorChallenges/Euler.json`). `enable_nanoda: true` in both configs.

This is the machine core of independent verification and it is stronger than a hand-rolled
audit: a second kernel, not Lean's own, confirms both the proof and the statement match.

### A1. Machine verification (the gate)
1. Install `landrun`, `lean4export`, `nanoda_bin` on PATH; `lake exe cache get` (Mathlib oleans).
2. `lake build Euler.Solution NavierStokes.ComparatorSolution` (disambiguated by module path) —
   this compiles the real proofs and runs their embedded `#print axioms`.
3. `lake exe comparator ComparatorChallenges/Euler.json` and `… NavierStokes.json`.
   **Pass = green build + Comparator/nanoda reports defeq-to-challenge AND axioms ⊆ the three.**
Output: build log, `#print axioms` output, Comparator report captured as CI artifacts.

### A2. Statement-faithfulness audit (the one check Comparator cannot do)
Comparator proves *solution ≡ challenge statement*. It cannot tell us whether the **challenge
statement itself** faithfully encodes the accepted mathematics. That is our intellectual
contribution:
- **Upstream diff:** line-by-line diff of `ComparatorChallenges/{Euler,NavierStokes}.lean`
  against DeepMind Formal Conjectures' Fefferman statement
  (`FormalConjectures/Millenium/NavierStokes.lean`), enumerating and justifying every adaptation:
  zero-viscosity/zero-force (Euler), `derivWithin` on `Set.Ici 0`, position-before-time argument
  order, the `toL2` total-function fallback, ℝ≥0∞-valued suprema, `Ico`/`Icc` lifespan sets.
- **Non-vacuity argument:** confirm the negated solution class is not vacuously unsatisfiable
  (which would make `¬∃ v p, Solution` trivially true). Show the class is inhabited by genuine
  short-time solutions, and that the data guards (`u₀ ≠ 0`, `HasCompactSupport u₀`,
  `InitialVelocityConditionDecay`) are non-trivial.
- **Defeq, not implication:** the standard we hold is type-identity (what Comparator enforces),
  not mere implication — a weakening is exactly what an implication could hide.
Output: `verify/statement_audit.md`.

### A3. Attestation
Record: NSE commit SHA, Mathlib rev, Comparator rev, per-theorem `{sorry: 0 (via #print axioms),
axioms, defeq-to-challenge: true (nanoda), non-vacuity: argued}`. Two independent kernels —
Lean's (build) and **nanoda** (Comparator export) — give a defensible two-verifier claim without
a third party. Emit `verify/attestation.json` in the Aristotle-dashboard format + a dashboard
row. (AXLE is **dropped** from this path: it is lean-4.32.2 and cannot read 4.34.0-rc2
export/olean formats — the same olean-version class of failure already recorded in our notes.)

### A4. Compute
- A2 (audit) is local and immediate; needs no build.
- A1 build is **heavy**: `lake exe cache get` fetches only *Mathlib* oleans; the repo's ~616k
  first-party lines are uncached and the four closures span most of them, so "build only the
  closure" is not a real reduction. A free GitHub-hosted runner (7 GB, Lean builds OOM-prone)
  will not suffice. **A large/self-hosted runner is required** — options: a paid large GH runner,
  or Chris's compute (AutoLab exec node / Mini #2 over Tailscale) once available. Not the
  disk-pressured primary Mini.

## 5. Track B — Visualization

A single interactive page (static, self-contained; no backend, no PDE solver). Three faithful
scenes, each captioned with the matching paper section / verified-statement line. **Track B is
anchored to `exists_compact_smooth_euler_singularity`** (the theorem that actually carries the
BKM signature); `euler_breakdown_R3` is the weaker global-nonexistence statement and is cited but
not animated.

- **B1. Wave packet & short-wave instability** — rotating wavevector `m` (mₜ = −Mᵀm) and
  amplifying transverse amplitude `v` (vₜ = −Mv + 2m(m·Mv)/|m|²) on a background shear (Prop 4.1):
  unit-sphere wavevector rotation with amplitude growth; the `ℓ/k` small-prefactor / large-
  gradient trade-off.
- **B2. Self-similar cascade** — Figure 1's loop: each amplified packet's leading gradient
  becomes the parent shear of the next, on nested intervals `tⱼ ↑ T_∞`: matryoshka of packets at
  shrinking scales + a timeline collapsing to finite `T_∞`; annotate the "gradients blow up while
  initial increments stay summable in every Hᵐ" balance (why the datum is smooth).
- **B3. Blowup signature** — animate `velocityC1Norm` limsup → ⊤ and `∫⁻ vorticityNorm` → ⊤ as
  t → T\* (BKM), tied to the exact clauses of the singularity theorem.

Each scene is an isolated component with a small documented parameter interface (α, k, ℓ, stage
j) so scenes are understood/tested independently. Faithful to the equations, tuned for legibility.

## 6. Combined deliverable & home

- **Riemann Lab route** (fits the lab brand; matches KG v3 / atlas pattern): verified badge
  (Track A attestation, honest framing) + the three-scene explainer.
- **Artifact mirror**: self-contained HTML, shareable immediately; dual-theme, legibility floor.
- Cross-links to the OpenAI repo, DeepMind Formal Conjectures upstream, Comparator, and our
  attestation JSON.

## 7. Testing

- A1: CI is the test — green build + Comparator pass (defeq + permitted axioms) is the gate.
- A2: golden-file extraction of the four statements; the upstream diff reviewed by a second pass.
- B: each scene renders light/dark, no horizontal body scroll, math annotations match the spec;
  eyes-on render before "done" (never ship flagship UI headless-only).

## 8. Risks / open items

- **Build cost/infra** is the main risk — see A4; secure a large runner before committing to A1.
- **Comparator toolchain deps** (`landrun`, `lean4export`, `nanoda_bin`) must be installable at
  v4.34.0-rc2; verify versions match the pinned Comparator rev.
- **"harmonic"** (Chris's word) is not required for a defensible two-verifier claim now that
  nanoda is the independent kernel; keep as optional third cross-check, confirm intent.
- **Statement audit (A2) is where any real critique lives** — give the upstream diff and
  non-vacuity argument the most care.

## 9. Out of scope (YAGNI)

- Re-proving or improving the mathematics.
- A full PDE solver / numerical blowup reproduction.
- Verifying anything beyond the four named declarations.
- Any claim about the Millennium Prize.
