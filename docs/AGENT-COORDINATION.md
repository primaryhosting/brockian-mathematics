# Agent Coordination Queue

Current checkpoint: 2026-08-01, after integrator wire of FreeLaplacian2 + EquidistributionSchema + AffineSymmetry.

This file is the shared handoff surface for Claude, Codex, Grok, Aristotle downloads,
and any fresh proof agent.  Use it to avoid duplicate work and to keep the next attacks
small enough to verify.

## Non-Negotiable Integration Rules

1. Start every session with:

```bash
git status --short --branch
git log --oneline -8
```

2. Never use `git add -A`.  Stage explicit files only.
3. Do not edit or revert another agent's dirty file unless the newest user message asks
   for that exact integration.
4. A proof only enters `Brockian.lean` after:

```bash
python3 scripts/no_theater_lint.py <file>.lean
python3 scripts/attest.py <file>.lean <Namespace> <decl1> ... --env lean-4.32.0
```

For Gate-1/Weyl bridge files, also check:

```bash
python3 scripts/attest.py <file>.lean <Namespace> <decl1> ... --env lean-4.28.0
```

5. If `scripts/attest.py` writes a namespace-short duplicate such as
   `registry/attestations/Bridge.json` or `SchrodingerESA.json`, keep only the canonical
   module attestation used by the registry (`WeylBridge.json`, `WeylSchrodingerESA.json`,
   etc.).
6. Regenerate public artifacts only after the attestation is canonical:

```bash
python3 scripts/gen_registry.py
python3 scripts/gen_claims.py
python3 scripts/gen_observatory.py
python3 scripts/gen_paper_table.py
```

7. Commit by explicit path.  Example:

```bash
git add Brockian/NewModule.lean Brockian.lean provenance/verdicts.yaml \
  registry/attestations/NewModule.json registry/theorems.json REGISTRY.md \
  PORT-QUEUE.md paper/registry_counts.tex paper/registry_table.tex \
  observatory/claims.yaml observatory/claims.json observatory/index.html
git commit -m "feat(NewModule): precise theorem being integrated"
```

## Current Verified State

Gate 1 is now reduced to a named Mathlib infrastructure gap, not an undefined hope.

Closed and registered:

- `Brockian.Weyl.Bridge.no_nonzero_L2_solution`: non-real L2 classical solutions vanish.
- `Brockian.Weyl.SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge`: ESA under the
  explicit `DeficiencyRepresentsODE` hypothesis.
- `Brockian.Weyl.SchrodingerESA.primeGaussian_essentiallySelfAdjoint`: potential term ESA.
- `Brockian.Automorphism.Full.autEquivDihedral`: full `Aut(C5) ~= D5`.

Still open:

- Construct the actual minimal unbounded `T = -d2/dx2 + V` on `L2(R)`.
- Prove `DeficiencyRepresentsODE` for that `T`.
- Prove free Laplacian ESA and unbounded Kato-Rellich if taking the perturbation route.
- For RH, replace the current decaying bounded potential by a confining candidate or prove
  explicitly why the current operator shape cannot have the required discrete spectrum.

## My Recommended Attack Queue

These are ordered by expected proof yield in this repo, not by philosophical importance.

### 1. `WeylSchrodingerMinimal`

Target file: `Brockian/WeylSchrodingerMinimal.lean`

Goal: define the minimal Schrodinger operator interface precisely enough that
`DeficiencyRepresentsODE` has a concrete target.

Suggested declarations:

- `SchrodingerCore`
- `schrodingerPMap`
- `schrodingerPMap_domain`
- `schrodingerPMap_isSymmetric` under compact-support or boundary-vanishing hypotheses
- `deficiencyRepresentsODE_of_adjoint_eigenvector` as the exact remaining statement if the
  full distributional regularity proof is too large

Why this is first: it turns the last Gate-1 gap from a prose sentence into one or two Lean
statements with exact hypotheses.  Claude/Codex can split this into "define T" and
"prove ODE representation" without touching each other's files.

Do not claim full `-Delta+V` ESA unless `DeficiencyRepresentsODE` is discharged for the
same concrete `T`.

### 2. `WeylFreeLaplacian`

Target file: `Brockian/WeylFreeLaplacian.lean`

Goal: free Laplacian ESA, preferably via a Fourier/multiplication abstraction.

Suggested first rung:

- define an abstract unitary-equivalent multiplication model,
- prove ESA transfers across the unitary equivalence,
- instantiate the multiplication-by-real-function side before trying the real Fourier
  transform.

Why this is second: a full Fourier proof may be too big for one pass, but the transfer
lemma is reusable and should verify in the existing operator framework.

### 3. `WeylOperatorChoice`

Target file: `Brockian/WeylOperatorChoice.lean`

Goal: make the RH operator mismatch explicit and machine-checkable.

Suggested declarations:

- `DecayingPotentialCandidate` / `ConfiningPotentialCandidate` as definitions.
- `rh_operator_needs_discrete_spectral_model` as a conditional necessary-condition theorem
  tied to `BrockianSystem.eigen_of_zero`.
- A non-theorem note or conditional schema explaining that bounded decaying
  prime-Gaussian potential is a Gate-1 test object, not a Hilbert-Polya candidate.

Why this is third: it prevents the program from accidentally spending weeks proving ESA
for an operator that the RH route cannot use.

### 4. `D5Representation`

Target file: `Brockian/D5Representation.lean`

Goal: downstream consequences of the now-complete `Aut(C5) ~= D5`.

Suggested declarations:

- action of `DihedralGroup 5` on functions `Fin 5 -> C`,
- constant subspace fixed by the action,
- rotation eigenmodes for fifth roots,
- isotypic projector definitions and basic idempotence/orthogonality lemmas.

Why this is fourth: finite algebra is one of the repo's highest-yield zones.  It is much
more likely to close than new unbounded analysis and strengthens the pentagonal spectral
side independently of RH.

### 5. `MetallicFamily`

Target file: `Brockian/MetallicFamily.lean`

Goal: generalize the "why five" story carefully without overclaiming.

Suggested declarations:

- metallic mean recurrence lemmas,
- `C5` specializations already implied by `golden_unique_to_five`,
- finite checked examples for silver/metallic candidates recorded as COMPUTATION if they
  use `native_decide`, not PROVED.

Why this is fifth: it is rich and probably publishable, but it can become numerology if the
statements are not pinned to precise algebraic spectra.

## Parallel Ownership Suggestions

- Claude: take `WeylSchrodingerMinimal`, because it benefits from careful statement design
  and precise prose around the remaining hypothesis.
- Codex: take `D5Representation`, because it is finite, local, and likely to close quickly.
- Grok/Aristotle: continue `boundedv-continuous` only with the corrected continuous or
  locally-integrable hypothesis.  Do not resurrect the refuted bare-bounded target.
- Any agent with analysis bandwidth: take `WeylFreeLaplacian` as a staged abstraction,
  not as a one-shot full Fourier formalization.

## Handoff Template

When leaving work for another agent, append a short note in the relevant file header or
`PORT-QUEUE.md`:

```text
Owner:
Target theorem:
Current status:
Verified commands:
Known blocker:
Do not touch:
```

Keep the note factual.  If a theorem is not AXLE-clean, it is not integrated.

## Active Claims (append-only)

- 2026-08-01 — **Claude claims `WeylSchrodingerMinimal`** (queue #1). Independently
  re-audited `WeylBridge.no_nonzero_L2_solution` = VERIFIED @ both lean-4.32.0 and
  lean-4.28.0, axiom-clean {propext, Classical.choice, Quot.sound}, statement faithful
  (proved even without the boundedness/continuity hypotheses). Proceeding to define the
  concrete minimal `T = -d²/dx²+V` and state/prove `DeficiencyRepresentsODE` for it.
  Do not touch `Brockian/WeylSchrodingerMinimal.lean`.

## Active Claims — Claude swarm (2026-08-01, append-only)

Claude launching a swarm on non-conflicting Gate-1-completion + cleanup targets. Do not
touch these files (in progress): `Brockian/WeylFreeLaplacian2.lean`, `Brockian/WeylKatoUnbounded.lean`,
`Brockian/WeylSelfAdjointExtension.lean`, `Brockian/SingularSeriesConvergence.lean`,
`Brockian/MetallicFamily.lean`. (Codex keeps D5Representation; Grok/Aristotle
keep boundedv-continuous.)

- 2026-08-01 — **Grok ships `WeylFreeLaplacian` + `WeylOperatorChoice`** (queue #2–#3).
  Both AXLE-verified @ lean-4.32.0, axiom-clean, no-theater lint clean, imported in
  `Brockian.lean`. Canonical files:
  - `Brockian/WeylFreeLaplacian.lean` — unitary ESA transfer (`conjCLM`), free-model
    packaging, Kato symmetry half (`isSymmetric_vadd_clm`). Does **not** construct
    unbounded −Δ or full unbounded Kato range-density.
  - `Brockian/WeylOperatorChoice.lean` — bounded-eigenvalue obstruction
    (`primeGaussian_not_realize_large_zero`, `rh_operator_needs_unbounded_spectrum`);
    decaying vs confining candidate shapes. Does **not** claim RH.
  Attestations: `registry/attestations/WeylFreeLaplacian.json`,
  `registry/attestations/WeylOperatorChoice.json`. Do not overwrite these two files
  without re-attesting.

- 2026-08-01 — **Claude ships `WeylSelfAdjointExtension`** (queue #4, roadmap item #4).
  AXLE-verified @ lean-4.32.0, all 15 declarations axiom-clean
  {propext, Classical.choice, Quot.sound}, no-theater lint clean, imported in
  `Brockian.lean`. Canonical file `Brockian/WeylSelfAdjointExtension.lean`
  (namespace `Brockian.Weyl.Extension`), attestation
  `registry/attestations/WeylSelfAdjointExtension.json`. Highlights:
  `adjoint_closure` (`(T̄)* = T*`, the closure-blindness of the graph-adjoint),
  `closure_isSymmetric` (closure of symmetric is symmetric — no graph-limit needed),
  `closure_eigenvalue_im_zero` (real spectrum of `T̄`), `le_closure_le_adjoint`
  (`T ⊆ T̄ ⊆ T*`), `closure_le_of_isSelfAdjoint_extension` (`T̄` minimal among
  self-adjoint extensions), and the crisp Gate-isolator
  `isSelfAdjoint_closure_iff_eq_adjoint` (**`T̄` self-adjoint ⟺ `T̄ = T*`**).
  Does **NOT** prove `T̄ = T*` / strict uniqueness `S = T̄`: both reduce to the reverse
  inclusion `T* ⊆ T̄`, i.e. the double-adjoint `T̄ = T** ` + "deficiency-free ⟹
  self-adjoint" von Neumann fact absent from Mathlib v4.32.0. Blocker named, not faked.
  Do not overwrite without re-attesting.

- 2026-08-01 — **Claude ships `SingularSeriesConvergence`** (roadmap item #17, the dropped
  `singular_series_converges` PORT-QUEUE axiom). AXLE-verified @ lean-4.32.0, all 6
  declarations axiom-clean {propext, Classical.choice, Quot.sound}, no-theater lint clean.
  Canonical file `Brockian/SingularSeriesConvergence.lean` (namespace
  `Brockian.SingularSeries.Convergence`), attestation
  `registry/attestations/SingularSeriesConvergence.json`. The analytic ∞-product convergence
  is now PROVED, not axiomatized. Chain: `err_bound` (`|(1-x)^k-(1-kx)| ≤ k²x²`,
  elementary induction) → `nu_p_eq_card_of_lt` (residue map injective for large `p`, so
  `ν=k` on the tail) → `localFactor_sub_one_bound` (uniform tail bound
  `|localFactor p − 1| ≤ 2^k·k²/p²`) → `summable_localFactorAt_sub_one` (comparison with
  `∑ 1/p²`, small primes shifted past via `summable_nat_add_iff`) →
  `singularSeriesFinite_tendsto_pos` (multipliable via `Real.multipliable_of_summable_log`;
  limit `= rexp(∑ log …) > 0` via `Real.rexp_tsum_eq_tprod`) → **UNCONDITIONAL**
  `singular_series_pos'` (discharges the `h_conv` hypothesis of the existing
  `singular_series_pos`; admissibility alone now gives `0 < singularSeries G`). Does **not**
  touch `Brockian/SingularSeries.lean` (only imports it). NOT yet imported in `Brockian.lean`
  / registry (no git per task). Do not overwrite without re-attesting.

- 2026-08-01 — **Grok swarm #2** claims the following *new* files only (do not take these):
  - `Brockian/D5Isotypic.lean` — rotation eigenmodes + isotypic projectors on Fin 5 → ℂ
  - `Brockian/WeylConfining.lean` — confining-potential necessary lemmas (not RH)
  - `Brockian/WeylMulReal.lean` — real L∞ multiplication ESA (bounded free/potential model)
  - `Brockian/GoldbachParity.lean` — small unconditional Goldbach/parity lemmas if hole-free
  - `Brockian/CycleSpectrumFamily.lean` — C_n spectrum family (not MetallicFamily.lean)
  - Integrator task: wire already-attested `SingularSeriesConvergence` + `WeylFreeLaplacian2`
    into `Brockian.lean` + registry if not already integrated (surgical; no content rewrite).
  Do **not** touch: WeylSchrodingerMinimal, MetallicFamily, WeylKatoUnbounded, FreeLaplacian
  (canonical Grok), OperatorChoice (canonical Grok), or any file with an active Claude claim.

- 2026-08-01 — **Grok executes strategic top-3**: audited MulReal/Confining/CycleSpectrum/GoldbachParity
  (already on main, registry live). **Shipped `D5Isotypic`** AXLE-verified @4.32 (eigenmodes +
  character sums + projector diagonalization on eigenmodes). Registry summary after integrate:
  PROVED ≈ 535+. Next per 20-move list: projector full-space idempotence, C5 spectral
  multiplicities packaging, singular-series downstream rewiring, Mathlib-upstream candidates.

- 2026-08-01 — **Claude ships `AffineSymmetry`** (paper audit target #3: retires the
  Papers 2 & 4 automorphism-conflation error). AXLE-verified @ lean-4.32.0, all 12
  declarations axiom-clean {propext, Classical.choice, Quot.sound}, no-theater lint clean.
  Canonical file `Brockian/AffineSymmetry.lean` (namespace `Brockian.AffineSymmetry`),
  attestation `registry/attestations/AffineSymmetry.json`. Cleanly SEPARATES the three
  conflated groups:
  - **additive-aut** `AddAut (ZMod p) ≃+ Additive (ZMod p)ˣ ≅ C_{p-1}` (`additiveAutEquivUnits`,
    Mathlib `ZMod.AddAutEquivUnits`); order `p-1` general (`additiveAut_card`), `= 4` at p=5
    (`additiveAut_card_five`); cyclic (`units_isCyclic`). This is mult-by-a-unit — NOT `D_p`.
  - **graph-aut** `C₅ ≃g C₅ ≅ D₅` order 10 — references `Automorphism.Full.aut_card_eq_ten`.
  - **±1-affine dihedral** `dihedralToPerm : DihedralGroup p →* Equiv.Perm (ZMod p)`
    (`i ↦ ±i+c`), faithful (`dihedralToPerm_injective`, needs `(2:ZMod p)≠0`), order `2p`
    (`dihedralToPerm_card`), living inside `Aff(1,F_p)` (`affineGroup`,
    `dihedralToPerm_range_le_affineGroup`). THIS is the map the papers actually meant.
  - `symmetry_separation`: orders 4 / 10 / 10 with `4 ≠ 10` — the additive-aut is NOT `D₅`.
  Imports `Brockian.AutomorphismFull` only (reuses the completed `Aut(C₅) ≅ D₅`); touches no
  other agent's file. NOT yet imported in `Brockian.lean` / registry (no git per task).
  Do not overwrite without re-attesting.

- 2026-08-01 — **INTEGRATOR (Grok) wires AXLE-attested modules into public surface** (import-only; no proof rewrites).
  Root imports added/confirmed in `Brockian.lean`:
  - `Brockian.SingularSeriesConvergence` (already present; registry already had 6 PROVED)
  - `Brockian.WeylFreeLaplacian2` (**new** import; attestation `WeylFreeLaplacian2.json`)
  - `Brockian.EquidistributionSchema` (**new** import; attestation `EquidistributionSchema.json`;
    HL/BV ⇒ density theorems marked CONDITIONAL open via provenance)
  - `Brockian.AffineSymmetry` (**new** import; attestation `AffineSymmetry.json`)
  Previously integrated and re-confirmed present: MetallicFamily, WeylKatoUnbounded,
  WeylSelfAdjointExtension, AdmissibilityCRT, PenroseL2, WeylSchrodingerMinimal, D5Representation.
  **Not imported:** `CycleSpectrumFamily` (no attestation yet); never touch
  `aristotle/kato-bounded/KatoBounded.lean`. Regenerated registry / claims / observatory /
  paper tables. claim_map: SS-CONV, GATE1-FREE-TRANSFER2, GATE1-SCHRODINGER-MINIMAL.
  Concurrent landings while integrating (already on main): `2a51d5c` FreeLaplacian2+EquidistributionSchema,
  `13d9602` AffineSymmetry (+ accidental `WeylMulReal` root import without attestation/file).
  Integrator removed `import Brockian.WeylMulReal` (no `module_verified` attestation; file still untracked
  for the owning agent). Public PROVED: 395 → 416 (+21 from FreeLaplacian2/Equidistribution/Affine).


- 2026-08-01 — **Grok swarm #3** (AXLE pipeline required for every ship). Claims *new files only*:
  - `Brockian/D5LaplacianModes.lean` — projectors diagonalize C5 adjacency/Laplacian
  - `Brockian/C5SpectralMultiplicities.lean` — spectrum of C5 with multiplicities
  - `Brockian/D5FourierInversion.lean` — full-space Fourier inversion / projector idempotence on VertexSpace
  - `Brockian/SingularSeriesWire.lean` — re-export unconditional singular_series_pos' for downstream use
  - `Brockian/ConfiningSpectralShape.lean` — necessary conditions packaging for confining operators (not RH)
  - `Brockian/GoldenUniquenessSchema.lean` — reusable schema around golden_unique_to_five
  Do not touch Minimal, MetallicFamily, FreeLaplacian*, OperatorChoice, D5Isotypic (extend via imports only).
  Pipeline for each: hole-free proofs → `no_theater_lint` → `attest.py --env lean-4.32.0` →
  `registry/attestations/<Module>.json` only if `module_verified: true`.

- 2026-08-01 — **Codex swarm #4 launched** (documentation/infrastructure only; no Lean proof files).
  Purpose: make the verification pipeline easier for Claude/Grok/Codex to share without
  colliding with active proof work. Claimed write scopes:
  - `docs/PROOF-DEPENDENCY-MAP.md` — registry-backed dependency map for Gate 1, D5/pentagonal,
    singular-series/Goldbach, and RH scaffold. Agent: Singer (`019fbee7-1604-7d82-8fc5-1bc788c09d07`).
  - `scripts/audit_registry_opens.py` — local audit for remaining CONDITIONAL/CONJECTURE entries
    and stale-open patterns. Agent: Faraday (`019fbee7-2a69-7983-980c-9e71c3ee5a83`).
  - `docs/MATHLIB-UPSTREAM-CANDIDATES.md` — upstream-candidate list with exact local
    declarations and cleanup requirements. Agent: Meitner (`019fbee7-45aa-7df3-b185-406e4e04aca3`).
  Do not let these agents edit `Brockian/*.lean`, registry attestations, or generated registry
  artifacts. Integration contract: review output → commit explicit paths only → no `git add -A`.
  Integrated at `95ac7e3`: all three artifacts reviewed and committed by explicit path only.
  Validation run: `python3 -m py_compile scripts/audit_registry_opens.py` and
  `python3 scripts/audit_registry_opens.py`. Integration-time open-surface audit reported
  8 `CONDITIONAL` entries + 1 `CONJECTURE`, no stale target Prop containers detected.
  After concurrent proof commits through `ad024f0`, the refreshed audit reports 695 `PROVED`,
  182 `DEFINITION`, 10 `CONDITIONAL`, and 1 `CONJECTURE` over 888 registry entries.
