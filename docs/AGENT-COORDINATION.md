# Agent Coordination Queue

Current checkpoint: 2026-08-02 — **LIVE multi-agent collab (Claude × Codex × Grok)**.

**Full protocol:** [`docs/MULTI-AGENT-COLLAB.md`](MULTI-AGENT-COLLAB.md)  
**Status board:** `python3 scripts/agent_board.py`

---

## LIVE BOARD (2026-08-02) — read before every edit

| Agent | Owns right now | Do not touch |
|-------|----------------|--------------|
| **Claude / Codex** | **SHIPPED** Gate-1 package @ `d20fd09` (`WeylWeakPrimitiveLocal` + `WeylKatoResolventConstruction`). Optional: remaining `aristotle/*` scratch | Grok pipeline/partner files mid-edit |
| **Grok** | `pipeline/`, `docs/partner/`, `docs/MULTI-AGENT-COLLAB.md`, `scripts/agent_board.py`, settle/refute/distill, finite sieve certs | Stretch Weyl proofs Claude/Codex own next; leave their `aristotle/*` alone |
| **Aristotle** | Race targets under `aristotle/` (owner of each job) | Brockian root without AXLE |

### Shipped together (collab recognition)

1. Grok `7489f9e` — verified-intelligence pipeline + partner pack  
2. Claude/Codex `d20fd09` — Gate-1 weak primitive + Kato resolvent reductions  

Next non-colliding split: Codex/Claude → construct resolvents / drop weak-reg hypothesis; Grok → SAIR refute + torus honesty + Mathlib harvest.

### Grok claim (append 2026-08-02 collab)

- **Grok collab support:** multi-agent protocol, `agent_board.py`, link pipeline cards to shipped Gate-1 modules. No Weyl proof edits.

---

## Multi-domain pipeline + settle

Problem cards: `pipeline/catalog/<domain>/`. Certificate unit of progress: `scripts/settle.py`
(see `docs/SETTLE-FACTORY.md`). Dry-run formalize→verify plan:

```bash
python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean
python3 -m pipeline.scripts.pipeline_cli ledger
python3 scripts/gen_program_report.py
python3 -m pipeline.artifacts.cs.sieve_counts --check
```

Partner pack: `docs/partner/` (strategy, torus audit, Mathlib/PhysLean harvest, QP targets).
Do not invent PROVED at problem level without AXLE. Lean still requires
`no_theater_lint` + `attest.py` before `Brockian.lean` import.

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

- 2026-08-01 — **Codex swarm #5 launched: bigger six-lane attack** (proof + upstream
  infrastructure; disjoint write scopes, no root-import or registry-generation until integration).
  Current shared audit before launch: 695 `PROVED`, 182 `DEFINITION`, 10 `CONDITIONAL`,
  1 `CONJECTURE` over 888 registry entries. Existing dirty lanes left untouched:
  `aristotle/kato-bounded/KatoBounded.lean` and `registry/attestations/WeylConfining.json`.
  Active agents:
  - Sagan (`019fbf12-4034-7b01-959e-e68a2b0b64f2`) — `Brockian/WeylWeakRegularityScaffold.lean`.
    Target: narrow `WeakSolutionRegularity` / `DeficiencyRepresentsODE` to verified pairing,
    domain, or ODE-representation lemmas. No edits to existing `WeylDeficiency*` files.
  - Harvey (`019fbf12-571d-71f0-93c9-c787b00c893f`) — `Brockian/WeylFourierMultiplier.lean`.
    Target: Fourier/free-Laplacian route, especially unitary-equivalence, range-density, or
    multiplication-model lemmas toward the open Fourier multiplier input.
  - Sartre (`019fbf12-73b0-74e0-9b4e-515a51f077d0`) — `Brockian/WeylKatoRangeDensity.lean`.
    Target: bounded/small-norm/range-density lemmas toward `BoundedPerturbationTransfer`.
    Must not touch `WeylKatoUnbounded.lean` or Aristotle's Kato file.
  - Huygens (`019fbf12-d0a9-7c71-8a00-82b991c9b18c`) —
    `Brockian/GoldbachCovarianceScaffold.lean`. Target: finite/local covariance-kernel
    consequences that reduce pressure on `GoldbachCovarianceTransfer` without claiming
    Goldbach or prime asymptotics.
  - Cicero (`019fbf12-e639-7e02-8b11-d4b26df3cc9c`) —
    `Brockian/EquidistributionFiniteScaffold.lean`. Target: finite/support/counting
    consequences around `PrimePairAsymptotic` and admissible configurations; no HL/BV claim.
  - Mill (`019fbf12-fc65-75a1-8835-a4c4647d8e73`) —
    `docs/MATHLIB-PR-BLUEPRINTS.md` and optionally `scripts/list_upstream_decls.py`.
    Target: PR-sized upstream extraction plan and dependency/import audit; no Lean proof edits.
  Integration contract for this swarm: accept only hole-free files; run `no_theater_lint`;
  AXLE-attest Lean modules at `lean-4.32.0`; for Gate-1/Weyl files also attempt
  `lean-4.28.0`; import into `Brockian.lean` only after canonical attestation; commit by
  explicit path only.

- 2026-08-01 — **Claude swarm #5 launched** (AXLE @4.32 gate required for every ship; new files only).
  Uncovered high-value territory — no overlap with Grok #3 / Codex #4 / prior swarms. Claims:
  - `Brockian/PentagonalPartition.lean` — Euler's pentagonal number theorem / partition ↔ pentagonal
    bridge (`Nat.Partition`; generating function ∏(1-xᵏ) = ∑(-1)ʲx^{j(3j-1)/2} and/or the p(n)
    pentagonal recurrence). NEW territory — the headline Euler↔Ramanujan connection, absent from core.
  - `Brockian/AdmissibilityKTuple.lean` — general admissible k-tuple configuration count over `ZMod q`
    via CRT + inclusion–exclusion (generalizes `universal_admissibility_count`; replaces the
    superseded `(q-1)^{k-1}` guess). Imports `Admissibility` only.
  - `Brockian/GaloisGeneralDegree.lean` — attempt the general `[ℚ(2cos 2π/p):ℚ] = (p-1)/2`
    (extends `GaloisWhyFive`'s concrete {3,5,7}); honest partial expected if Mathlib lacks the
    maximal-real-subfield degree. Imports `GaloisWhyFive`/`Spectral` only.
  Do NOT touch these files or Admissibility/GaloisWhyFive/Spectral internals (extend via import only).
  Pipeline each: hole-free → `no_theater_lint` → AXLE `check` @lean-4.32.0 → attestation only if
  `module_verified`. Claude integrates via explicit-path commit + registry regen.
  Aristotle follow-up: `c6a46c07` (bridge-deficiency) DONE server-side but Harmonic API 500s on
  download (unretrievable — not integrated); `2204b385` (boundedv-continuous) still RUNNING.

- 2026-08-01 — **Claude swarm #5 INTEGRATED** (all three, AXLE @4.32, axiom-clean, lint-clean, explicit-path commits):
  - `PentagonalPartition` (`8d0cf50`) — Euler pentagonal numbers + injectivity (distinct PST exponents) + p(0)=1 vs Nat.Partition; full PST/recurrence OPEN; NO C5/D5 bridge claimed.
  - `AdmissibilityKTuple` (`ccb0f92`) — general k-tuple count |A_q(H)|=q-|H| (refutes (q-1)^{k-1}); CRT lift; roadmap #14.
  - `GaloisGeneralDegree` (`90e1f0e`) — **FULL general why-five**: [Q(2cos 2pi/p):Q]=(p-1)/2 for all odd primes + quadratic_iff_five_general. Closes the case GaloisWhyFive left open.
  Registry now 726 PROVED / 186 DEFINITION / 10 CONDITIONAL / 1 CONJECTURE, 0 dups, 0 UNVERIFIED.
  Aristotle c6a46c07 (bridge-deficiency) STILL 500 on download (Harmonic API outage, unretrievable);
  2204b385 (boundedv-continuous) status per list above. Next open frontier for whoever's free:
  confining⇒discrete-spectrum (Rellich, #6), general multi-factor CRT admissibility, full PST (Franklin).

- 2026-08-01 — **Claude swarm #6 launched** (AXLE @4.32 gate; new files only; each cleanly extends a
  Claude-owned module — NO overlap with Grok/Codex Weyl/Goldbach/equidistribution scaffolds in flight
  [WeylFourierMultiplier, WeylKatoRangeDensity, WeylWeakRegularityScaffold, GoldbachCovarianceScaffold,
  EquidistributionFiniteScaffold] or C5SpectralMultiplicities finrank work). Claims:
  - `Brockian/AdmissibilityCRTGeneral.lean` — iterated multi-factor CRT admissible count
    `∏ᵢ (qᵢ − |Hᵢ|)` over arbitrary pairwise-coprime moduli (extends AdmissibilityKTuple + AdmissibilityCRT
    beyond the 2-factor lift). Imports AdmissibilityKTuple/AdmissibilityCRT only.
  - `Brockian/GaloisMinPolyFamily.lean` — explicit minimal polynomial of 2cos(2π/p): the monic integer
    polynomial of degree (p−1)/2 (Ψ_p / real-cyclotomic, Chebyshev-related) = minpoly ℚ (spectralGen p);
    generalizes the concrete Q5=X²+X−1, P7=X³+X²−2X−1 in GaloisWhyFive. Imports GaloisGeneralDegree/GaloisWhyFive/Spectral only.
  - `Brockian/PentagonalTheoremFranklin.lean` — attempt the full Euler pentagonal number theorem
    (Franklin involution) or the p(n) pentagonal recurrence; honest partial expected (Mathlib-absent).
    Imports PentagonalPartition only.
  Do NOT touch those files or Admissibility*/Galois*/Pentagonal* internals (extend by import only).
  Pipeline each: hole-free → no_theater_lint → AXLE check @lean-4.32.0 → attestation only if module_verified.

- 2026-08-01 — **Grok swarm #4** (keep proving; AXLE @4.32 required). New files only:
  - `Brockian/Fin5InnerProduct.lean` — Hermitian product on VertexSpace; eigenmode orthogonality
  - `Brockian/GoldbachLocalWheel.lean` — finite K₂/K₃ wheel lemmas (not global Goldbach)
  - `Brockian/SingularSeriesExamples.lean` — concrete admissible G examples with positive series
  - `Brockian/ConnectivityGoldenBridge.lean` — λ₂(C₅)=2−1/φ packaging lemmas
  - `Brockian/WeylSymmetryPackage.lean` — short package of IsSymmetric real-spectrum facts for reading path
  - Integrator: ship `WeylFourierMultiplier` (already AXLE verified) into Brockian.lean + registry
  Also attempt repair (optional, same claim): KatoRangeDensity / WeakRegularityScaffold if still failing.
  Pipeline: hole-free → no_theater_lint → attest.py → json only if module_verified.
  Do not touch PentagonalPartition, AdmissibilityKTuple, GaloisGeneralDegree, NewEra internals.

- 2026-08-01 — **Grok swarm #6 on 39-move map** (804 PROVED baseline). New files; AXLE @4.32 required:
  - Lane A#4 `Brockian/OddDistinctPartition.lean` — p_odd=p_distinct wire Mathlib
  - Lane B#10 `Brockian/CosAlgebraicInteger.lean` — 2cos(2π/p) algebraic integer / minpoly degree hooks
  - Lane C#12 `Brockian/AdmissibilityDiagonal.lean` — g≡0 mod q → count q−1
  - Lane C#15 `Brockian/TwinPrimeConstant.lean` — 𝔖({0,2}) concrete reduction
  - Lane E#25 `Brockian/WeylLawTarget.lean` — N(T)~(T/2π)log conditional schema (CONDITIONAL)
  - Lane G#34 / integrate: finish+ship Fin5InnerProduct, GoldbachLocalWheel, WeylSymmetryPackage if verified
  Do not fake Franklin PST, RH, full free −Δ, or Brun sieve. Pipeline: hole-free → lint → attest → json if verified.

- 2026-08-01 — **Codex swarm #5 INTEGRATED** (six-lane bigger attack; all accepted lanes
  AXLE/lint-gated, no root-import without attestation):
  - `WeylFourierMultiplier` (`e4cf92f` + integration `acd864e`) — Fourier multiplier dense-range
    transfer layer. Independently rechecked by Codex: no-theater lint clean, canonical
    `WeylFourierMultiplier.json` verified @4.32, extra read-only AXLE cross-check verified @4.28.
    Full free `-Δ` ESA still needs Plancherel + unbounded `ξ²` multiplier dense ranges +
    domain/action intertwining.
  - `WeylWeakRegularityScaffold` (integrated in `7b07d26`) — deficiency vector now unpacks to
    the weak Schrodinger equation; remaining analysis is exactly weak-to-classical regularity.
  - `WeylKatoRangeDensity` (`6cd3878`) — faithful range-density transfer API, closed-range
    upgrades, zero perturbation, bounded self-adjoint witness; verified @4.32 and @4.28.
    Does not prove unbounded Kato-Rellich.
  - `GoldbachCovarianceScaffold` (`230a41f` + integration `7b07d26`) — finite p=2,3 wheel
    and singular-series local inputs; does not prove `GoldbachCovarianceTransfer`.
  - `EquidistributionFiniteScaffold` (`7aaf495`) — finite prime-pair config partition,
    non-admissible-zero and finite deviation bounds; no HL/BV or global equidistribution claim.
  - `docs/MATHLIB-PR-BLUEPRINTS.md` + `scripts/list_upstream_decls.py` (`c12fb00`) —
    16 PR-sized upstream extraction plan; script is read-only and `py_compile` clean.

- 2026-08-01 — **Codex swarm #6 launched from the 39-move map** (non-overlap with active
  Claude/Grok claims; AXLE @4.32 required for Lean files, explicit-path integration only).
  Initial audit baseline after current integrations: 804 `PROVED`, 201 `DEFINITION`,
  12 `CONDITIONAL`, 1 `CONJECTURE` over 1018 registry entries.
  Active agents:
  - Maxwell (`019fc09e-5d83-76b3-9db9-9b3781a36f18`) — item #35,
    `scripts/audit_dependency_firewall.py` + `docs/DEPENDENCY-FIREWALL.md`; read-only
    overclaim-firewall audit.
  - Schrodinger (`019fc09e-7a23-76b3-9bc2-62fa29d4942b`) — item #36,
    `scripts/audit_registry_consistency.py` + `docs/REGISTRY-CONSISTENCY.md`; read-only
    conditional/conjecture/provenance self-consistency audit.
  - Popper (`019fc09e-8f65-7893-973b-abca4ba3b94f`) — item #39,
    `scripts/gen_paper_theorem_table.py`, `paper/theorem_table.md`,
    `docs/PAPER-TABLE-GENERATION.md`; paper-ready theorem table generator.
  - Dewey (`019fc09e-b43d-7580-83c4-8353554f6782`) — item #11, retargeted after collision
    with Grok's `AdmissibilityDiagonal`: now `Brockian/AdmissibilityCriterionScaffold.lean`
    only, toward local admissibility-criterion equivalences.
  - Gibbs (`019fc09e-d1d4-7852-a43b-61d11f60882d`) — item #19, retargeted after collision
    with Grok's `TwinPrimeConstant`: now `Brockian/EquidistributionDeviationBound.lean`
    only, finite deviation-bound packaging.
  - Herschel (`019fc09e-eb4d-7832-8ff6-05a4fc2c2f62`) — item #28,
    `Brockian/RiemannXiFunctionalEquation.lean` only if Mathlib has enough xi/functional
    equation API; otherwise report the exact blocker and write no theorem.
  Do not touch Grok-owned `OddDistinctPartition`, `CosAlgebraicInteger`, `AdmissibilityDiagonal`,
  `TwinPrimeConstant`, `WeylLawTarget`, `Fin5InnerProduct`, `GoldbachLocalWheel`,
  `WeylSymmetryPackage`, or Claude-owned Admissibility/Galois/Pentagonal files.

- 2026-08-02 — **Codex swarm #6 INTEGRATED / closed**. All six handles closed after
  integration or final audit. Landed pieces:
  - #35 overclaim firewall: `scripts/audit_dependency_firewall.py` +
    `docs/DEPENDENCY-FIREWALL.md` (`eafd7b7`, also carried in `aacaf27`). Current
    `--fail-on-high` mode exits cleanly: no HIGH direct citation from a `PROVED` entry to
    an open declaration; only LOW mixed-module warnings remain.
  - #36 registry consistency: `scripts/audit_registry_consistency.py` +
    `docs/REGISTRY-CONSISTENCY.md` (`d8ff917`, also carried in `aacaf27`). Current strict
    audit has `ERROR: 0`, no stale open entries, no duplicate registry names.
  - #39 paper theorem table: `scripts/gen_paper_theorem_table.py`,
    `paper/theorem_table.md`, `docs/PAPER-TABLE-GENERATION.md` (`5f9d32b`).
  - #11 local admissibility criterion scaffold: `AdmissibilityCriterionScaffold`
    (`3955765`) proves the finite `ν(q) < q` local criterion and the prime-local wrapper;
    no prime distribution theorem claimed.
  - #19 finite deviation-bound package: `EquidistributionDeviationBound` (`3a3afd9`)
    packages per-config/total/pair-count normalized finite deviations from explicit
    `PrimePairAsymptotic` + finite-window error-budget hypotheses; no HL/BV claim.
  - #28 xi functional equation bridge: `RiemannXiFunctionalEquation` (`72a4194`)
    uses Mathlib's `completedRiemannZeta_one_sub` to prove `riemannXi (1-s)=riemannXi s`
    and zero-set symmetry.
  Current shared registry after concurrent Claude/Grok landings through `0b7eec6`:
  1018 `PROVED`, 234 `DEFINITION`, 19 `CONDITIONAL`, 1 `CONJECTURE` over 1272 entries.
  Open-entry audit is clean by register discipline; the added `FranklinInvolution` and
  `WeylLawTarget` entries are honest conditional frontiers. Remaining local dirt observed:
  Aristotle's `aristotle/kato-bounded/KatoBounded.lean` plus noncanonical short-name
  duplicate attestations `FourierMultiplier.json` and `LocalWheel.json`; do not stage them.

- 2026-08-01 — **Claude swarm #7 on 39-move map** (804 baseline; AXLE @4.32 gate; new files only).
  Takes the UN-claimed closeable targets in lanes A/B/C/F — explicitly avoids Grok #6
  (#4 OddDistinct, #10 CosAlgInt, #12 AdmissibilityDiagonal, #15 TwinPrimeConstant, #25 WeylLawTarget,
  Fin5InnerProduct/GoldbachLocalWheel/WeylSymmetryPackage) and Codex Weyl lane (#20-27). Claims:
  - #1 `Brockian/FranklinInvolution.lean` — discharge the Franklin sign-reversing involution
    (makes PentagonalTheoremFranklin unconditional). Imports PentagonalPartition/PentagonalTheoremFranklin.
  - #3 `Brockian/RamanujanCongruence.lean` — p(5n+4) ≡ 0 (mod 5) (the Euler↔five headline).
  - #6 `Brockian/CyclotomicRealDegree.lean` — composite-n degree [ℚ(2cos 2π/n):ℚ]=φ(n)/2 (+ #8 which-n-quadratic).
  - #7 `Brockian/GaloisCyclicGroup.lean` — Gal(ℚ(2cos 2π/p)/ℚ) cyclic of order (p−1)/2.
  - #9 `Brockian/MetallicRealization.lean` — metallic-means spectral realization (extends MetallicFamily, import-only).
  - #11 `Brockian/AdmissibilityHLCriterion.lean` — HL criterion: admissible ⟺ ν(p)<p ∀p (imports Admissibility*).
  - #28 `Brockian/XiFunctionalEquation.lean` — ξ(s)=ξ(1−s) via Mathlib completedRiemannZeta (imports RiemannScaffold).
  Claude ALSO does #35 (overclaim-firewall CI invariant) + #36 (registry self-consistency audit) as tooling directly.
  Do not touch these files or Pentagonal*/Galois*/Admissibility*/MetallicFamily/RiemannScaffold internals (import only).
  Honesty: #1/#3/#6 may return honest reductions/partials; frontier (#16/#29/#30/#32) stay CONDITIONAL, never faked.

- 2026-08-02 — **Claude swarm #8: attack the CONDITIONALs** (AXLE-only; NO local lake build / #print axioms
  — that thrash-locked the 16GB machine; attest.py obtains axioms via AXLE). Focus = discharge/reduce
  the 19 CONDITIONAL + 1 CONJECTURE. Claude takes the ones it owns; leaves the Weyl conditionals
  (DeficiencyODE #20 WeakSolutionRegularity, FreeLaplacian2 #21 Plancherel, KatoUnbounded #22) to Codex,
  and the frontier (RH_of_BrockianSystem, goldbach_from_spectral_model, GoldbachCovarianceTransfer,
  WeylLawTarget) stay CONDITIONAL/CONJECTURE — never faked. Claims:
  - `Brockian/FranklinInvolutionProof.lean` — construct (∀ m, FranklinData m): the explicit sign-reversing
    involution on Nat.Partition.distincts (smallest-part s / top-diagonal t case split), discharging the 5
    Franklin CONDITIONALs → makes the Euler pentagonal number theorem UNCONDITIONAL. Imports
    FranklinInvolution/PentagonalTheoremFranklin/PentagonalPartition (extend by import only).
  - `Brockian/EquidistributionBVReduction.lean` — reduce `equidistribution_of_asymptotic` (rung=open) to a
    named Bombieri–Vinogradov-strength hypothesis (honest rung open→literature): prove every algebra/limit
    step, isolating the single cited analytic input. Imports Equidistribution (extend by import only).
  Do not touch FranklinInvolution/PentagonalTheoremFranklin/Equidistribution internals (import only).

- 2026-08-02 — **Codex swarm #7 launched: Weyl/Gate-1 conditionals + registry hygiene**.
  Baseline after concurrent landings through `5f2ea2a`: 1020 `PROVED`, 235 `DEFINITION`,
  23 `CONDITIONAL`, 1 `CONJECTURE` over 1279 entries. This swarm explicitly avoids Claude #8
  Franklin/equidistribution files and Grok finite-arithmetic files. Claims:
  - Archimedes (`019fc1fd-bfbb-7011-b987-bbdec72dac20`) —
    `Brockian/WeylWeakRegularityCore.lean`; target #20 weak-to-classical regularity core
    reductions. No edits to `WeylWeakRegularityScaffold.lean` or `DeficiencyODE` internals.
  - Plato (`019fc1fd-da35-78a0-bcb3-d7c9d786f6b3`) —
    `Brockian/WeylPlancherelScaffold.lean`; target #21 Plancherel/free-Laplacian Fourier
    input interface toward `FourierMultiplierInput`. No edits to existing `WeylFourier*`
    or `WeylFreeLaplacian*` files.
  - Laplace (`019fc1fd-f4b0-7443-a805-c779113d0edb`) —
    `Brockian/WeylKatoRellichScaffold.lean`; target #22 Kato-Rellich/resolvent transfer
    scaffold. No edits to `WeylKatoUnbounded.lean`, `WeylKatoRangeDensity.lean`, or
    Aristotle's Kato file.
  - Nash (`019fc1fe-0971-7613-b51a-257084a17593`) —
    `docs/REGISTRY-HYGIENE-QUEUE.md` and optionally `scripts/list_attestation_smells.py`;
    read-only report/helper for noncanonical duplicate attestations and root-import mismatches.
  AXLE @4.32 required for Lean files; Weyl files should attempt read-only @4.28 if cheap.
  Do not run long local `lake build`; previous agents observed heavy-import silent stalls.
  Import into `Brockian.lean` only after canonical attestation and explicit integration.

- 2026-08-02 — **Grok Tier-1 swarm**: Cos traces + singular series examples + Goldbach wheels + claim sync.
  New files only:
  - `Brockian/CosTraceNorm.lean` — Tr/Norm of 2cos(2π/p) for p=3,5,7 (+ hooks)
  - `Brockian/SingularSeriesMoreExamples.lean` — {0,4},{0,6} etc admissible + positivity
  - `Brockian/GoldbachWheelExtended.lean` — K_p for p=11,13 and multi-wheel products
  Observatory claim_map sync for Tier-1 + recent ships. AXLE @4.32 required. No RH/Franklin/Gate1 fakes.

- 2026-08-02 — **Aristotle racing the two dischargeable conditionals** (Harmonic API recovered).
  Submitted the SHARPENED residuals (self-contained flattened targets in `aristotle/{franklin,weak-regularity}/`):
  - Franklin involution `∀ m, FranklinMap m` (F2 already proved in FranklinInvolutionProof) → project `6436e21f-eb32-4f4f-abef-df18c9a71b04`. If Aristotle closes it: 5+ Franklin conditionals discharge, PST unconditional.
  - WeakSolutionRegularity (1D elliptic regularity, continuous V) → project `c400008b-5931-4ec5-9dc0-df7900be07eb`. If closed: DeficiencyODE Gate-1 conditionals discharge. (Codex's Weyl lane — coordinate on integration.)
  Our own AXLE-verified swarm keeps the retrievable path; Aristotle is a redundant stronger-prover race.
  NOTE: Harmonic download API has been flaky (old job c6a46c07 still 500s); results may need retry to pull.

- 2026-08-02 — **Franklin CONDITIONAL cleanup (hygiene)**. Unconditional PST is already
  PROVED as `Brockian.FranklinFixedPoint.pentagonalNumberTheorem` (no hyps; AXLE @4.32).
  Registry post-pass marks the six Franklin reduction lemmas `DISCHARGED` via
  `discharged_by: pentagonalNumberTheorem` — **no Franklin entry remains CONDITIONAL**.
  Remaining open CONDITIONALs are non-Franklin: equidistribution/BV, Goldbach spectral model,
  RH_of_BrockianSystem, DeficiencyODE/weak regularity, FreeLaplacian2 Fourier, KatoUnbounded
  transfer, SchrodingerMinimal ODE, WeylLawTarget counting (18 total). Documented in
  `PORT-QUEUE.md` RESOLVED (2026-08-02).

- 2026-08-02 — **Orphan re-attest pass**. `no_theater_lint` clean on all three.
  - `RiemannXiSymmetry` — re-attested `module_verified: true` (15 decls); imported in
    `Brockian.lean`; ships.
  - `WeylKatoNeumann` — re-attested `module_verified: true` (already imported/canonical
    `WeylKatoNeumann.json`); ships refresh.
  - `D5CharacterTable` — AXLE `module_verified: false` (`sorryAx` footprint in rotation/
    reflection character proofs under flatten); **not shipped** (lean file stays local WIP).
  Hygiene: removed failed short dup `FourierMultiplier.json` and non-canonical short
  `LocalWheel.json` / `KatoNeumann.json` (canonicals `WeylFourierMultiplier` /
  `GoldbachLocalWheel` / `WeylKatoNeumann` remain). Never stage `aristotle/kato-bounded`.

- 2026-08-02 — **CONDITIONAL ATTACK dispatch** (full plan: docs/CONDITIONAL-ATTACK-PLAN.md). Assignments:
  - **Codex (Weyl lane):** A1 `WeakSolutionRegularity` (1D elliptic regularity → discharges DeficiencyODE ×2 + SchrodingerMinimal), A4 Kato–Rellich `essentiallySelfAdjoint_perturb`. AXLE-gate each.
  - **Grok (reduce-only, do NOT fake):** C1 sharpen Hilbert–Pólya criterion (RH_of_BrockianSystem), C2 local SpectralModel structure (Goldbach), C3 circle-method major-arc as a NEW conditional (keep GoldbachCovarianceTransfer conjecture), C4 WeylLawTarget schemas → wire to a concrete confining candidate. These stay CONDITIONAL/CONJECTURE — never claim RH/Goldbach closed.
  - **Claude + Harmonic:** A3 free-Δ Plancherel (`freeLaplacian_essentiallySelfAdjoint_of_fourier`) — AXLE swarm + Harmonic submit; B1 equidistribution uniformity symmetry (`sing a = sing b`).
  - **Harmonic:** A1 weak-regularity job `c400008b` RUNNING (Claude monitoring for sorry-free close).
  Frontier honesty: RH/Goldbach/WeylLaw are open-problem-strength — dispatched as reduce/strengthen, not full proofs.

- 2026-08-02 — **Codex swarm #8 launched: prove both remaining Gate-1 attackables**.
  Baseline `55bb46f`: 1449 PROVED / 294 DEFINITION / 21 CONDITIONAL / 6 DISCHARGED /
  1 CONJECTURE; dirty paths are only Aristotle scratch plus pipeline/docs drafts. New-file
  claims only; never touch `aristotle/kato-bounded/KatoBounded.lean`, `aristotle/franklin/`,
  `aristotle/weak-regularity/`, or another agent's generated registry artifacts.
  - Weak primitive/local lane — `Brockian/WeylWeakPrimitiveLocal.lean`. Primary target:
    discharge or sharply reduce
    `Brockian.WeylWeakRegularityDischarge.WeakToPrimitiveRegularity` by a local
    primitive/fundamental-lemma route. Acceptable partials: a precise
    `DistributionalPrimitiveIdentity` / `WeakEqualsPrimitiveODE` predicate and proofs that it
    implies `WeakToPrimitiveRegularity`, plus uniqueness/normalization/a.e.-representative
    transport lemmas. No restating the conclusion under a vacuous name.
  - Kato resolvent lane — `Brockian/WeylKatoResolventConstruction.lean` (or a strictly
    narrower fresh Kato module if the API demands it). Primary target: construct the bounded
    right-resolvent/smallness hypotheses needed by `WeylKatoRellichTransfer` from the strongest
    already-verified ESA/free-Laplacian inputs. Acceptable partials: exact non-vacuous
    `RightResolvent` construction interfaces and theorem(s) composing them with
    `essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one`.
  AXLE @ lean-4.32.0 + `no_theater_lint` + axiom-clean required before any integration.
  If either lane cannot close, return the exact missing Mathlib API/theorem, not a weakened
  fake.

- 2026-08-02 — **Claude harvest+viz swarm** (infra/tooling, NOT Lean proofs — new areas, no collision).
  Implements the Mathlib+PhysLean harvest spec (docs/superpowers/specs/2026-08-02-mathlib-physlean-harvest-design.md).
  New areas claimed (do not touch): `scripts/harvest/`, `scripts/export_public_registry.py`, `torus/` (component package).
  - H1 EXTRACTOR: `scripts/harvest/extract_env.lean` + `scripts/harvest/run_extract.py` — Lean env-dump
    (Environment.constants + collectAxioms → NDJSON: name/kind/module/type/axioms/sorryFree). AXLE-typecheck the Lean tool.
  - H2 STORE+API: `scripts/harvest/schema.sql` (verified_declarations w/ source+verified_by facets),
    `scripts/harvest/ingest.py` (NDJSON→store, dedup vs Brockian-original, derive register+provenance),
    `scripts/harvest/search_api.py` (GET /api/verified/search). Extend honesty: split-by-source, never merge.
  - H3 PUBLIC+COMPONENT: `scripts/export_public_registry.py` (SANITIZED export — names/registers/statements/axioms,
    NO internal ledger_run/provenance notes), `torus/VerifiedClaim.tsx` + `torus/useVerified.ts` + manifest schema.
  Claude handles the torus.riemannlab.com Lovable deploy AFTER build (sanitized export only; honesty-firewall wiring).
