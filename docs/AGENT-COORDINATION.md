# Agent Coordination Queue

Current checkpoint: 2026-08-01, after `bcdfd5a`.

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
`Brockian/MetallicFamily.lean`. (Codex keeps D5Representation + WeylOperatorChoice; Grok/Aristotle
keep boundedv-continuous + the original WeylFreeLaplacian staging.)
