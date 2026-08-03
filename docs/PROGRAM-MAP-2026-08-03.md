# Brockian Program Map - 2026-08-03

## BLUF

The program made two different kinds of progress in the last overnight cycle:

1. **Conceptual progress:** Gate 1 is closed for the concrete one-dimensional
   Schwartz-core Schrodinger operator with continuous bounded real potential;
   the pentagon adjacency operator is now proved fully `D5`-equivariant and its
   golden eigenspace is connected to the golden character multiplicity.
2. **Certificate breadth:** Grok's corpus generator instantiated existing general
   theorems over thousands of finite cases. These are valid AXLE-verified Lean
   theorems, but they are specializations rather than thousands of independent
   mathematical discoveries.

After integrating Grok's final canonical wave and its final unitary-perfect
module, the root registry is:

| Register | Count |
|---|---:|
| PROVED | 10,568 |
| DEFINITION | 581 |
| CONJECTURE | 40 |
| CONDITIONAL | 20 |
| DISCHARGED | 7 |

No famous open conjecture was solved. The 40 conjectures are nullary `Prop`
containers marking open boundaries, not theorems.

The current continuation added the unconditional bounded Kato-Rellich theorem,
its concrete `-d^2+V` application, a correctly normalized spectral free
Laplacian, a reusable maximal-multiplication criterion, Kummer's theorem, and
Wolstenholme's theorem. It also discharged the historical Kato transfer
conditional, hence `CONDITIONAL 21 -> 20` and `DISCHARGED 6 -> 7`.

## Depth-Adjusted Delta

Baseline: commit `a5ff22d`, where the bounded-continuous-potential Gate 1 chain
closed at `2,002 PROVED / 351 DEFINITION / 1 CONJECTURE / 21 CONDITIONAL /
6 DISCHARGED`.

At checkpoint `100f976`, the post-Gate-1 delta was `8,351 PROVED / 181
DEFINITION / 33 CONJECTURE` across 544 new root modules. Its composition was:

| Lane | PROVED | DEF | CONJECTURE | Meaning |
|---|---:|---:|---:|---|
| Even-gap singular-series instances | 6,090 | 0 | 0 | Generated applications of the general admissibility/local-factor theorems |
| Real-cyclotomic prime instances | 1,190 | 0 | 0 | Generated degree and integrality applications of the general real-subfield theorem |
| Goldbach `K2 * Kp` wheel instances | 774 | 129 | 0 | Generated exact finite local-factor identities; not Goldbach |
| Open-problem finite/structural modules | 282 | 51 | 33 | Concrete cases and necessary conditions with explicit open boundaries |
| Pentagon representation bridge | 15 | 1 | 0 | New conceptual symmetry and character-multiplicity results |

Thus 8,054 of 8,351 new PROVED entries are generated specializations of three
general theorem families. They are valid certificates, but the general theorem
is the mathematical payload. Future reports must show both raw and
depth-adjusted counts.

Since that checkpoint, eight additional root modules added `52 PROVED / 20
DEFINITION / 4 CONJECTURE`. The operator/representation campaign in this report
accounts for `24 PROVED / 13 DEFINITION / 0 CONJECTURE`; the remaining `28 / 7 /
4` are concurrent finite open-frontier additions. This split prevents those two
kinds of progress from being conflated.

## What Closed

### 1. Bounded-potential Gate 1

The concrete operator `-d^2/dx^2 + V` on the Schwartz core of `L2(R)` is
essentially self-adjoint for continuous bounded real `V`. The verified chain now
includes the distributional weak equation, Fourier-energy uniqueness, closure
equal to adjoint, self-adjoint closure, surjective unit shifts, and bounded unit
resolvents.

This is a real operator-theory result. It does not provide a Hilbert-Polya
spectrum, and a bounded decaying potential has the wrong spectral shape for RH.

### 2. Pentagon symmetry mechanism

`PentagonEquivariance` proves that adjacency commutes with the full dihedral
action and that the golden eigenspace is a two-dimensional `D5`-invariant
subspace. `PentagonCharacterMultiplicity` matches its dimension with the golden
character value and proves multiplicity one in the packaged permutation
character.

`PentagonTraceBridge` now closes the remaining elementary bridge: the packaged
fixed-point-count function `permCharacter` is the trace of the concrete
permutation matrix implementing `d5Pull`.

### 3. Open-frontier certificates

Thirty-six open-problem modules now contribute 310 proved finite or structural
facts. Strong examples include the Sierpinski and Riesel covering certificates,
Erdos-Straus residue reductions, Lehmer necessary conditions, concrete
Carmichael/Brown/amicable instances, elementary Collatz descent families, and
the verified unitary-perfect cases `6`, `60`, and `90` (with `28` excluded).

These modules improve the formal map around open problems. Their conjecture
containers remain open by construction.

### 4. Final Grok range integration

The final verified wave extends:

- even-pair admissibility, local factors, and finite singular-series positivity
  through gap `2200`;
- real-cyclotomic degree/integrality instances through prime `1093`;
- exact two-prime Goldbach-wheel identities through `K2 * K797`.

These are local/finite statements. They do not prove Hardy-Littlewood
asymptotics, twin-prime infinitude, or Goldbach.

### 5. Confining-operator campaign

Five AXLE-green modules now add the next general operator layer:

- `WeylHarmonicOscillator`: the concrete Schwartz-core `-d^2+x^2` `LinearPMap`,
  with exact action, dense domain, symmetry, and confining shape;
- `WeylWeightedRellich`: compact-embedding factorization implies compact
  resolvent, including compact closure of closed-ball images;
- `WeylOscillatorDiscrete`: the Fredholm consequence that every nonzero
  compact-resolvent spectral value is an eigenvalue with finite-dimensional
  eigenspace;
- `WeylUpstream`: deficiency-trivial essential self-adjointness is equivalent
  to self-adjointness of the graph closure for a dense symmetric core;
- `PentagonTraceBridge`: `permCharacter` is exactly the trace of the concrete
  `d5PermutationMatrix`, closing the fixed-point/trace bridge.

The oscillator specialization still assumes oscillator ESA and the actual
weighted Rellich compact embedding. Those two analytic inputs are not disguised
as proved results.

### 6. Bounded Kato-Rellich and normalized free Laplacian

`WeylKatoRellich` now proves that a bounded self-adjoint perturbation preserves
essential self-adjointness of a densely defined symmetric core. Its proof uses
the graph homeomorphism `(x,y) |-> (x,Bx+y)`, closure compatibility, and a direct
adjoint-domain computation. `WeylKatoConcreteApplication` applies it to the
exact Schwartz-core identity for `-d^2+V`.

`WeylFreeLaplacianCorrected` fixes a normalization error caught during the
Harmonic audit: Mathlib's Fourier transform sends `-f''` to
`4*pi^2*xi^2 * Fourier(f)`. The corresponding maximal multiplier and its
Fourier conjugate are ESA. The final Schwartz-core restriction theorem remains
in progress and is not claimed.

## Integrity State

- All 12 modules in the final range wave and the final `UnitaryPerfect` module
  have `module_verified: true` AXLE 4.32 attestations and allowed axioms only;
  the range wave has zero no-theater lint findings.
- Registry freshness passes at 11,022 total entries.
- Registry open-entry consistency has zero errors after fixing source paths to
  derive from canonical attestation stems rather than namespace tails.
- One noncanonical untracked `BrocardGap.json` duplicates the canonical
  `BrocardGapConjecture.json`. It is excluded by the root-import filter and must
  not be committed.
- The dependency firewall is a conservative metadata audit, not a Lean
  dependency graph. It now reports many warnings because honest provenance text
  names the conjecture that each finite theorem does not solve. Those warnings
  are not proof dependencies and must not be reported as theorem failures.

## What Remains Open

1. **Oscillator ESA:** prove essential self-adjointness of the concrete
   Schwartz-core `-d^2/dx^2 + x^2` operator.
2. **Weighted Rellich:** construct the oscillator energy/graph space and prove
   its concrete inclusion into `L2(R)` is compact; all downstream compactness
   and finite-multiplicity consequences are now proved.
3. **Unbounded spectral mapping:** relate the closure spectrum to either compact
   unit resolvent and add eigenvalue isolation/zero-only accumulation.
4. **RH correspondence:** no operator-spectrum to zeta-zero correspondence is
   known or formalized; this remains RH-strength.
5. **Goldbach/HL:** local factors and admissibility are proved, but global prime
   asymptotics remain conditional/open.
6. **Open-frontier conjectures:** all 40 conjecture containers remain open.

## Next Ownership Split

| Priority | Owner | Target |
|---|---|---|
| P0 | Codex + Claude | Prove oscillator ESA, preferably through Hermite/Fourier energy or a semibounded-core theorem |
| P1 | Codex + Claude | Construct the oscillator graph/form space and prove the actual weighted Rellich compact embedding |
| P2 | Codex | Add unbounded spectral mapping and isolation once compact resolvent is instantiated |
| P3 | Integrator | Stop automatic range expansion; accept new generated corpus only when it tests a new general theorem |
| P4 | Integrator | Turn `WeylUpstream` into a minimal-import Mathlib PR and upstream the compact-eigenspace lemma |

The program should now optimize for new general lemmas and closed conceptual
bridges, not raw registry growth.
