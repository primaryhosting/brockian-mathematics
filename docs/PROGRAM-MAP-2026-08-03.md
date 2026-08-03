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

After integrating Grok's final canonical wave, the root registry is:

| Register | Count |
|---|---:|
| PROVED | 10,348 |
| DEFINITION | 530 |
| CONJECTURE | 33 |
| CONDITIONAL | 21 |
| DISCHARGED | 6 |

No famous open conjecture was solved. The 33 conjectures are nullary `Prop`
containers marking open boundaries, not theorems.

## Depth-Adjusted Delta

Baseline: commit `a5ff22d`, where the bounded-continuous-potential Gate 1 chain
closed at `2,002 PROVED / 351 DEFINITION / 1 CONJECTURE / 21 CONDITIONAL /
6 DISCHARGED`.

The post-Gate-1 delta is `8,346 PROVED / 179 DEFINITION / 32 CONJECTURE` across
543 new root modules. Its composition is:

| Lane | PROVED | DEF | CONJECTURE | Meaning |
|---|---:|---:|---:|---|
| Even-gap singular-series instances | 6,090 | 0 | 0 | Generated applications of the general admissibility/local-factor theorems |
| Real-cyclotomic prime instances | 1,190 | 0 | 0 | Generated degree and integrality applications of the general real-subfield theorem |
| Goldbach `K2 * Kp` wheel instances | 774 | 129 | 0 | Generated exact finite local-factor identities; not Goldbach |
| Open-problem finite/structural modules | 277 | 49 | 32 | Concrete cases and necessary conditions with explicit open boundaries |
| Pentagon representation bridge | 15 | 1 | 0 | New conceptual symmetry and character-multiplicity results |

Thus 8,054 of 8,346 new PROVED entries are generated specializations of three
general theorem families. They are valid certificates, but the general theorem
is the mathematical payload. Future reports must show both raw and
depth-adjusted counts.

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

One elementary bridge remains: identify the packaged fixed-point-count function
`permCharacter` with the trace of the concrete `d5Pull` permutation
representation. The current file states this limitation explicitly.

### 3. Open-frontier certificates

Thirty-two open-problem modules now contribute 277 proved finite or structural
facts. Strong examples include the Sierpinski and Riesel covering certificates,
Erdos-Straus residue reductions, Lehmer necessary conditions, concrete
Carmichael/Brown/amicable instances, and elementary Collatz descent families.

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

## Integrity State

- All 12 modules in the final Grok wave have `module_verified: true` AXLE 4.32
  attestations, allowed axioms only, and zero no-theater lint findings.
- Registry freshness passes at 10,938 total entries.
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

1. **Confining operator:** construct and analyze `-d^2/dx^2 + x^2` as the next
   concrete unbounded candidate.
2. **Compact resolvent:** formalize the weighted Rellich compact embedding and
   derive discrete spectrum for the harmonic oscillator closure.
3. **RH correspondence:** no operator-spectrum to zeta-zero correspondence is
   known or formalized; this remains RH-strength.
4. **Goldbach/HL:** local factors and admissibility are proved, but global prime
   asymptotics remain conditional/open.
5. **Open-frontier conjectures:** all 33 conjecture containers remain open.

## Next Ownership Split

| Priority | Owner | Target |
|---|---|---|
| P0 | Codex | Finish and attest `WeylHarmonicOscillator`: concrete core, density, symmetry, confining package |
| P1 | Codex + Claude | Define the oscillator graph/form norm and isolate the weighted Rellich compact-embedding theorem |
| P2 | Claude | Prove `permCharacter` equals the trace/fixed-point character of concrete `d5Pull` |
| P3 | Integrator | Stop automatic range expansion; accept new generated corpus only when it tests a new general theorem |
| P4 | Integrator | Prepare Mathlib-quality extractions of the abstract Weyl/Cayley and Schwartz-core lemmas |

The program should now optimize for new general lemmas and closed conceptual
bridges, not raw registry growth.
