# Aristotle top-three proof review — 2026-08-11

**Register outcome:** all three are **PARTIAL** pending source import and independent verification.

An Aristotle completion email is evidence that a proof-generation run finished. It is not the repository's `PROVED` certificate. The source bundles are not represented in open PR #2, and no target-named source file was found on `main` or either open Aristotle branch.

## Intake result

| Rank | Target | Aristotle claim | Repository state | Novelty assessment |
|---|---|---|---|---|
| 1 | `Math2.kahn_kalai` | Park–Pham theorem, explicit `K = 648 / log 2`; six-file Lean development; standard axiom set | source absent; no independent build/AXLE run | **Strong Lean novelty candidate.** Public Lean files located during the audit only state/scaffold related Kahn–Kalai claims and contain `sorry`. |
| 2 | `CS.hilbert10_undecidable` | full DPR/MRDP chain, H10 noncomputability over naturals and integers; standard axiom set | source absent; no independent build/AXLE run | **Likely novel in Lean, not novel across proof assistants.** A full Coq mechanization of MRDP/H10 was published in 2019. |
| 3 | `CS.blum_speedup` | arbitrary Blum measure and computable speedup factor; cofinite improvement; padding and step-measure corollaries | source absent; no independent build/AXLE run | **Strong Lean novelty candidate.** No public Lean proof was located in the limited identifier/topic search. |

The three targets are distinct; no admin/chris duplicate occurs within this shortlist.

## Checks completed

- Read the newest completion message for each target and recorded its UTC completion time.
- Compared target identifiers against `main`, the two open Aristotle branches, and open PR #2's proof inventory.
- Confirmed that the repository's ledger derivation maps a claimed `proved` attempt without independent AXLE verification to `PARTIAL`.
- Ran public GitHub identifier/topic searches for the target names and distinctive helper names.
- Compared each statement at a high level with the original mathematical theorem and known formalization landscape.

## Checks still required before promotion

### 1. `Math2.kahn_kalai`

1. Import every source file (`Weights`, `Basic`, `Fragments`, `KeyLemma`, `Iteration`, `Main`) without rewriting the proof.
2. Confirm the exact definitions of `mu`, `IsUp`, `pThreshold`, `qThreshold`, covers, and `ell` agree with Park–Pham.
3. Test empty/full families and every `sSup` boundedness/nonemptiness dependency; rule out a vacuous threshold definition.
4. Check that the explicit constant is positive and that the theorem proves one universal `K`.
5. Run the pinned `lake build`, no-placeholder scan, `#print axioms`, and independent AXLE attestation.

Public comparison: [Park–Pham theorem](https://authors.library.caltech.edu/records/2d31p-cjn16); [existing Lean statement-only scaffold](https://github.com/mdnestor/MiscLean/blob/bd150bcd568b3a80dee1f6465ae4b1ac7feb40a7/MiscLean/kahn_kalai.lean).

### 2. `CS.hilbert10_undecidable`

1. Verify the exact theorem type expresses undecidability/noncomputability of Diophantine solvability, rather than merely packaging a pre-assumed MRDP statement.
2. Audit the halting-set enumeration and noncomputability proof for circular imports.
3. Audit pairing, beta coding, bounded universal closure, primitive-recursive Diophantine graphs, and the conversion to `MvPolynomial`.
4. Check coercions and quantifier domains in both the natural-witness and integer-witness versions, including the four-square substitution.
5. Run the pinned build, placeholder scan, axiom probe, and independent AXLE attestation.

Landscape comparison: [full H10/MRDP in Coq](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2019.27); [Mathlib's Matiyasevic/Pell component](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PellMatiyasevic.html).

### 3. `CS.blum_speedup`

1. Inspect the exact `CS.BlumMeasure` axioms and prove that the cost domain is exactly the halting domain.
2. Inspect the type and assumptions of the speedup factor `r`. A bare computable `r` does not by itself justify the prose conclusion “no fastest algorithm”; the relevant strict-growth choice/corollary must be explicit.
3. Confirm “almost every input” is a genuine cofinite condition and that both programs compute the same total function.
4. Audit the fixed-point/recursion-theorem construction, padding, totality, and diagonalization for hidden assumptions.
5. Run the pinned build, placeholder scan, axiom probe, and independent AXLE attestation.

Original result: [Blum, 1967](https://doi.org/10.1145/321386.321395).

## Promotion rule

Only after the source bundle and verifier output are committed should an attempt be upgraded with `lean_axle_verified = true` and clean axioms. Until then, the generated register must remain `PARTIAL`, and novelty wording must remain “candidate” or “likely.”
