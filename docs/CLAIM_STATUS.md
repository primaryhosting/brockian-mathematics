# Brockian claim-status table

> Generated from `ledger/claims/claims.json`. This is an evidence and claim-boundary table, not a substitute for a Lean artifact or independent rerun.

## Status legend

- **Exact**: finite or algebraic statement as formulated.
- **Standard**: established mathematics; the Brockian contribution is formalization, integration, or certified reuse.
- **Conditional / Conjectural**: carries named hypothesis debt in the theorem statement; kernel axioms do not display those assumptions.
- **V4** requires a pinned local build, source/signature hashes, and raw axiom report. **V5** also requires independent reproduction. No V0–V3 record may be described as final verified.

## Claims

| ID | Claim | Status / kind | Verification | Lean declaration | Explicit hypothesis debt |
|---|---|---|---|---|---|
| BM-LOCAL-001-v1.0 | Pair admissibility local factor | Standard / Formalization | V3 | Brockian.Admissibility.universal_admissibility_count | None |
| BM-LOCAL-002-v1.0 | Goldbach local count and centered spike | Exact / Formalization | V3 | Brockian.GoldbachComb.gCount_eq | None |
| BM-CYCLO-001-v1.0 | Cycle-spectrum rigidity of the golden value | Standard / Formalization | V3 | Brockian.Spectral.golden_unique_to_five | None |
| BM-COND-001-v1.0 | Fixed-modulus prime-pairs-in-AP hypothesis | Conjectural / Hypothesis | V0 | Brockian.Hypothesis.PrimePairsInAPAtModulus | `Brockian.Hypothesis.PrimePairsInAPAtModulus` — A single fixed modulus q and fixed gap g. |
| BM-COND-002-v1.0 | Uniform prime-pairs-in-AP hypothesis | Conjectural / Hypothesis | V0 | Brockian.Hypothesis.UniformPrimePairsInAP | `Brockian.Hypothesis.UniformPrimePairsInAP` — Exactly q <= Q(X), where Q is an explicit argument; no unnamed level of distribution is permitted. |

## Evidence records

### BM-LOCAL-001-v1.0 — Pair admissibility local factor

**Statement.** For a nonzero gap g modulo q, the two forbidden start residues are 0 and -g, so the standard local obstruction count for H={0,g} is nu_q(H)=2 and the admissible-start count is q-2.

**Scope.** Finite residue arithmetic over ZMod q with [NeZero q] and g nonzero modulo q; this is the k=2 Hardy-Littlewood local factor, not a global prime-distribution theorem.

**Artifact.** `Brockian.Admissibility.universal_admissibility_count` · `Brockian/Admissibility.lean` · local build: **pending** · independent check: **pass**.

**Prior art / boundary.** Classical Hardy-Littlewood singular-series local obstruction factor nu_q(H). The contribution claimed here is formalization and reusable local-sieve infrastructure, not novelty in analytic number theory.

**Failure condition.** A counterexample to the finite cardinality identity, a source/signature mismatch, or a failed rebuild invalidates this record.

**Approved public wording.** Machine-checked formalization of the standard pair-admissibility local factor; no new prime-distribution result is claimed.

### BM-LOCAL-002-v1.0 — Goldbach local count and centered spike

**Statement.** For prime p, the number of ordered pairs of nonzero residues summing to c is p-1 when c=0 and p-2 otherwise; the centered form is the finite spike 1_{c=0}-1/p.

**Scope.** Finite arithmetic in ZMod p. It does not transfer a local covariance kernel to a global Goldbach correlation.

**Artifact.** `Brockian.GoldbachComb.gCount_eq` · `Brockian/GoldbachComb.lean` · local build: **pending** · independent check: **pending**.

**Prior art / boundary.** Elementary finite-field residue count. The global Goldbach-transfer interpretation remains outside this exact finite theorem.

**Failure condition.** A failed finite-field count, mismatched theorem statement, or unsatisfied proof gate invalidates the claim.

**Approved public wording.** Exact finite local count formalized in Lean; no global Goldbach consequence is claimed.

### BM-CYCLO-001-v1.0 — Cycle-spectrum rigidity of the golden value

**Statement.** For prime p, the occurrence of phi-1=2 cos(2 pi / 5) in the stated cycle-spectrum model forces p=5. The current Lean proof uses the exact cosine relation; the paper must also state the short conductor-5 cyclotomic explanation.

**Scope.** Cycle-spectrum rigidity. It does not imply a special global law for prime distribution modulo 5.

**Artifact.** `Brockian.Spectral.golden_unique_to_five` · `Brockian/Spectral.lean` · local build: **pending** · independent check: **pending**.

**Prior art / boundary.** Elementary cosine/cyclotomic rigidity; for exposition, Q(sqrt(5)) has conductor 5. The scientific value is a machine-checked cycle-spectrum rigidity statement, not numerological privilege for five.

**Failure condition.** A mismatch between the formal spectrum definition and the stated cyclotomic implication, or failure of the verified proof artifact, invalidates the claim.

**Approved public wording.** Machine-checked rigidity for a cycle-spectrum value; no prime-distribution consequence is claimed.

### BM-COND-001-v1.0 — Fixed-modulus prime-pairs-in-AP hypothesis

**Statement.** For fixed q and gap g, real prime-pair counts in each admissible residue class admit a named Hardy-Littlewood-style main term with lower-order error.

**Scope.** Fixed modulus q only. This record deliberately makes no uniformity-in-q claim.

**Artifact.** `Brockian.Hypothesis.PrimePairsInAPAtModulus` · `Brockian/Hypothesis/PrimePairsInAP.lean` · local build: **pending** · independent check: **pending**.

**Prior art / boundary.** Hardy-Littlewood prime-pair conjectural framework refined to a fixed arithmetic progression. Conditional theorems must carry this proposition as an explicit argument.

**Failure condition.** A counterexample to the stated asymptotic or any attempt to provide an implicit/global instance without evidence invalidates the use of this hypothesis.

**Approved public wording.** Open hypothesis for a fixed modulus; it is not a theorem and does not prove equidistribution.

### BM-COND-002-v1.0 — Uniform prime-pairs-in-AP hypothesis

**Statement.** For a fixed gap g and an explicitly supplied modulus range Q(X), the per-class prime-pair asymptotic holds with an error term uniform for q less than or equal to Q(X).

**Scope.** The strength is determined by the supplied range Q; examples such as logarithmic ranges and power ranges must be named in every downstream theorem.

**Artifact.** `Brockian.Hypothesis.UniformPrimePairsInAP` · `Brockian/Hypothesis/PrimePairsInAP.lean` · local build: **pending** · independent check: **pending**.

**Prior art / boundary.** Uniform Hardy-Littlewood-type prime-pair asymptotics in arithmetic progressions. This is the only hypothesis name to use for results that consume a q-range.

**Failure condition.** Failure in the named range, ambiguity about Q, or use of a fixed-q result as though it were uniform invalidates the claim.

**Approved public wording.** Open uniformity hypothesis with an explicit modulus range; it is not implied by Bombieri-Vinogradov.
