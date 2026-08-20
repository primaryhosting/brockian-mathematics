/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

Mathlib (as of the pinned commit) contains no development of étale cohomology, Weil
cohomology theories, or zeta functions of varieties over finite fields, so no existing

def projSpacePointCount (q n m : ℕ) : ℕ := ∑ i ∈ range (n + 1), q ^ (i * m)

/-- The multiset of geometric Frobenius eigenvalues on the `w`-th cohomology group of
projective `n`-space over `F_q`: the single eigenvalue `q ^ (w / 2)` when `w = 2 i` with
`i ≤ n`, and nothing otherwise. -/
