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

lemma sum_range_two_mul_of_odd_eq_zero {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)
    (hodd : ∀ w, w % 2 = 1 → f w = 0) :
    ∑ w ∈ range (2 * n + 1), f w = ∑ i ∈ range (n + 1), f (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
    have h2 : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      hodd (2 * n + 1) (by omega), h2, add_zero, Finset.sum_range_succ,
      Finset.sum_range_succ]

/-- **The Riemann hypothesis for varieties over finite fields (Weil conjectures,
proved by Deligne), base case: projective space.**

For every `q` and `n`, the family of Frobenius eigenvalues `projFrobEigenvalues q n`
computes the point counts `#P^n(F_{q^m})` through the Lefschetz trace formula, and it
satisfies the Weil Riemann hypothesis: each eigenvalue occurring in cohomological degree
`w` has absolute value exactly `q ^ (w / 2)`. -/
