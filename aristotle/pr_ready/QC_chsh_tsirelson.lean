/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Statement: The quantum CHSH operator has operator norm ≤ 2√2 (Tsirelson's bound).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QC

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, a self-adjoint element `a` bounded above by `r` and below by `-r`
(in the C⋆-order) has norm at most `r`. -/
theorem norm_le_of_neg_le_of_le {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : a ≤ algebraMap ℝ A r) (h₂ : -a ≤ algebraMap ℝ A r) : ‖a‖ ≤ r := by
  obtain (hsub | hnt) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim a 0] using hr
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
    · exact (le_algebraMap_iff_spectrum_le (a := a) ha).mp h₁ ‖a‖ h
    · have hmem : ‖a‖ ∈ spectrum ℝ (-a) := by
        rw [← spectrum.neg_eq]
        simpa using h
      exact (le_algebraMap_iff_spectrum_le (a := -a) ha.neg).mp h₂ ‖a‖ hmem

/-- The `ℝ`-star-module structure on a C⋆-algebra, obtained by restricting scalars from `ℂ`. -/
instance : StarModule ℝ A where
  star_smul r a := by
    rw [show (star r : ℝ) = r from rfl, ← algebraMap_smul ℂ r a,
      ← algebraMap_smul ℂ r (star a), star_smul]
    simp

end CStar

/-- The negation of the first pair of observables of a CHSH tuple is again a CHSH tuple. -/
theorem isCHSHTuple_neg {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) : IsCHSHTuple (-A₀) (-A₁) B₀ B₁ where
  A₀_inv := by simpa using T.A₀_inv
  A₁_inv := by simpa using T.A₁_inv
  B₀_inv := T.B₀_inv
  B₁_inv := T.B₁_inv
  A₀_sa := by simp [T.A₀_sa]
  A₁_sa := by simp [T.A₁_sa]
  B₀_sa := T.B₀_sa
  B₁_sa := T.B₁_sa
  A₀B₀_commutes := by simp [T.A₀B₀_commutes]
  A₀B₁_commutes := by simp [T.A₀B₁_commutes]
  A₁B₀_commutes := by simp [T.A₁B₀_commutes]
  A₁B₁_commutes := by simp [T.A₁B₁_commutes]

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
theorem isSelfAdjoint_chsh {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsSelfAdjoint (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) := by
  unfold IsSelfAdjoint
  simp only [star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

/-- **Tsirelson's bound.** For a CHSH tuple `(A₀, A₁, B₀, B₁)` in a unital C⋆-algebra
(four ±1-valued observables, the `Aᵢ` commuting with the `Bⱼ`), the CHSH operator
`A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` has operator norm at most `2√2`. -/
theorem chsh_tsirelson {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (A₀ A₁ B₀ B₁ : A) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * √2 := by
  have hsq : (√2) ^ 3 = 2 * √2 := by
    have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [pow_succ, h2]
  have hbound : (√2) ^ 3 • (1 : A) = algebraMap ℝ A (2 * √2) := by
    rw [← hsq, Algebra.algebraMap_eq_smul_one]
  refine norm_le_of_neg_le_of_le (isSelfAdjoint_chsh T) (by positivity) ?_ ?_
  · rw [← hbound]
    exact tsirelson_inequality A₀ A₁ B₀ B₁ T
  · have := tsirelson_inequality (-A₀) (-A₁) B₀ B₁ (isCHSHTuple_neg T)
    rw [← hbound]
    calc -(A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
        = (-A₀) * B₀ + (-A₀) * B₁ + (-A₁) * B₀ - (-A₁) * B₁ := by
          simp only [neg_mul]; abel
      _ ≤ (√2) ^ 3 • (1 : A) := this

/-- Sanity check: the hypotheses of `QC.chsh_tsirelson` are satisfiable, e.g. by the C⋆-algebra
of bounded operators on a finite-dimensional complex Hilbert space, with the trivial CHSH tuple. -/
example :
    ‖(1 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) * 1 + 1 * 1 + 1 * 1 - 1 * 1‖
      ≤ 2 * √2 :=
  chsh_tsirelson 1 1 1 1
    { A₀_inv := one_pow 2, A₁_inv := one_pow 2, B₀_inv := one_pow 2, B₁_inv := one_pow 2,
      A₀_sa := star_one _, A₁_sa := star_one _, B₀_sa := star_one _, B₁_sa := star_one _,
      A₀B₀_commutes := rfl, A₀B₁_commutes := rfl, A₁B₀_commutes := rfl, A₁B₁_commutes := rfl }

end QC

