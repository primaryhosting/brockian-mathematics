import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped RealInnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, a self-adjoint element sandwiched between `-r` and `r`
(as multiples of the unit) has norm at most `r`. -/
theorem norm_le_of_neg_algebraMap_le_of_le_algebraMap
    {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : algebraMap ℝ A (-r) ≤ a) (h₂ : a ≤ algebraMap ℝ A r) : ‖a‖ ≤ r := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim a 0] using hr
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
    · exact (le_algebraMap_iff_spectrum_le (R := ℝ) ha).mp h₂ _ h
    · have := (algebraMap_le_iff_le_spectrum (R := ℝ) ha).mp h₁ _ h
      linarith

/-- Negating both of the `B` observables of a CHSH tuple again yields a CHSH tuple. -/
theorem IsCHSHTuple.neg_B {a₀ a₁ b₀ b₁ : A} (T : IsCHSHTuple a₀ a₁ b₀ b₁) :
    IsCHSHTuple a₀ a₁ (-b₀) (-b₁) where
  A₀_inv := T.A₀_inv
  A₁_inv := T.A₁_inv
  B₀_inv := by simpa using T.B₀_inv
  B₁_inv := by simpa using T.B₁_inv
  A₀_sa := T.A₀_sa
  A₁_sa := T.A₁_sa
  B₀_sa := by simp [T.B₀_sa]
  B₁_sa := by simp [T.B₁_sa]
  A₀B₀_commutes := by simp [T.A₀B₀_commutes]
  A₀B₁_commutes := by simp [T.A₀B₁_commutes]
  A₁B₀_commutes := by simp [T.A₁B₀_commutes]
  A₁B₁_commutes := by simp [T.A₁B₁_commutes]

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
theorem isSelfAdjoint_chsh {a₀ a₁ b₀ b₁ : A} (T : IsCHSHTuple a₀ a₁ b₀ b₁) :
    IsSelfAdjoint (a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁) := by
  have h : ∀ x y : A, star x = x → star y = y → x * y = y * x → star (x * y) = x * y := by
    intro x y hx hy hxy
    rw [star_mul, hx, hy, ← hxy]
  simp only [IsSelfAdjoint, star_sub, star_add,
    h _ _ T.A₀_sa T.B₀_sa T.A₀B₀_commutes, h _ _ T.A₀_sa T.B₁_sa T.A₀B₁_commutes,
    h _ _ T.A₁_sa T.B₀_sa T.A₁B₀_commutes, h _ _ T.A₁_sa T.B₁_sa T.A₁B₁_commutes]

/-- **Tsirelson's bound**: in a unital C⋆-algebra, the CHSH operator
`A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` associated with a CHSH tuple (four self-adjoint involutions,
the `Aᵢ` commuting with the `Bⱼ`) has operator norm at most `2√2`. -/
theorem chsh_tsirelson (a₀ a₁ b₀ b₁ : A) (T : IsCHSHTuple a₀ a₁ b₀ b₁) :
    ‖a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁‖ ≤ 2 * Real.sqrt 2 := by
  have hsq : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h2]
  have hmap : ∀ r : ℝ, r • (1 : A) = algebraMap ℝ A r := fun r =>
    (Algebra.algebraMap_eq_smul_one r).symm
  -- upper bound
  have hub : a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁ ≤ algebraMap ℝ A (2 * Real.sqrt 2) := by
    have := tsirelson_inequality a₀ a₁ b₀ b₁ T
    rwa [hsq, hmap] at this
  -- lower bound, via the CHSH tuple with negated `B` observables
  have hlb : algebraMap ℝ A (-(2 * Real.sqrt 2)) ≤ a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁ := by
    have h := tsirelson_inequality a₀ a₁ (-b₀) (-b₁) T.neg_B
    rw [hsq, hmap] at h
    have h' : -(a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁) ≤ algebraMap ℝ A (2 * Real.sqrt 2) := by
      convert h using 1
      ring
    rw [map_neg]
    exact neg_le.mp h'
  exact norm_le_of_neg_algebraMap_le_of_le_algebraMap (isSelfAdjoint_chsh T)
    (by positivity) hlb hub

end QC

