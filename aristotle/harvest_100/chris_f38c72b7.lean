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

import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The quantum CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁`, built from a CHSH tuple of
observables in a C⋆-algebra (e.g. the bounded operators on a Hilbert space), has norm
at most `2√2`.  This is Tsirelson's bound.

The order-theoretic core is Mathlib's `tsirelson_inequality`
(`Mathlib/Algebra/Star/CHSH.lean`), which gives
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1`.
Here we upgrade that to a bound on the C⋆-norm: applying it also to the CHSH tuple
`(A₀, A₁, -B₀, -B₁)` yields the matching lower bound, and a two-sided order bound on a
selfadjoint element gives a norm bound.
-/

namespace QC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A selfadjoint element of a unital C⋆-algebra squeezed between `-r` and `r`
has norm at most `r`. -/
theorem norm_le_of_neg_algebraMap_le_of_le_algebraMap {a : A} {r : ℝ} (hr : 0 ≤ r)
    (ha : IsSelfAdjoint a) (h₁ : -(algebraMap ℝ A r) ≤ a) (h₂ : a ≤ algebraMap ℝ A r) :
    ‖a‖ ≤ r := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · simpa [Subsingleton.elim a 0] using hr
  · have hub : ∀ x ∈ spectrum ℝ a, x ≤ r :=
      (le_algebraMap_iff_spectrum_le (a := a) (r := r) ha).mp h₂
    have hlb : ∀ x ∈ spectrum ℝ a, -r ≤ x :=
      (algebraMap_le_iff_le_spectrum (a := a) (r := -r) ha).mp (by simpa using h₁)
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := a) ha with h | h
    · exact hub _ h
    · have := hlb _ h
      linarith

omit [PartialOrder A] [StarOrderedRing A] in
/-- The CHSH operator built from a CHSH tuple is selfadjoint. -/
theorem isSelfAdjoint_chsh {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsSelfAdjoint (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) := by
  have h : ∀ x y : A, star x = x → star y = y → x * y = y * x → star (x * y) = x * y := by
    intro x y hx hy hxy
    rw [star_mul, hx, hy, ← hxy]
  unfold IsSelfAdjoint
  rw [star_sub, star_add, star_add,
    h A₀ B₀ T.A₀_sa T.B₀_sa T.A₀B₀_commutes,
    h A₀ B₁ T.A₀_sa T.B₁_sa T.A₀B₁_commutes,
    h A₁ B₀ T.A₁_sa T.B₀_sa T.A₁B₀_commutes,
    h A₁ B₁ T.A₁_sa T.B₁_sa T.A₁B₁_commutes]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Negating both of Bob's observables in a CHSH tuple gives another CHSH tuple. -/
theorem isCHSHTuple_neg_B {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsCHSHTuple A₀ A₁ (-B₀) (-B₁) where
  A₀_inv := T.A₀_inv
  A₁_inv := T.A₁_inv
  B₀_inv := by rw [neg_pow, T.B₀_inv]; simp
  B₁_inv := by rw [neg_pow, T.B₁_inv]; simp
  A₀_sa := T.A₀_sa
  A₁_sa := T.A₁_sa
  B₀_sa := by rw [star_neg, T.B₀_sa]
  B₁_sa := by rw [star_neg, T.B₁_sa]
  A₀B₀_commutes := by rw [mul_neg, neg_mul, T.A₀B₀_commutes]
  A₀B₁_commutes := by rw [mul_neg, neg_mul, T.A₀B₁_commutes]
  A₁B₀_commutes := by rw [mul_neg, neg_mul, T.A₁B₀_commutes]
  A₁B₁_commutes := by rw [mul_neg, neg_mul, T.A₁B₁_commutes]

/-- **Tsirelson's bound.**  For a CHSH tuple `A₀, A₁, B₀, B₁` of observables in a
C⋆-algebra (for instance, bounded operators on a Hilbert space), the CHSH operator
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has norm at most `2√2`. -/
theorem chsh_tsirelson (A₀ A₁ B₀ B₁ : A) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 := by
  have key : (Real.sqrt 2) ^ 3 • (1 : A) = algebraMap ℝ A (2 * Real.sqrt 2) := by
    rw [Algebra.algebraMap_eq_smul_one]
    congr 1
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hup : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ algebraMap ℝ A (2 * Real.sqrt 2) := by
    rw [← key]; exact tsirelson_inequality A₀ A₁ B₀ B₁ T
  have hlow' : A₀ * (-B₀) + A₀ * (-B₁) + A₁ * (-B₀) - A₁ * (-B₁)
      ≤ algebraMap ℝ A (2 * Real.sqrt 2) := by
    rw [← key]; exact tsirelson_inequality A₀ A₁ (-B₀) (-B₁) (isCHSHTuple_neg_B T)
  have hlow : -(algebraMap ℝ A (2 * Real.sqrt 2)) ≤ A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ := by
    have hneg : -(A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
        = A₀ * (-B₀) + A₀ * (-B₁) + A₁ * (-B₀) - A₁ * (-B₁) := by
      simp only [mul_neg]; abel
    exact neg_le.mp (hneg ▸ hlow')
  exact norm_le_of_neg_algebraMap_le_of_le_algebraMap
    (by positivity) (isSelfAdjoint_chsh T) hlow hup

/-- **Tsirelson's bound for bounded operators on a Hilbert space.**  If `A₀, A₁, B₀, B₁`
is a CHSH tuple of bounded operators on a complex Hilbert space `H` (each one selfadjoint
with square `1`, and Alice's observables commuting with Bob's), then the operator norm of
the CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` is at most `2√2`. -/
theorem chsh_tsirelson_operator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A₀ A₁ B₀ B₁ : H →L[ℂ] H) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_tsirelson A₀ A₁ B₀ B₁ T

end QC

