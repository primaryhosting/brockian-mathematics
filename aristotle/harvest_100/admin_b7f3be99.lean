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
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Tsirelson's bound for the CHSH operator in a C*-algebra

Given a CHSH tuple `(A₀, A₁, B₀, B₁)` in a unital C*-algebra (four self-adjoint
involutions such that the `Aᵢ` commute with the `Bⱼ`), the CHSH operator

`C = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`

satisfies `‖C‖ ≤ 2 * √2`.

The proof is the classical one: `C` is self-adjoint and
`C * C = 4 - [A₀, A₁] * [B₀, B₁]`, where each commutator has norm at most `2`.
Hence `‖C‖ ^ 2 = ‖C * C‖ ≤ 4 + 4 = 8` by the C*-identity.
-/

namespace QC

section Algebra

variable {A : Type*} [Ring A]

/-- The square of the CHSH operator equals `4 - [A₀, A₁] * [B₀, B₁]`. -/
theorem chsh_sq_eq {A₀ A₁ B₀ B₁ : A}
    (hA0 : A₀ * A₀ = 1) (hA1 : A₁ * A₁ = 1) (hB0 : B₀ * B₀ = 1) (hB1 : B₁ * B₁ = 1)
    (c00 : A₀ * B₀ = B₀ * A₀) (c01 : A₀ * B₁ = B₁ * A₀)
    (c10 : A₁ * B₀ = B₀ * A₁) (c11 : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  have s00 : ∀ x : A, B₀ * (A₀ * x) = A₀ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← c00, mul_assoc]
  have s01 : ∀ x : A, B₁ * (A₀ * x) = A₀ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← c01, mul_assoc]
  have s10 : ∀ x : A, B₀ * (A₁ * x) = A₁ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← c10, mul_assoc]
  have s11 : ∀ x : A, B₁ * (A₁ * x) = A₁ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← c11, mul_assoc]
  have q0 : ∀ x : A, A₀ * (A₀ * x) = x := by intro x; rw [← mul_assoc, hA0, one_mul]
  have q1 : ∀ x : A, A₁ * (A₁ * x) = x := by intro x; rw [← mul_assoc, hA1, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    s00, s01, s10, s11, q0, q1, hA0, hA1, hB0, hB1, mul_one]
  abel_nf
  simp
  abel

end Algebra

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [NormOneClass A]

/-- A self-adjoint involution in a unital C*-algebra has norm `1`. -/
theorem norm_eq_one_of_sa_involution {a : A} (ha : star a = a) (h : a * a = 1) : ‖a‖ = 1 := by
  have h2 : ‖a‖ * ‖a‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self (x := a), ha, h, norm_one]
  nlinarith [norm_nonneg a]

/-- The commutator of two self-adjoint involutions has norm at most `2`. -/
theorem norm_commutator_le_two {a b : A} (ha : star a = a) (hb : star b = b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) : ‖a * b - b * a‖ ≤ 2 := by
  have hna : ‖a‖ = 1 := norm_eq_one_of_sa_involution ha ha2
  have hnb : ‖b‖ = 1 := norm_eq_one_of_sa_involution hb hb2
  calc ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := by gcongr <;> exact norm_mul_le _ _
    _ = 2 := by rw [hna, hnb]; norm_num

/-- **Tsirelson's bound**: in a unital C*-algebra, the CHSH operator built from a CHSH tuple
`(A₀, A₁, B₀, B₁)` (self-adjoint involutions, with the `Aᵢ` commuting with the `Bⱼ`) has
operator norm at most `2 * √2`. -/
theorem chsh_tsirelson {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * √2 := by
  have hA0 : A₀ * A₀ = 1 := by have := T.A₀_inv; rwa [sq] at this
  have hA1 : A₁ * A₁ = 1 := by have := T.A₁_inv; rwa [sq] at this
  have hB0 : B₀ * B₀ = 1 := by have := T.B₀_inv; rwa [sq] at this
  have hB1 : B₁ * B₁ = 1 := by have := T.B₁_inv; rwa [sq] at this
  set C : A := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ with hC
  -- `C` is self-adjoint
  have hCsa : star C = C := by
    simp only [hC, star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
      ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
  -- the square of `C`
  have hsq : C * C = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) :=
    chsh_sq_eq hA0 hA1 hB0 hB1 T.A₀B₀_commutes T.A₀B₁_commutes T.A₁B₀_commutes T.A₁B₁_commutes
  have hcA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 :=
    norm_commutator_le_two T.A₀_sa T.A₁_sa hA0 hA1
  have hcB : ‖B₀ * B₁ - B₁ * B₀‖ ≤ 2 :=
    norm_commutator_le_two T.B₀_sa T.B₁_sa hB0 hB1
  have hfour : ‖(4 : A)‖ ≤ 4 := by
    have : (4 : A) = 1 + 1 + 1 + 1 := by norm_num
    rw [this]
    calc ‖(1 : A) + 1 + 1 + 1‖ ≤ ‖(1 : A) + 1 + 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ (‖(1 : A) + 1‖ + ‖(1 : A)‖) + ‖(1 : A)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(1 : A)‖ + ‖(1 : A)‖) + ‖(1 : A)‖) + ‖(1 : A)‖ := by gcongr; exact norm_add_le _ _
      _ = 4 := by rw [norm_one]; norm_num
  have hnormsq : ‖C‖ * ‖C‖ ≤ 8 := by
    have h1 : ‖C‖ * ‖C‖ = ‖C * C‖ := by
      rw [← CStarRing.norm_star_mul_self (x := C), hCsa]
    rw [h1, hsq]
    calc ‖(4 : A) - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖(4 : A)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ := norm_sub_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₀ * B₁ - B₁ * B₀‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hs2 : (0:ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hs2sq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [norm_nonneg C, hnormsq, hs2, hs2sq]

end CStar

end QC

