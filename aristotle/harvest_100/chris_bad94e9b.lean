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

(Note: Lean requires `import` commands to come before any module docstring, so this
header is written as an ordinary block comment.)
-/

import Mathlib

/-!
# Tsirelson's bound for the CHSH operator

Given a CHSH tuple `(A₀, A₁, B₀, B₁)` in a unital C*-algebra `A` — four self-adjoint
involutions with each `Aᵢ` commuting with each `Bⱼ` — the CHSH operator

`C = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`

satisfies `‖C‖ ≤ 2√2`.

The proof is the classical one: `C` is self-adjoint and
`C² = 4 + [A₀, A₁] · [B₁, B₀]`, whence `‖C‖² = ‖C²‖ ≤ 4 + 2·2 = 8`.

A corollary specializes this to bounded operators on a complex Hilbert space, where
the norm is the operator norm.
-/

namespace QC

open scoped Real

variable {A : Type*}

/-- The CHSH operator associated to four observables. -/
def chshOp [Ring A] (A₀ A₁ B₀ B₁ : A) : A :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

section Algebra

variable [Ring A]

/-- Auxiliary swap lemma: if `p` commutes with `b`, then `(a * p) * (b * q) = (a * b) * (p * q)`. -/
private lemma mul_mul_mul_swap' {a p b q : A} (h : p * b = b * p) :
    (a * p) * (b * q) = (a * b) * (p * q) := by
  rw [mul_assoc, ← mul_assoc p b q, h, mul_assoc b p q, ← mul_assoc]

/-- Expansion of `(a₀ p + a₁ m)²` when `a₀, a₁` are involutions commuting with `p, m`. -/
private lemma sq_expand {a₀ a₁ p m : A} (h0 : a₀ * a₀ = 1) (h1 : a₁ * a₁ = 1)
    (hp0 : p * a₀ = a₀ * p) (hp1 : p * a₁ = a₁ * p)
    (hm0 : m * a₀ = a₀ * m) (hm1 : m * a₁ = a₁ * m) :
    (a₀ * p + a₁ * m) * (a₀ * p + a₁ * m)
      = (p * p + m * m) + ((a₀ * a₁) * (p * m) + (a₁ * a₀) * (m * p)) := by
  rw [add_mul, mul_add, mul_add, mul_mul_mul_swap' hp0, mul_mul_mul_swap' hp1,
    mul_mul_mul_swap' hm0, mul_mul_mul_swap' hm1, h0, h1, one_mul, one_mul]
  abel

variable [StarRing A]

/-- The square of the CHSH operator: `C² = 4 + [A₀, A₁] · [B₁, B₀]`. -/
theorem chshOp_sq {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ * chshOp A₀ A₁ B₀ B₁ =
      4 + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁) := by
  have hA₀ : A₀ * A₀ = 1 := by rw [← sq]; exact T.A₀_inv
  have hA₁ : A₁ * A₁ = 1 := by rw [← sq]; exact T.A₁_inv
  have hB₀ : B₀ * B₀ = 1 := by rw [← sq]; exact T.B₀_inv
  have hB₁ : B₁ * B₁ = 1 := by rw [← sq]; exact T.B₁_inv
  have hPA₀ : (B₀ + B₁) * A₀ = A₀ * (B₀ + B₁) := by
    rw [add_mul, mul_add, ← T.A₀B₀_commutes, ← T.A₀B₁_commutes]
  have hPA₁ : (B₀ + B₁) * A₁ = A₁ * (B₀ + B₁) := by
    rw [add_mul, mul_add, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
  have hMA₀ : (B₀ - B₁) * A₀ = A₀ * (B₀ - B₁) := by
    rw [sub_mul, mul_sub, ← T.A₀B₀_commutes, ← T.A₀B₁_commutes]
  have hMA₁ : (B₀ - B₁) * A₁ = A₁ * (B₀ - B₁) := by
    rw [sub_mul, mul_sub, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
  have hC : chshOp A₀ A₁ B₀ B₁ = A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁) := by
    simp only [chshOp, mul_add, mul_sub]; abel
  have hPP : (B₀ + B₁) * (B₀ + B₁) + (B₀ - B₁) * (B₀ - B₁) = 4 := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, hB₀, hB₁]
    abel_nf
    norm_num
  have hPM : (B₀ + B₁) * (B₀ - B₁) = B₁ * B₀ - B₀ * B₁ := by
    simp only [add_mul, mul_sub, hB₀, hB₁]; abel
  have hMP : (B₀ - B₁) * (B₀ + B₁) = -(B₁ * B₀ - B₀ * B₁) := by
    simp only [sub_mul, mul_add, hB₀, hB₁]; abel
  rw [hC, sq_expand hA₀ hA₁ hPA₀ hPA₁ hMA₀ hMA₁, hPP, hPM, hMP]
  noncomm_ring

end Algebra

section NormAux

variable [NormedRing A] [NormOneClass A]

private lemma norm_four_le : ‖(4 : A)‖ ≤ 4 := by
  have h : (4 : A) = 1 + 1 + 1 + 1 := by norm_num
  rw [h]
  calc ‖(1 : A) + 1 + 1 + 1‖ ≤ ‖(1 : A) + 1 + 1‖ + ‖(1 : A)‖ := norm_add_le _ _
    _ ≤ (‖(1 : A) + 1‖ + ‖(1 : A)‖) + ‖(1 : A)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖(1 : A)‖ + ‖(1 : A)‖) + ‖(1 : A)‖) + ‖(1 : A)‖ := by gcongr; exact norm_add_le _ _
    _ = 4 := by simp only [norm_one]; norm_num

end NormAux

section Norm

variable [NormedRing A] [StarRing A] [CStarRing A] [NormOneClass A]

/-- A self-adjoint involution in a unital C*-algebra has norm one. -/
theorem norm_eq_one_of_sa_involution {a : A} (hsa : star a = a) (hinv : a ^ 2 = 1) :
    ‖a‖ = 1 := by
  have h : ‖a‖ * ‖a‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, hsa, ← sq, hinv, norm_one]
  nlinarith [norm_nonneg a]

/-- **Tsirelson's bound**: in a unital C*-algebra (e.g. the bounded operators on a Hilbert
space), the CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` built from a CHSH tuple has norm at
most `2√2`. -/
theorem chsh_tsirelson {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * √2 := by
  have hnA₀ : ‖A₀‖ = 1 := norm_eq_one_of_sa_involution T.A₀_sa T.A₀_inv
  have hnA₁ : ‖A₁‖ = 1 := norm_eq_one_of_sa_involution T.A₁_sa T.A₁_inv
  have hnB₀ : ‖B₀‖ = 1 := norm_eq_one_of_sa_involution T.B₀_sa T.B₀_inv
  have hnB₁ : ‖B₁‖ = 1 := norm_eq_one_of_sa_involution T.B₁_sa T.B₁_inv
  have hcommA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 :=
    calc ‖A₀ * A₁ - A₁ * A₀‖ ≤ ‖A₀ * A₁‖ + ‖A₁ * A₀‖ := norm_sub_le _ _
      _ ≤ ‖A₀‖ * ‖A₁‖ + ‖A₁‖ * ‖A₀‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 := by rw [hnA₀, hnA₁]; norm_num
  have hcommB : ‖B₁ * B₀ - B₀ * B₁‖ ≤ 2 :=
    calc ‖B₁ * B₀ - B₀ * B₁‖ ≤ ‖B₁ * B₀‖ + ‖B₀ * B₁‖ := norm_sub_le _ _
      _ ≤ ‖B₁‖ * ‖B₀‖ + ‖B₀‖ * ‖B₁‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 := by rw [hnB₀, hnB₁]; norm_num
  set C : A := chshOp A₀ A₁ B₀ B₁ with hCdef
  have hgoal : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ = C := rfl
  rw [hgoal]
  have hsa : star C = C := by
    rw [hCdef, chshOp]
    simp only [star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
      ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
  have hsq : ‖C‖ * ‖C‖ ≤ 8 := by
    rw [← CStarRing.norm_star_mul_self, hsa, hCdef, chshOp_sq T]
    calc ‖(4 : A) + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖
        ≤ ‖(4 : A)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖ := norm_add_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₁ * B₀ - B₀ * B₁‖ := by
          gcongr
          · exact norm_four_le
          · exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hsq2 : (2 * √2) * (2 * √2) = 8 := by
    have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [h]
  nlinarith [norm_nonneg C, hsq, hsq2, Real.sqrt_nonneg 2]

end Norm

/-- Tsirelson's bound for bounded operators on a complex Hilbert space: the CHSH operator
built from a CHSH tuple of observables has operator norm at most `2√2`. -/
theorem chsh_tsirelson_operator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * √2 :=
  chsh_tsirelson T

end QC

