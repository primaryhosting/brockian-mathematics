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
## Overview

For a CHSH tuple `A₀, A₁, B₀, B₁` (four self-adjoint involutions, with the `Aᵢ` commuting with
the `Bⱼ`) inside a unital C*-algebra, the CHSH operator

  `M = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`

satisfies Tsirelson's bound `‖M‖ ≤ 2 √2`.

The proof is the classical one: one checks the algebraic identity

  `M ^ 2 = 4 - [A₀, A₁] * [B₀, B₁]`,

each commutator has norm at most `2` (since each entry is a self-adjoint involution, hence of
norm one), so `‖M ^ 2‖ ≤ 8`; since `M` is self-adjoint, the C*-identity gives
`‖M‖ ^ 2 = ‖M ^ 2‖ ≤ 8`, i.e. `‖M‖ ≤ 2 √2`.

The statement is given for an arbitrary unital C*-algebra; since the algebra `H →L[ℂ] H` of
bounded operators on a Hilbert space is such an algebra, the usual statement about the operator
norm of the quantum CHSH operator follows (see `QC.chsh_tsirelson_operator`).
-/

namespace QC

open scoped Real

variable {R : Type*}

/-- The CHSH operator associated with four observables. -/
def chshOp [Mul R] [Add R] [Sub R] (A₀ A₁ B₀ B₁ : R) : R :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

section Algebraic

variable [Ring R] [StarRing R]

/-- The key algebraic identity `M ^ 2 = 4 - [A₀, A₁] * [B₀, B₁]` for the CHSH operator `M`. -/
theorem chshOp_sq {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ ^ 2 = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  obtain ⟨hA0, hA1, hB0, hB1, -, -, -, -, c00, c01, c10, c11⟩ := T
  simp only [pow_two] at hA0 hA1 hB0 hB1
  have d00 : ∀ x : R, B₀ * (A₀ * x) = A₀ * (B₀ * x) := fun x => by
    rw [← mul_assoc, ← c00, mul_assoc]
  have d01 : ∀ x : R, B₁ * (A₀ * x) = A₀ * (B₁ * x) := fun x => by
    rw [← mul_assoc, ← c01, mul_assoc]
  have d10 : ∀ x : R, B₀ * (A₁ * x) = A₁ * (B₀ * x) := fun x => by
    rw [← mul_assoc, ← c10, mul_assoc]
  have d11 : ∀ x : R, B₁ * (A₁ * x) = A₁ * (B₁ * x) := fun x => by
    rw [← mul_assoc, ← c11, mul_assoc]
  have e0 : ∀ x : R, A₀ * (A₀ * x) = x := fun x => by rw [← mul_assoc, hA0, one_mul]
  have e1 : ∀ x : R, A₁ * (A₁ * x) = x := fun x => by rw [← mul_assoc, hA1, one_mul]
  have hfour : (4 : R) = 1 + 1 + 1 + 1 := by norm_num
  simp only [chshOp]
  noncomm_ring
  simp only [d00, d01, d10, d11, e0, e1, hA0, hA1, hB0, hB1, mul_one]
  rw [hfour]
  abel

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
theorem chshOp_isSelfAdjoint {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    star (chshOp A₀ A₁ B₀ B₁) = chshOp A₀ A₁ B₀ B₁ := by
  simp only [chshOp, star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

end Algebraic

section CStar

variable [NormedRing R] [StarRing R] [CStarRing R] [NormOneClass R]

/-- A self-adjoint involution in a unital C*-algebra has norm one. -/
theorem norm_eq_one_of_star_eq_self_of_sq_eq_one {A : R} (hsa : star A = A) (hinv : A ^ 2 = 1) :
    ‖A‖ = 1 := by
  have h : ‖A‖ * ‖A‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, hsa, ← pow_two, hinv, norm_one]
  nlinarith [norm_nonneg A]

/-- The commutator of two self-adjoint involutions has norm at most `2`. -/
theorem norm_commutator_le {A B : R} (hA : star A = A) (hA2 : A ^ 2 = 1)
    (hB : star B = B) (hB2 : B ^ 2 = 1) : ‖A * B - B * A‖ ≤ 2 := by
  have hA1 : ‖A‖ = 1 := norm_eq_one_of_star_eq_self_of_sq_eq_one hA hA2
  have hB1 : ‖B‖ = 1 := norm_eq_one_of_star_eq_self_of_sq_eq_one hB hB2
  calc ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := by gcongr <;> exact norm_mul_le _ _
    _ = 2 := by rw [hA1, hB1]; norm_num

/-- **Tsirelson's bound.** The CHSH operator of a CHSH tuple in a unital C*-algebra
(for instance, the algebra of bounded operators on a Hilbert space) has norm at most `2 √2`. -/
theorem chsh_tsirelson {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2 := by
  set M : R := chshOp A₀ A₁ B₀ B₁ with hM
  -- the norm of `M ^ 2` is at most `8`
  have hfour : ‖(4 : R)‖ ≤ 4 := by
    have h4 : (4 : R) = 1 + 1 + 1 + 1 := by norm_num
    calc ‖(4 : R)‖ = ‖(1 : R) + 1 + 1 + 1‖ := by rw [h4]
      _ ≤ ‖(1 : R) + 1 + 1‖ + ‖(1 : R)‖ := norm_add_le _ _
      _ ≤ (‖(1 : R) + 1‖ + ‖(1 : R)‖) + ‖(1 : R)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(1 : R)‖ + ‖(1 : R)‖) + ‖(1 : R)‖) + ‖(1 : R)‖ := by gcongr; exact norm_add_le _ _
      _ = 4 := by rw [norm_one]; norm_num
  have hA := norm_commutator_le T.A₀_sa T.A₀_inv T.A₁_sa T.A₁_inv
  have hB := norm_commutator_le T.B₀_sa T.B₀_inv T.B₁_sa T.B₁_inv
  have hsq : ‖M ^ 2‖ ≤ 8 := by
    rw [hM, chshOp_sq T]
    calc ‖(4 : R) - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖(4 : R)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ := norm_sub_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₀ * B₁ - B₁ * B₀‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by gcongr
      _ = 8 := by norm_num
  -- self-adjointness plus the C*-identity turn this into a bound on `‖M‖`
  have hnorm : ‖M‖ * ‖M‖ ≤ 8 := by
    have := CStarRing.norm_star_mul_self (x := M)
    rw [chshOp_isSelfAdjoint T, ← pow_two] at this
    rw [← this]
    exact hsq
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [norm_nonneg M, Real.sqrt_nonneg 2]

end CStar

/-- Tsirelson's bound for the quantum CHSH operator, stated for bounded operators on a
complex Hilbert space: if `A₀, A₁, B₀, B₁` are `±1`-valued observables (self-adjoint
involutions) with the `Aᵢ` commuting with the `Bⱼ`, then the operator norm of the CHSH
operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` is at most `2 √2`. -/
theorem chsh_tsirelson_operator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_tsirelson T

end QC

