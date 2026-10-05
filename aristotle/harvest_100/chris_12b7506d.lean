import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

variable {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [NormOneClass R]

/-- The CHSH operator associated to a CHSH tuple `(A₀, A₁, B₀, B₁)`. -/
def chshOp (A₀ A₁ B₀ B₁ : R) : R := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

section Ring

variable {S : Type*} [Ring S]

/-- Interchange of the two middle factors of a product of four elements,
when they commute. -/
theorem mul_mul_mul_comm_of_commute (x y z w : S) (h : y * z = z * y) :
    x * y * (z * w) = x * z * (y * w) := by
  calc x * y * (z * w) = x * (y * z * w) := by noncomm_ring
    _ = x * (z * y * w) := by rw [h]
    _ = x * z * (y * w) := by noncomm_ring

end Ring

/-- A self-adjoint involution in a unital C*-algebra has norm one. -/
theorem norm_eq_one_of_sa_involution {A : R} (hsa : star A = A) (hinv : A ^ 2 = 1) :
    ‖A‖ = 1 := by
  have hA : A * A = 1 := by rw [← pow_two, hinv]
  have h : ‖A‖ * ‖A‖ = 1 := by
    have h2 := CStarRing.norm_star_mul_self (x := A)
    rw [hsa, hA, norm_one] at h2
    linarith
  nlinarith [norm_nonneg A]

omit [CStarRing R] [NormOneClass R] in
/-- The CHSH operator is self-adjoint. -/
theorem chshOp_isSelfAdjoint {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    star (chshOp A₀ A₁ B₀ B₁) = chshOp A₀ A₁ B₀ B₁ := by
  simp only [chshOp, star_add, star_sub, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

omit [CStarRing R] [NormOneClass R] in
/-- The square of the CHSH operator equals `4 + [A₀, A₁] * [B₁, B₀]`. -/
theorem chshOp_sq {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ ^ 2 = 4 + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁) := by
  have hA₀ : A₀ * A₀ = 1 := by rw [← pow_two, T.A₀_inv]
  have hA₁ : A₁ * A₁ = 1 := by rw [← pow_two, T.A₁_inv]
  have hB₀ : B₀ * B₀ = 1 := by rw [← pow_two, T.B₀_inv]
  have hB₁ : B₁ * B₁ = 1 := by rw [← pow_two, T.B₁_inv]
  have c₀₀ : B₀ * A₀ = A₀ * B₀ := T.A₀B₀_commutes.symm
  have c₀₁ : B₁ * A₀ = A₀ * B₁ := T.A₀B₁_commutes.symm
  have c₁₀ : B₀ * A₁ = A₁ * B₀ := T.A₁B₀_commutes.symm
  have c₁₁ : B₁ * A₁ = A₁ * B₁ := T.A₁B₁_commutes.symm
  rw [pow_two, chshOp]
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  simp only [mul_mul_mul_comm_of_commute _ _ _ _ c₀₀,
    mul_mul_mul_comm_of_commute _ _ _ _ c₀₁,
    mul_mul_mul_comm_of_commute _ _ _ _ c₁₀,
    mul_mul_mul_comm_of_commute _ _ _ _ c₁₁]
  simp only [hA₀, hA₁, hB₀, hB₁, one_mul, mul_one]
  noncomm_ring
  abel_nf
  simp
  abel

/-- **Tsirelson's bound**: in a unital C*-algebra, the CHSH operator of a CHSH tuple has
norm at most `2√2`.

Mathlib's `tsirelson_inequality` (in `Mathlib/Algebra/Star/CHSH.lean`) gives the order-theoretic
bound `A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1` in an ordered `*`-algebra; here we
prove the norm (operator-norm) form, using the C*-identity together with the algebraic identity
`chshOp_sq`. -/
theorem chsh_tsirelson {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2 := by
  set S : R := chshOp A₀ A₁ B₀ B₁ with hS
  have hnA₀ : ‖A₀‖ = 1 := norm_eq_one_of_sa_involution T.A₀_sa T.A₀_inv
  have hnA₁ : ‖A₁‖ = 1 := norm_eq_one_of_sa_involution T.A₁_sa T.A₁_inv
  have hnB₀ : ‖B₀‖ = 1 := norm_eq_one_of_sa_involution T.B₀_sa T.B₀_inv
  have hnB₁ : ‖B₁‖ = 1 := norm_eq_one_of_sa_involution T.B₁_sa T.B₁_inv
  have hcommA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 := by
    calc ‖A₀ * A₁ - A₁ * A₀‖ ≤ ‖A₀ * A₁‖ + ‖A₁ * A₀‖ := norm_sub_le _ _
      _ ≤ ‖A₀‖ * ‖A₁‖ + ‖A₁‖ * ‖A₀‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ = 2 := by rw [hnA₀, hnA₁]; norm_num
  have hcommB : ‖B₁ * B₀ - B₀ * B₁‖ ≤ 2 := by
    calc ‖B₁ * B₀ - B₀ * B₁‖ ≤ ‖B₁ * B₀‖ + ‖B₀ * B₁‖ := norm_sub_le _ _
      _ ≤ ‖B₁‖ * ‖B₀‖ + ‖B₀‖ * ‖B₁‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ = 2 := by rw [hnB₀, hnB₁]; norm_num
  have h4 : ‖(4 : R)‖ ≤ 4 := by
    have h : (4 : R) = 1 + 1 + 1 + 1 := by norm_num
    rw [h]
    calc ‖(1 : R) + 1 + 1 + 1‖ ≤ ‖(1 : R) + 1 + 1‖ + ‖(1 : R)‖ := norm_add_le _ _
      _ ≤ (‖(1 : R) + 1‖ + ‖(1 : R)‖) + ‖(1 : R)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(1 : R)‖ + ‖(1 : R)‖) + ‖(1 : R)‖) + ‖(1 : R)‖ := by
          gcongr; exact norm_add_le _ _
      _ = 4 := by rw [norm_one]; norm_num
  have hsq : ‖S‖ * ‖S‖ ≤ 8 := by
    have h1 : ‖S‖ * ‖S‖ = ‖S ^ 2‖ := by
      have h2 := CStarRing.norm_star_mul_self (x := S)
      rw [chshOp_isSelfAdjoint T] at h2
      rw [pow_two, ← h2]
    rw [h1, chshOp_sq T]
    calc ‖(4 : R) + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖
        ≤ ‖(4 : R)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖ := norm_add_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₁ * B₀ - B₀ * B₁‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [norm_nonneg S, Real.sqrt_nonneg 2]

/-- **Tsirelson's bound for operators on a Hilbert space**: for four bounded observables
`A₀, A₁, B₀, B₁` on a Hilbert space forming a CHSH tuple (each self-adjoint with square `1`,
with the `Aᵢ` commuting with the `Bⱼ`), the CHSH operator
`A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` has operator norm at most `2√2`. -/
theorem chsh_tsirelson_operator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (A₀ A₁ B₀ B₁ : H →L[ℂ] H)
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_tsirelson T

end QC

#print axioms QC.chsh_tsirelson
#print axioms QC.chsh_tsirelson_operator

