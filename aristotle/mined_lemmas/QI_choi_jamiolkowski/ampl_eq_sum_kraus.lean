import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

universe u

variable {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras, acting on
`k × n` block matrices: the `(x, y)` block of `M` (an `n × n` matrix) is sent to the
`(x, y)` block of the result (an `m × m` matrix). -/

lemma ampl_eq_sum_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (B : Matrix (n × m) (n × m) ℂ) (hB : choi Φ = Bᴴ * B)
    (k : Type*) [Fintype k] [DecidableEq k] (M : Matrix (k × n) (k × n) ℂ) :
    ampl Φ M = ∑ r : n × m, krausAmpl B r k * M * (krausAmpl B r k)ᴴ := by
  ext p q
  rw [Matrix.sum_apply]
  have hL : ampl Φ M p q =
      ∑ i, ∑ j, ∑ r : n × m,
        (starRingEnd ℂ) (B r (i, p.2)) * M (p.1, i) (q.1, j) * B r (j, q.2) := by
    rw [ampl]
    simp only [Matrix.of_apply]
    rw [apply_eq_sum_choi]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hB]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [starRingEnd_apply]
    ring
  have hR : ∀ r : n × m, (krausAmpl B r k * M * (krausAmpl B r k)ᴴ) p q =
      ∑ i, ∑ j, (starRingEnd ℂ) (B r (i, p.2)) * M (p.1, i) (q.1, j) * B r (j, q.2) := by
    intro r
    have hKM : ∀ (t : k × n), (krausAmpl B r k * M) p t
        = ∑ i, (starRingEnd ℂ) (B r (i, p.2)) * M (p.1, i) t := by
      intro t
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [krausAmpl, Matrix.of_apply, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hKM]
    simp only [krausAmpl, Matrix.of_apply, apply_ite (star : ℂ → ℂ), star_zero,
      starRingEnd_apply, star_star]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  rw [hL]
  simp only [hR]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  exact Finset.sum_comm

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
