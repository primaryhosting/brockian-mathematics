import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma exp_mul_exp_eq_sum_bchL {K : ℕ} (hKa : a ^ K = 0) (hKb : b ^ K = 0) :
    IsNilpotent.exp a * IsNilpotent.exp b = ∑ N ∈ range (2 * K), bchL a b N := by
  classical
  have hprod : IsNilpotent.exp a * IsNilpotent.exp b
      = ∑ p ∈ range K ×ˢ range K, ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2) := by
    rw [IsNilpotent.exp_eq_sum hKa, IsNilpotent.exp_eq_sum hKb, Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_inv]
  have hmaps : ∀ p ∈ range K ×ˢ range K, p.1 + p.2 ∈ range (2 * K) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2))]
  refine Finset.sum_congr rfl fun N _ => ?_
  have hsub : ∑ p ∈ (range K ×ˢ range K) with p.1 + p.2 = N,
        ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2)
      = ∑ p ∈ Finset.antidiagonal N, ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      rw [Finset.mem_antidiagonal]
      exact hp.2
    · intro p hp hp2
      rw [Finset.mem_antidiagonal] at hp
      have hno : ¬ (p.1 < K ∧ p.2 < K) := by
        intro hcon
        exact hp2 (by
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨hcon.1, hcon.2⟩, hp⟩)
      rcases not_and_or.mp hno with h | h
      · rw [pow_eq_zero_of_le (not_lt.mp h) hKa, zero_mul, smul_zero]
      · rw [pow_eq_zero_of_le (not_lt.mp h) hKb, mul_zero, smul_zero]
  rw [hsub, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, bchL]

/-- Assembling the graded components of `exp d * exp (c/2)`. -/
