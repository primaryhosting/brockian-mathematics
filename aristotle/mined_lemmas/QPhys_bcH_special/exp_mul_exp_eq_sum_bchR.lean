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

lemma exp_mul_exp_eq_sum_bchR (hcd : Commute c d) {K : ℕ} (hKc : c ^ K = 0) (hKd : d ^ K = 0) :
    IsNilpotent.exp d * IsNilpotent.exp ((2⁻¹ : ℚ) • c) = ∑ N ∈ range (3 * K), bchR c d N := by
  classical
  have hKc' : ((2⁻¹ : ℚ) • c) ^ K = 0 := by rw [smul_pow, hKc, smul_zero]
  have hprod : IsNilpotent.exp d * IsNilpotent.exp ((2⁻¹ : ℚ) • c)
      = ∑ p ∈ range K ×ˢ range K,
          ((p.1 ! : ℚ) * (p.2 ! : ℚ) * 2 ^ p.2)⁻¹ • (c ^ p.2 * d ^ p.1) := by
    rw [IsNilpotent.exp_eq_sum hKd, IsNilpotent.exp_eq_sum hKc', Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_pow, smul_smul, smul_mul_smul_comm, (hcd.pow_pow j i).eq]
    congr 1
    rw [inv_pow]
    field_simp
  have hmaps : ∀ p ∈ range K ×ˢ range K, p.1 + 2 * p.2 ∈ range (3 * K) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => ((p.1 ! : ℚ) * (p.2 ! : ℚ) * 2 ^ p.2)⁻¹ • (c ^ p.2 * d ^ p.1))]
  refine Finset.sum_congr rfl fun N _ => ?_
  have hB : ∑ j ∈ (range (N + 1)) with (2 * j ≤ N ∧ j < K ∧ N - 2 * j < K),
        bchCoef N j • (c ^ j * d ^ (N - 2 * j)) = bchR c d N := by
    rw [bchR]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j hj hj2
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj hj2
    by_cases h1 : 2 * j ≤ N
    · rcases lt_or_ge j K with h2 | h2
      · have h3 : K ≤ N - 2 * j := not_lt.mp (hj2 hj h1 h2)
        rw [pow_eq_zero_of_le h3 hKd, mul_zero, smul_zero]
      · rw [pow_eq_zero_of_le h2 hKc, zero_mul, smul_zero]
    · rw [bchCoef, if_neg h1, zero_smul]
  rw [← hB]
  refine Finset.sum_nbij' (fun p => p.2) (fun j => (N - 2 * j, j)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hj ⊢
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have h5 : N - 2 * p.2 = p.1 := by omega
    simp [h5]
  · intro j _
    simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    dsimp only
    have hp1 : N - 2 * p.2 = p.1 := by omega
    rw [bchCoef, if_pos (by omega), hp1]

end

/-- **Baker–Campbell–Hausdorff, special case of a central commutator.**

If `a` and `b` are nilpotent elements of a `ℚ`-algebra whose commutator `[a,b] = ab - ba`
commutes with both `a` and `b`, then `exp a * exp b = exp (a + b + ½[a,b])`. -/
