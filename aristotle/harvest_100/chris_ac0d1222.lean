import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math

open Finset Polynomial

/-- The sum of all `n`-th roots of unity in `ℂ` vanishes when `1 < n`. -/
lemma sum_nthRootsFinset_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ x ∈ nthRootsFinset n (1 : ℂ), x = 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (by omega)
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (Finset.range n) := by
    intro i hi j hj hij
    exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have himg : (Finset.range n).image (fun i : ℕ => ζ ^ i) = nthRootsFinset n (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [Polynomial.mem_nthRootsFinset (by omega)]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himg, Finset.sum_image (fun i hi j hj h => hinj hi hj h)]
  exact hζ.geom_sum_eq_zero hn

/-- The sum of the primitive `9`-th roots of unity equals `μ(9)`. -/
theorem mobius_root_sum_9 :
    ∑ ζ ∈ primitiveRoots 9 ℂ, ζ = (ArithmeticFunction.moebius 9 : ℤ) := by
  have hdisj : ∀ (m : ℕ), ((Nat.divisors m : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => primitiveRoots i ℂ) := by
    intro m i _ j _ hij
    exact IsPrimitiveRoot.disjoint hij
  have h9 : ∑ i ∈ Nat.divisors 9, ∑ ζ ∈ primitiveRoots i ℂ, ζ = 0 := by
    rw [← Finset.sum_biUnion (hdisj 9),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots (n := 9) (R := ℂ)]
    exact sum_nthRootsFinset_eq_zero (by norm_num)
  have h3 : ∑ i ∈ Nat.divisors 3, ∑ ζ ∈ primitiveRoots i ℂ, ζ = 0 := by
    rw [← Finset.sum_biUnion (hdisj 3),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots (n := 3) (R := ℂ)]
    exact sum_nthRootsFinset_eq_zero (by norm_num)
  have hd9 : Nat.divisors 9 = ({1, 3, 9} : Finset ℕ) := by decide
  have hd3 : Nat.divisors 3 = ({1, 3} : Finset ℕ) := by decide
  rw [hd9] at h9
  rw [hd3] at h3
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton] at h9
  rw [Finset.sum_insert (by simp), Finset.sum_singleton] at h3
  have hmu : ArithmeticFunction.moebius 9 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    have := hsq 3 (by norm_num)
    simp at this
  rw [hmu]
  push_cast
  norm_num at h9 h3 ⊢
  linear_combination h9 - h3

end Math

