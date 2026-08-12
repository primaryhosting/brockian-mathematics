import Mathlib

open Finset Polynomial

namespace Math

/-- For `1 < n`, the sum of all complex `n`-th roots of unity is zero. -/
lemma sum_nthRootsFinset_complex_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ z ∈ nthRootsFinset n (1 : ℂ), z = 0 := by
  have hpos : 0 < n := lt_trans Nat.zero_lt_one hn
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hpos.ne'⟩
  have hnodup : (nthRoots n (1 : ℂ)).Nodup := IsPrimitiveRoot.nthRoots_one_nodup hζ
  have hset : nthRootsFinset n (1 : ℂ) = (nthRoots n (1 : ℂ)).toFinset :=
    nthRootsFinset_def n (1 : ℂ)
  rw [hset, show (∑ z ∈ (nthRoots n (1:ℂ)).toFinset, z)
        = ((nthRoots n (1:ℂ)).toFinset.val.map id).sum from rfl,
    Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup,
    IsPrimitiveRoot.nthRoots_eq hζ (α := 1) (one_pow n)]
  simp only [mul_one, Multiset.map_map, Function.comp_def, id]
  rw [show ((Multiset.range n).map (fun i => ζ ^ i)).sum = ∑ i ∈ Finset.range n, ζ ^ i from rfl]
  exact hζ.geom_sum_eq_zero hn

/-- The sum of the primitive 9-th roots of unity (in `ℂ`) equals the Möbius function `μ 9`. -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  classical
  have h9 : nthRootsFinset 9 (1 : ℂ) = (Nat.divisors 9).biUnion fun i ↦ primitiveRoots i ℂ :=
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots
  have h3 : nthRootsFinset 3 (1 : ℂ) = (Nat.divisors 3).biUnion fun i ↦ primitiveRoots i ℂ :=
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots
  have hd9 : Nat.divisors 9 = ({1, 3, 9} : Finset ℕ) := by decide
  have hd3 : Nat.divisors 3 = ({1, 3} : Finset ℕ) := by decide
  have s9 : ∑ z ∈ nthRootsFinset 9 (1 : ℂ), z
      = (∑ z ∈ primitiveRoots 1 ℂ, z) + (∑ z ∈ primitiveRoots 3 ℂ, z)
        + ∑ z ∈ primitiveRoots 9 ℂ, z := by
    rw [h9, hd9, Finset.sum_biUnion]
    · simp [Finset.sum_insert, add_assoc]
    · intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun x hx hx' =>
        hab ((isPrimitiveRoot_of_mem_primitiveRoots hx).unique
          (isPrimitiveRoot_of_mem_primitiveRoots hx'))
  have s3 : ∑ z ∈ nthRootsFinset 3 (1 : ℂ), z
      = (∑ z ∈ primitiveRoots 1 ℂ, z) + ∑ z ∈ primitiveRoots 3 ℂ, z := by
    rw [h3, hd3, Finset.sum_biUnion]
    · simp [Finset.sum_insert]
    · intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun x hx hx' =>
        hab ((isPrimitiveRoot_of_mem_primitiveRoots hx).unique
          (isPrimitiveRoot_of_mem_primitiveRoots hx'))
  have z9 : ∑ z ∈ nthRootsFinset 9 (1 : ℂ), z = 0 :=
    sum_nthRootsFinset_complex_eq_zero (by norm_num)
  have z3 : ∑ z ∈ nthRootsFinset 3 (1 : ℂ), z = 0 :=
    sum_nthRootsFinset_complex_eq_zero (by norm_num)
  have hmu : (ArithmeticFunction.moebius 9 : ℤ) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by
      intro h
      have := h 3 (by norm_num)
      simp at this)
  rw [z9] at s9
  rw [z3] at s3
  rw [← s3] at s9
  have : ∑ z ∈ primitiveRoots 9 ℂ, z = 0 := by linear_combination -s9
  rw [this, hmu]
  norm_num

end Math

