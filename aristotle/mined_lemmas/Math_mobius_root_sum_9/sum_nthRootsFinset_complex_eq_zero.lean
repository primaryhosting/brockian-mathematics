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
