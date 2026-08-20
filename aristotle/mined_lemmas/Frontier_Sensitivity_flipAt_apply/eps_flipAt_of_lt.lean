import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma eps_flipAt_of_lt {n : ℕ} (u : Q n) {k l : Fin n} (h : k < l) :
    eps (flipAt k u) l = - eps u l := by
  have hk : k ∈ Finset.univ.filter (fun i : Fin n => i < l) := by simp [h]
  rw [eps, eps, ← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk]
  have hprod : ∏ i ∈ (Finset.univ.filter (fun i : Fin n => i < l)).erase k,
      (if flipAt k u i then (-1 : ℝ) else 1)
      = ∏ i ∈ (Finset.univ.filter (fun i : Fin n => i < l)).erase k,
        (if u i then (-1 : ℝ) else 1) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [flipAt_apply_of_ne _ (Finset.ne_of_mem_erase hi)]
  rw [hprod, flipAt_apply_self]
  cases hu : u k <;> simp

/-! #### Entries of the signed adjacency matrix -/

