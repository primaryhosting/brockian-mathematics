/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

lemma ee_sum (d : ZMod 17) : ∑ k : ZMod 17, ee (k * d) = if d = 0 then 17 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero]
  · rw [if_neg hd]
    have hbij : ∑ k : ZMod 17, ee (k * d) = ∑ k : ZMod 17, ee k :=
      Equiv.sum_comp (Equiv.mulRight₀ d hd) ee
    rw [hbij]
    have h2 : ∑ k : ZMod 17, ee k = ∑ j ∈ Finset.range 17, om ^ j := by
      rw [Finset.sum_nbij' (i := fun (k : ZMod 17) => k.val) (j := fun (j : ℕ) => (j : ZMod 17))]
      · intro a _; simp [ZMod.val_lt]
      · intro a _; simp
      · intro a _; simp
      · intro a ha; simp only [Finset.mem_range] at ha
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
      · intro a _; rfl
    rw [h2]
    exact om_prim.geom_sum_eq_zero (by norm_num)

/-- The adjacency matrix of the cycle graph `C₁₇`, with vertices indexed by `ZMod 17`. -/
