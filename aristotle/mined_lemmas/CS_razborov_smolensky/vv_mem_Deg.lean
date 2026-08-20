import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem vv_mem_Deg (ζ : F) (i : Fin n) : vv ζ i ∈ Deg F n 1 := by
  have h : vv ζ i = (fun _ : Cube n => (1 : F)) + (ζ⁻¹ - 1) • (fun x : Cube n => bitv F (x i)) := by
    funext x; simp [vv, mul_comm]
  rw [h]
  exact Submodule.add_mem _ (const_mem_Deg _) (Submodule.smul_mem _ _ (bit_var_mem_Deg i))

