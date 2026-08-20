import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem bit_var_mem_Deg {n : ℕ} (i : Fin n) :
    (fun x : Cube n => bitv F (x i)) ∈ Deg F n 1 := by
  have h := mon_mem_Deg (F := F) (S := ({i} : Finset (Fin n))) (d := 1) (by simp)
  have he : (fun x : Cube n => bitv F (x i)) = (mon ({i} : Finset (Fin n)) : Cube n → F) := by
    funext x; simp [mon]
  rw [he]; exact h

open Classical in
/-- The set of points where `P` fails to compute the Boolean function `v`. -/
