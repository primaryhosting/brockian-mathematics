import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem MOD_self_mem (q : ℕ) : InAC0mod q (MOD q) := by
  have hd : ∀ l : List ℕ, List.foldr max 0 (List.map (Circuit.depth ∘ Circuit.var) l) = 0 := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  have hs : ∀ l : List ℕ, (List.map (Circuit.size ∘ Circuit.var) l).sum = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih, Nat.add_comm]
  refine ⟨1, 1, fun n => ⟨Circuit.cmod ((List.range n).map Circuit.var), ?_, ?_, ?_⟩⟩
  · simp [Circuit.depth_cmod, hd]
  · simp [Circuit.size_cmod, hs]
  · intro x _
    rw [Circuit.eval_cmod]
    have h : (List.map (fun c => Circuit.eval q c x) ((List.range n).map Circuit.var))
        = (List.range n).map x := by
      rw [List.map_map]
      exact List.map_congr_left (by intro i _; simp)
    rw [h, count_true_range]
    rfl

/-- **Razborov–Smolensky theorem**: for distinct primes `p` and `q`, `MOD p ∉ AC⁰[q]`. -/
