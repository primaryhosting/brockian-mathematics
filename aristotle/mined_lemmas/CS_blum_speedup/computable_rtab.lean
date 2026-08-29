import RequestProject.BlumTime

/-!
# The core of the speed-up construction

This file contains the (first-order, oracle-parametrised) combinatorial core of the
diagonal construction used in the proof of Blum's speed-up theorem.

The construction is parametrised by two functions:

* `rf : ℕ → ℕ`, the speed-up factor;
* `T : ℕ → ℕ`, an oracle giving the running time of the (self-referential) code under
  construction at a given input.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Small helpers -/

/-- Bounded universal quantifier, as a `Bool`. -/

theorem computable_rtab {r : ℕ → ℕ} (hr : Computable r) : Computable (rtab r) := by
  have h : Computable fun k : ℕ =>
      Nat.rec (motive := fun _ => List ℕ) [r 0] (fun n l => l ++ [r (n + 1)]) k := by
    refine Computable.nat_rec (f := fun k : ℕ => k) (g := fun _ : ℕ => [r 0])
      (h := fun (_ : ℕ) (p : ℕ × List ℕ) => p.2 ++ [r (p.1 + 1)]) Computable.id
      (Computable.list_cons.comp (hr.comp (Computable.const 0)) (Computable.const []))
      (Computable₂.mk (Computable.list_append.comp (Computable.snd.comp Computable.snd)
        (Computable.list_cons.comp
          (hr.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))
          (Computable.const []))))
  refine h.of_eq fun k => ?_
  induction k with
  | zero => simp [rtab]
  | succ k ih =>
    simp only [rtab, List.range_succ, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [ih]

/-- The functional whose fixed point is the family of programs. -/
