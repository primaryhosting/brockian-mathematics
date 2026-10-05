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

theorem primrec_allB {α : Type*} [Primcodable α] {f : α → ℕ → Bool} {m : α → ℕ}
    (hm : Primrec m) (hf : Primrec₂ f) : Primrec fun a => allB (m a) (fun y => f a y) := by
  have h : Primrec fun a => ((List.range (m a)).foldr (fun y b => f a y && b) true) :=
    Primrec.list_foldr (f := fun a => List.range (m a)) (g := fun _ => true)
      (h := fun a p => f a p.1 && p.2) (Primrec.list_range.comp hm) (Primrec.const true)
      (Primrec₂.mk (Primrec.and.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))
  refine h.of_eq fun a => ?_
  simp only [allB]
  induction (List.range (m a)) with
  | nil => simp
  | cons b l ih => simp [ih]

