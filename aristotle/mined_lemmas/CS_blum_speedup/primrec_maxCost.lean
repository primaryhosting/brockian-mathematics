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

theorem primrec_maxCost :
    Primrec fun p : Env × ℕ × ℕ => maxCost (costE p.1) p.2.1 p.2.2 := by
  have hmap : Primrec fun p : Env × ℕ × ℕ =>
      (List.range (p.2.2 + 1)).map
        (fun d => costE p.1 (Nat.pair (Nat.pair (p.2.1 + 1) d) p.2.2)) := by
    refine Primrec.list_map
      (f := fun p : Env × ℕ × ℕ => List.range (p.2.2 + 1))
      (g := fun (p : Env × ℕ × ℕ) (d : ℕ) => costE p.1 (Nat.pair (Nat.pair (p.2.1 + 1) d) p.2.2))
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec₂.mk (primrec_costE.comp (Primrec.fst.comp Primrec.fst) ?_))
    exact Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.list_foldr (f := fun p : Env × ℕ × ℕ =>
      (List.range (p.2.2 + 1)).map (fun d => costE p.1 (Nat.pair (Nat.pair (p.2.1 + 1) d) p.2.2)))
    (g := fun _ => 0) (h := fun _ q => max q.1 q.2) hmap (Primrec.const 0)
    (Primrec₂.mk (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))

