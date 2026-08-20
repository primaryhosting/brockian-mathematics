/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGSModel

/-!
## Basic properties of the machine model

* costs and query lists only grow;
* the cost of a run does not depend on the cost already accumulated (`run_shift`);
* every recorded query has length at most the cost, and there are at most `cost`
  many queries (`run_QInv`);
* locality: a run only depends on the oracle at the strings it queries
  (`run_local`).
-/

namespace CS.BGS

variable {O O' : Oracle} {st : State} {i : ℕ} {s : Str} {a b c e : Expr}

/-! ### Unfolding lemmas -/


lemma run_shift (O : Oracle) (p : Prog) (st : State) (d : ℕ) :
    run O p (shiftSt st d) = shiftSt (run O p st) d := by
  induction p generalizing st with
  | skip => simp [shiftSt]; omega
  | assign i e => simp [shiftSt, evalE_shift]; omega
  | seq p q ihp ihq => simp only [run_seq, ihp, ihq]
  | ite c t f iht ihf =>
      rw [run_ite, run_ite, evalE_shift]
      have key : ({ shiftSt (evalE O c st).2 d with
            cost := (shiftSt (evalE O c st).2 d).cost + 1 } : State)
          = shiftSt { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } d := by
        simp [shiftSt]; omega
      simp only [key]
      split
      · exact ihf _ _
      · exact iht _ _
  | loop c body ih =>
      rw [run_loop, run_loop, evalE_shift]
      have key : ({ shiftSt (evalE O c st).2 d with
            cost := (shiftSt (evalE O c st).2 d).cost + 1 } : State)
          = shiftSt { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } d := by
        simp [shiftSt]; omega
      simp only [key]
      exact iter_shift O body (fun s d => ih s) _ _ _

/-! ### The cost bounds the queries -/

/-- Invariant: every recorded query is no longer than the cost so far, and there are
at most `cost` many recorded queries. -/
