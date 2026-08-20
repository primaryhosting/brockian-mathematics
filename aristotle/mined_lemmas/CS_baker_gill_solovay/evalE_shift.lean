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


lemma evalE_shift (O : Oracle) (e : Expr) (st : State) (d : ℕ) :
    evalE O e (shiftSt st d) = ((evalE O e st).1, shiftSt (evalE O e st).2 d) := by
  induction e generalizing st with
  | var i => simp [shiftSt]
  | lit s => simp [shiftSt]; omega
  | cat a b iha ihb => simp [shiftSt, iha, ihb]; omega
  | smash a b iha ihb => simp [shiftSt, iha, ihb]; omega
  | tail a iha => simp [shiftSt, iha]; omega
  | eqE a b iha ihb => simp [shiftSt, iha, ihb]; omega
  | query a iha => simp [shiftSt, iha]; omega

