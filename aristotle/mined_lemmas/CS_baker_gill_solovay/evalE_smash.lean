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


@[simp] lemma evalE_smash : evalE O (.smash a b) st =
    (List.replicate ((evalE O a st).1.length * (evalE O b (evalE O a st).2).1.length) false,
      { (evalE O b (evalE O a st).2).2 with
        cost := (evalE O b (evalE O a st).2).2.cost
          + (evalE O a st).1.length * (evalE O b (evalE O a st).2).1.length + 1 }) := rfl

