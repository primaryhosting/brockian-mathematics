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


lemma iter_cost_mono (O : Oracle) (body : Prog)
    (ih : ∀ s : State, s.cost ≤ (run O body s).cost) (n : ℕ) (s : State) :
    s.cost ≤ ((run O body)^[n] s).cost := by
  induction n generalizing s with
  | zero => simp
  | succ n ihn => rw [Function.iterate_succ_apply]; exact le_trans (ih s) (ihn _)

