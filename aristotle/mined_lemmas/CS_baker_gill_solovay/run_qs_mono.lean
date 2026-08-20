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


lemma run_qs_mono (O : Oracle) (p : Prog) (st : State) : st.qs ⊆ (run O p st).qs := by
  induction p generalizing st with
  | skip => simp
  | assign i e => simpa using evalE_qs_mono O e st
  | seq p q ihp ihq => exact (ihp st).trans (ihq (run O p st))
  | ite c t f iht ihf =>
      have h1 := evalE_qs_mono O c st
      rw [run_ite]
      split
      · exact h1.trans (ihf _)
      · exact h1.trans (iht _)
  | loop c body ih =>
      have h1 := evalE_qs_mono O c st
      rw [run_loop]
      exact h1.trans (iter_qs_mono O body ih _ _)

/-! ### Cost shifting -/

/-- Shift the accumulated cost of a state. -/
