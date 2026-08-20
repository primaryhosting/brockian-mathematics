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


lemma run_cost_mono (O : Oracle) (p : Prog) (st : State) :
    st.cost ≤ (run O p st).cost := by
  induction p generalizing st with
  | skip => simp
  | assign i e => have h1 := evalE_cost_mono O e st; simp only [run_assign]; omega
  | seq p q ihp ihq => have h1 := ihp st; have h2 := ihq (run O p st); simp only [run_seq]; omega
  | ite c t f iht ihf =>
      have h1 := evalE_cost_mono O c st
      rw [run_ite]
      split
      · have h2 := ihf { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
        simp only at h2; omega
      · have h2 := iht { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
        simp only at h2; omega
  | loop c body ih =>
      have h1 := evalE_cost_mono O c st
      rw [run_loop]
      have h2 := iter_cost_mono O body ih (evalE O c st).1.length
        { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
      simp only at h2; omega

/-! ### Monotonicity of the query list -/

