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


lemma evalE_cost_mono (O : Oracle) (e : Expr) (st : State) :
    st.cost ≤ (evalE O e st).2.cost := by
  induction e generalizing st with
  | var i => simp
  | lit s => simp
  | cat a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_cat]; omega
  | smash a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_smash]; omega
  | tail a iha => have h1 := iha st; simp only [evalE_tail]; omega
  | eqE a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_eqE]; omega
  | query a iha => have h1 := iha st; simp only [evalE_query]; omega

