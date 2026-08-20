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


lemma evalE_QInv (O : Oracle) (e : Expr) (st : State) (h : QInv st) : QInv (evalE O e st).2 := by
  induction e generalizing st with
  | var i => exact QInv_up' h (by omega)
  | lit s => exact QInv_up' h (by omega)
  | cat a b iha ihb =>
      simp only [evalE_cat]
      exact QInv_up' (ihb _ (iha _ h)) (by omega)
  | smash a b iha ihb =>
      simp only [evalE_smash]
      exact QInv_up' (ihb _ (iha _ h)) (by omega)
  | tail a iha =>
      simp only [evalE_tail]
      exact QInv_up' (iha _ h) (by omega)
  | eqE a b iha ihb =>
      simp only [evalE_eqE]
      exact QInv_up' (ihb _ (iha _ h)) (by omega)
  | query a iha =>
      have h1 := iha _ h
      simp only [evalE_query]
      refine ⟨fun q hq => ?_, ?_⟩
      · simp only at hq ⊢
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have := h1.1 q hq; omega
      · simp only [List.length_cons]
        have := h1.2
        omega

