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


lemma evalE_local {O O' : Oracle} (e : Expr) (st : State)
    (h : ∀ q ∈ (evalE O e st).2.qs, O' q = O q) : evalE O' e st = evalE O e st := by
  induction e generalizing st with
  | var i => simp
  | lit s => simp
  | cat a b iha ihb =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        exact (evalE_qs_mono O b (evalE O a st).2) hq
      have hb : evalE O' b (evalE O a st).2 = evalE O b (evalE O a st).2 :=
        ihb _ (fun q hq => h q hq)
      simp only [evalE_cat, ha, hb]
  | smash a b iha ihb =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        exact (evalE_qs_mono O b (evalE O a st).2) hq
      have hb : evalE O' b (evalE O a st).2 = evalE O b (evalE O a st).2 :=
        ihb _ (fun q hq => h q hq)
      simp only [evalE_smash, ha, hb]
  | tail a iha =>
      have ha : evalE O' a st = evalE O a st := iha st (fun q hq => h q hq)
      simp only [evalE_tail, ha]
  | eqE a b iha ihb =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        exact (evalE_qs_mono O b (evalE O a st).2) hq
      have hb : evalE O' b (evalE O a st).2 = evalE O b (evalE O a st).2 :=
        ihb _ (fun q hq => h q hq)
      simp only [evalE_eqE, ha, hb]
  | query a iha =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        simp only [evalE_query]
        exact List.mem_cons_of_mem _ hq
      have hO : O' (evalE O a st).1 = O (evalE O a st).1 := by
        refine h _ ?_
        simp only [evalE_query]
        exact List.mem_cons_self
      simp only [evalE_query, ha, hO]

