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


lemma run_QInv (O : Oracle) (p : Prog) (st : State) (h : QInv st) : QInv (run O p st) := by
  induction p generalizing st with
  | skip => exact QInv_up' h (by omega)
  | assign i e =>
      have h1 := evalE_QInv O e st h
      simp only [run_assign]
      exact QInv_up h1 (by omega)
  | seq p q ihp ihq => exact ihq _ (ihp _ h)
  | ite c t f iht ihf =>
      have h1 := evalE_QInv O c st h
      rw [run_ite]
      have h2 : QInv { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } :=
        QInv_up' h1 (by omega)
      split
      · exact ihf _ h2
      · exact iht _ h2
  | loop c body ih =>
      have h1 := evalE_QInv O c st h
      rw [run_loop]
      have h2 : QInv { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } :=
        QInv_up' h1 (by omega)
      exact iter_QInv O body ih _ _ h2

/-! ### Locality -/

