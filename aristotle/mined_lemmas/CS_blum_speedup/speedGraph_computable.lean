/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/


theorem speedGraph_computable (hr : Computable r) :
    Computable fun p : (Code × ℕ) × ℕ => speedGraph r p.1.1 p.1.2 p.2 := by
  have hpi : Computable fun p : (Code × ℕ) × ℕ => padIdx p.1.1 p.1.2 :=
    (padIdx_primrec.comp Primrec.fst).to_comp
  have hx : Computable fun p : (Code × ℕ) × ℕ => p.1.2 := (Primrec.snd.comp Primrec.fst).to_comp
  have hm : Computable fun p : (Code × ℕ) × ℕ => p.2 := Computable.snd
  have hA : Computable fun p : (Code × ℕ) × ℕ => costA r (padIdx p.1.1 p.1.2) p.1.2 :=
    (costA_computable hr).comp (hpi.pair hx)
  have hBig : Computable fun p : (Code × ℕ) × ℕ => bigB r p.1.2 := (bigB_computable hr).comp hx
  have hcond : Computable fun p : (Code × ℕ) × ℕ => padLe p.1.1 p.1.2 :=
    (padLe_primrec.comp Primrec.fst).to_comp
  have hleft : Computable fun p : (Code × ℕ) × ℕ =>
      decide (p.2 = costA r (padIdx p.1.1 p.1.2) p.1.2) :=
    computable_decide_eq.comp (hm.pair hA)
  have hstepArg : Computable fun p : (Code × ℕ) × ℕ => ((p.1.1, p.1.2), p.2 - bigB r p.1.2) :=
    Computable.fst.pair (Primrec.nat_sub.to_comp.comp hm hBig)
  have hstep : Computable fun p : (Code × ℕ) × ℕ =>
      stepGraph p.1.1 p.1.2 (p.2 - bigB r p.1.2) :=
    stepGraph_computable.comp hstepArg
  have hright : Computable fun p : (Code × ℕ) × ℕ =>
      (decide (bigB r p.1.2 ≤ p.2) && stepGraph p.1.1 p.1.2 (p.2 - bigB r p.1.2)) :=
    Primrec.and.to_comp.comp (computable_decide_le.comp (hBig.pair hm)) hstep
  exact Computable.cond hcond hleft hright

/-- The Blum complexity measure witnessing speedup. -/
