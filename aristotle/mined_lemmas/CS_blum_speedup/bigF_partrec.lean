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


theorem bigF_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec₂ fun (C : Code) (a : ℕ) => bigF M r C a := by
  have harg : Computable fun p : Code × ℕ => (p.1, p.2.unpair.1, p.2.unpair.2) :=
    Computable.fst.pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp.pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
  have h := (acc_partrec M hr).comp harg
  exact h

/-! ## Elementary facts about the construction -/

section Facts

variable {M : BlumMeasure} {r : ℕ → ℕ} {C : Code}

