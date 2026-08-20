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


theorem patchFun_partrec : Partrec₂ patchFun := by
  have h0 : Computable fun p : (Code × ℕ × ℕ) × ℕ => p.1.1 := Computable.fst.comp Computable.fst
  have hy : Computable fun p : (Code × ℕ × ℕ) × ℕ => p.2 := Computable.snd
  have harg1 := Primrec₂.natPair.to_comp.comp (Computable.const (0 : ℕ)) hy
  have harg2 := Primrec₂.natPair.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst)) hy
  have h1 := eval_part.comp h0 harg1
  have h2 := eval_part.comp h0 harg2
  have hcond : Computable fun p : (Code × ℕ × ℕ) × ℕ => decide (p.2 < p.1.2.2) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun p : (Code × ℕ × ℕ) × ℕ => p.2 < p.1.2.2 :=
      Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact hh.to_comp.of_eq (fun p => by simp)
  exact Partrec.cond hcond h1 h2

