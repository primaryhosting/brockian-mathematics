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


theorem stepGraph_computable :
    Computable fun p : (Code × ℕ) × ℕ => stepGraph p.1.1 p.1.2 p.2 := by
  have h1 : Primrec fun p : (Code × ℕ) × ℕ => evaln p.2 p.1.1 p.1.2 :=
    primrec_evaln.comp (((Primrec.snd).pair (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst))
  have hpred : Primrec fun p : (Code × ℕ) × ℕ => p.2 - 1 := Primrec.pred.comp Primrec.snd
  have h2 : Primrec fun p : (Code × ℕ) × ℕ => evaln (p.2 - 1) p.1.1 p.1.2 :=
    primrec_evaln.comp ((hpred.pair (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst))
  have hs1 : PrimrecPred fun p : (Code × ℕ) × ℕ => (evaln p.2 p.1.1 p.1.2).isSome = true :=
    ⟨fun _ => inferInstance, by simpa using (Primrec.option_isSome.comp h1)⟩
  have hs2 : PrimrecPred fun p : (Code × ℕ) × ℕ =>
      (evaln (p.2 - 1) p.1.1 p.1.2).isSome = false := by
    refine ⟨fun _ => inferInstance, ?_⟩
    refine (Primrec.not.comp (Primrec.option_isSome.comp h2)).of_eq ?_
    intro a; cases h : evaln (a.2 - 1) a.1.1 a.1.2 <;> simp [h]
  have heq : PrimrecPred fun p : (Code × ℕ) × ℕ => p.2 = 0 :=
    Primrec.eq.comp (Primrec.snd) (Primrec.const (0 : ℕ))
  obtain ⟨_, h⟩ := hs1.and (heq.or hs2)
  exact h.to_comp.of_eq (fun p => by simp [stepGraph])

