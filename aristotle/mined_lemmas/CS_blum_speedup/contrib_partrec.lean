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


theorem contrib_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ × ℕ => contrib M r q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hcond : Computable fun q : Code × ℕ × ℕ × ℕ => decide (q.2.1 ≤ q.2.2.2) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun q : Code × ℕ × ℕ × ℕ => q.2.1 ≤ q.2.2.2 :=
      Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact hh.to_comp.of_eq (fun p => by simp)
  have harg : Computable fun q : Code × ℕ × ℕ × ℕ => (q.1, q.2.2.2, q.2.2.1) :=
    Computable.fst.pair
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hcanc := (cancelAt_partrec M hr).comp harg
  have hb : Computable fun p : (Code × ℕ × ℕ × ℕ) × Bool => p.2 := Computable.snd
  have hcode : Computable fun p : (Code × ℕ × ℕ × ℕ) × Bool => ofNat Code p.1.2.2.2 :=
    (Computable.ofNat Code).comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hx : Computable fun p : (Code × ℕ × ℕ × ℕ) × Bool => p.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hev := eval_part.comp hcode hx
  have hsucc : Computable₂ fun (_ : (Code × ℕ × ℕ × ℕ) × Bool) (v : ℕ) => v + 1 :=
    Primrec.succ.to_comp.comp Computable.snd
  have hthen1 := Partrec.map hev hsucc
  have helse1 : Partrec fun _ : (Code × ℕ × ℕ × ℕ) × Bool => (Part.some 0) :=
    Computable.const 0
  have hinner := Partrec.cond hb hthen1 helse1
  have hthen := Partrec.bind hcanc hinner.to₂
  have helse : Partrec fun _ : Code × ℕ × ℕ × ℕ => (Part.some 0) := Computable.const 0
  have h := Partrec.cond hcond hthen helse
  exact h

