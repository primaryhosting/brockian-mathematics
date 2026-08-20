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


theorem noElig_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => noElig M r q.1 q.2.1 q.2.2 := by
  have hx : Computable fun q : Code × ℕ × ℕ => q.2.2 :=
    Computable.snd.comp Computable.snd
  have hg : Partrec fun _ : Code × ℕ × ℕ => (Part.some true) := Computable.const true
  have hcond : Computable fun p : (Code × ℕ × ℕ) × (ℕ × Bool) =>
      decide (p.2.1 < p.1.2.1) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun p : (Code × ℕ × ℕ) × (ℕ × Bool) => p.2.1 < p.1.2.1 :=
      Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact hh.to_comp.of_eq (fun p => by simp)
  have hbr1 : Partrec fun p : (Code × ℕ × ℕ) × (ℕ × Bool) => (Part.some p.2.2) :=
    Computable.snd.comp Computable.snd
  have harg : Computable fun p : (Code × ℕ × ℕ) × (ℕ × Bool) => (p.1.1, p.1.2.1, p.2.1) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd))
  have helig := (elig_partrec M hr).comp harg
  have hmap : Computable₂ fun (p : (Code × ℕ × ℕ) × (ℕ × Bool)) (e : Bool) => p.2.2 && !e :=
    Primrec.and.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (Primrec.not.to_comp.comp Computable.snd)
  have hbr2 := Partrec.map helig hmap
  have hh := Partrec.cond hcond hbr1 hbr2
  have h := Partrec.nat_rec (f := fun q : Code × ℕ × ℕ => q.2.2)
    (g := fun _ : Code × ℕ × ℕ => (Part.some true))
    (h := fun (q : Code × ℕ × ℕ) (p : ℕ × Bool) =>
      bif decide (p.1 < q.2.1) then Part.some p.2
        else (elig M r q.1 q.2.1 p.1).map fun e => p.2 && !e)
    hx hg hh
  exact h

