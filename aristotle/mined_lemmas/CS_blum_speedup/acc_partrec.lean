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


theorem acc_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => acc M r q.1 q.2.1 q.2.2 := by
  have hx : Computable fun q : Code × ℕ × ℕ => q.2.2 := Computable.snd.comp Computable.snd
  have harg0 : Computable fun q : Code × ℕ × ℕ => (q.1, q.2.1, q.2.2, (0:ℕ)) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.snd.comp Computable.snd).pair (Computable.const 0)))
  have hg := (contrib_partrec M hr).comp harg0
  have hargS : Computable fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) =>
      (p.1.1, p.1.2.1, p.1.2.2, p.2.1 + 1) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
          (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))))
  have hcS := (contrib_partrec M hr).comp hargS
  have hmax : Computable₂ fun (p : (Code × ℕ × ℕ) × (ℕ × ℕ)) (w : ℕ) => max p.2.2 w :=
    Primrec.nat_max.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      Computable.snd
  have hh := Partrec.map hcS hmax
  have h := Partrec.nat_rec (f := fun q : Code × ℕ × ℕ => q.2.2)
    (g := fun q : Code × ℕ × ℕ => contrib M r q.1 q.2.1 q.2.2 0)
    (h := fun (q : Code × ℕ × ℕ) (p : ℕ × ℕ) =>
      (contrib M r q.1 q.2.1 q.2.2 (p.1 + 1)).map fun w => max p.2 w)
    hx hg hh
  exact h

