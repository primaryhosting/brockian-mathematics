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


theorem maxK_partrec (M : BlumMeasure) :
    Partrec fun q : Code × ℕ × ℕ => maxK M q.1 q.2.1 q.2.2 := by
  have hsnd : Computable fun q : Code × ℕ × ℕ => q.2 := Computable.snd
  have hm : Computable fun q : Code × ℕ × ℕ => q.2.1 := Computable.fst.comp hsnd
  have hu : Computable fun q : Code × ℕ × ℕ => q.2.2 := Computable.snd.comp hsnd
  have hC : Computable fun q : Code × ℕ × ℕ => q.1 := Computable.fst
  have hpatch00 := patchCode_primrec.to_comp.comp (hC.pair (hm.pair (Computable.const (0 : ℕ))))
  have hpatch0 : Computable fun q : Code × ℕ × ℕ => patchCode q.1 q.2.1 0 := hpatch00
  have hg0 := (cost_partrec M).comp hpatch0 hu
  have hg : Partrec fun q : Code × ℕ × ℕ => M.cost (patchCode q.1 q.2.1 0) q.2.2 := hg0
  have hfst : Computable fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) => p.1 := Computable.fst
  have hsnd2 : Computable fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) => p.2 := Computable.snd
  have hC2 := hC.comp hfst
  have hm2 := hm.comp hfst
  have hu2 := hu.comp hfst
  have hj := (Computable.fst : Computable fun s : ℕ × ℕ => s.1).comp hsnd2
  have hv := (Computable.snd : Computable fun s : ℕ × ℕ => s.2).comp hsnd2
  have hpatchS := patchCode_primrec.to_comp.comp
    (hC2.pair (hm2.pair (Primrec.succ.to_comp.comp hj)))
  have hcostS0 := (cost_partrec M).comp hpatchS hu2
  have hcostS : Partrec fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) =>
      M.cost (patchCode p.1.1 p.1.2.1 (p.2.1 + 1)) p.1.2.2 := hcostS0
  have hmax0 := Primrec.nat_max.to_comp.comp
    (hv.comp (Computable.fst : Computable fun z : ((Code × ℕ × ℕ) × (ℕ × ℕ)) × ℕ => z.1))
    (Computable.snd : Computable fun z : ((Code × ℕ × ℕ) × (ℕ × ℕ)) × ℕ => z.2)
  have hmax : Computable₂ fun (p : (Code × ℕ × ℕ) × (ℕ × ℕ)) (w : ℕ) => max p.2.2 w := hmax0
  have hh := Partrec.map hcostS hmax
  have h := Partrec.nat_rec (f := fun q : Code × ℕ × ℕ => q.2.2)
    (g := fun q : Code × ℕ × ℕ => M.cost (patchCode q.1 q.2.1 0) q.2.2)
    (h := fun (q : Code × ℕ × ℕ) (p : ℕ × ℕ) =>
      (M.cost (patchCode q.1 q.2.1 (p.1 + 1)) q.2.2).map (fun w => max p.2 w))
    hu hg hh
  exact h

/-- The bound used at stage `u` for the index `i`: `r` applied to the largest cost of a
patched level-`(i+1)` program at `u`. -/
