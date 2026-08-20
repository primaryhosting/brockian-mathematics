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


theorem rSup_computable {r : ℕ → ℕ} (hr : Computable r) : Computable (rSup r) := by
  have h := Computable.nat_rec (f := fun m : ℕ => m) (g := fun _ : ℕ => r 0)
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => max p.2 (r (p.1+1))) Computable.id (Computable.const (r 0))
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hr.comp (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))))
  exact h

/-! ## Blum's speedup theorem -/

/-- **Blum's speedup theorem.**  For *every* Blum complexity measure `M` and every computable
speedup factor `r` there is a computable function `f` such that every program `e` computing `f`
is beaten by another program `e'` for the same function: on almost every input, the cost of `e`
is at least `r` applied to the cost of `e'`.  Hence `f` has no fastest program. -/
