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


theorem bound_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => bound M r q.1 q.2.1 q.2.2 := by
  have hC : Computable fun q : Code × ℕ × ℕ => q.1 := Computable.fst
  have hi : Computable fun q : Code × ℕ × ℕ => q.2.1 :=
    Computable.fst.comp (Computable.snd : Computable fun q : Code × ℕ × ℕ => q.2)
  have hu : Computable fun q : Code × ℕ × ℕ => q.2.2 :=
    Computable.snd.comp (Computable.snd : Computable fun q : Code × ℕ × ℕ => q.2)
  have harg0 := hC.pair ((Primrec.succ.to_comp.comp hi).pair hu)
  have harg : Computable fun q : Code × ℕ × ℕ => (q.1, q.2.1 + 1, q.2.2) := harg0
  have hmk0 := (maxK_partrec M).comp harg
  have hmk : Partrec fun q : Code × ℕ × ℕ => maxK M q.1 (q.2.1 + 1) q.2.2 := hmk0
  have hr2 : Computable₂ fun (_ : Code × ℕ × ℕ) (v : ℕ) => r v := hr.comp Computable.snd
  have h := Partrec.map hmk hr2
  exact h

/-! ## Eligibility and cancellation -/

/-- Index `i` is *eligible* at stage `y` if the cost of program `i` on input `y` is at most the
bound attached to `i` at that stage. -/
