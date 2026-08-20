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


theorem iter_computable {r : ℕ → ℕ} (hr : Computable r) : Computable fun k : ℕ => r^[k] 0 := by
  have h : Computable fun k : ℕ => Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => r ih) k := by
    refine Computable.nat_rec (f := fun k : ℕ => k) (g := fun _ : ℕ => (0 : ℕ))
      (h := fun _ p => r p.2) Computable.id (Computable.const 0) ?_
    exact hr.comp (Computable.snd.comp Computable.snd)
  refine h.of_eq (fun k => ?_)
  induction k with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ← ih]

end CS

import RequestProject.Base

/-!
# Blum's speedup theorem for an arbitrary Blum complexity measure

This file develops the construction behind Blum's speedup theorem: for *every* Blum complexity
measure and every computable speedup factor `r` there is a computable `f` such that every
program for `f` can be sped up by the factor `r`, almost everywhere, by another program for `f`.
-/

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

set_option maxHeartbeats 1000000

namespace CS

/-! ## Tools attached to a Blum measure -/

/-- The cost function of a Blum measure is partial computable. -/
