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


theorem acc_congr {n m x : ℕ} (h : ∀ i ≤ x, contrib M r C n x i = contrib M r C m x i) :
    acc M r C n x = acc M r C m x := by
  have key : ∀ j ≤ x, (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C n x 0)
      (fun k ih => ih.bind fun v => (contrib M r C n x (k+1)).map fun w => max v w) j)
      = (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C m x 0)
      (fun k ih => ih.bind fun v => (contrib M r C m x (k+1)).map fun w => max v w) j) := by
    intro j
    induction j with
    | zero => intro _; exact h 0 (Nat.zero_le x)
    | succ k ih =>
      intro hk
      show Part.bind _ _ = Part.bind _ _
      rw [ih (by omega), h (k+1) hk]
  exact key x le_rfl

