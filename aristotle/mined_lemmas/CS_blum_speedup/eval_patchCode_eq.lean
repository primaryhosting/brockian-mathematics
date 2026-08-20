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


theorem eval_patchCode_eq (hr : Computable r) {n L : ℕ}
    (hL : ∀ x, L ≤ x → acc M r (selfCode M hr) n x = acc M r (selfCode M hr) 0 x) :
    eval (patchCode (selfCode M hr) n L) = fun y => Part.some (bigFun M hr y) := by
  funext y
  rcases Nat.lt_or_ge y L with h | h
  · rw [eval_patch_self_lt M hr n L y h, acc_zero_eq]
  · rw [eval_patch_self M hr n L y h, hL y h, acc_zero_eq]

end SelfRef

/-! ## A monotone majorant of the speedup factor -/

/-- The monotone majorant `rSup r m = max_{k ≤ m} r k`. -/
