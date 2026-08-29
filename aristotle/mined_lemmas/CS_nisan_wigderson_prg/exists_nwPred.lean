import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Finset

variable {n m : ℕ}

/-- The real value of a boolean: `1` for `true`, `0` for `false`. -/

lemma exists_nwPred (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (S : Finset (Fin n)) (i : Fin m)
    (hf : ∀ x y : Fin n → Bool, (∀ j ∈ S, x j = y j) → f i x = f i y) :
    ∃ (ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool),
      1 / 2 + (hybAvg f T ((i : ℕ) + 1) - hybAvg f T (i : ℕ))
        ≤ unifAvg (fun x => bval (nwPred f T i S ui tail z x == f i x)) := by
  obtain ⟨a, ha⟩ := exists_ge_unifAvg (fun a : Bool × (Fin m → Bool) × (Fin n → Bool) =>
    unifAvg (fun x => bval (nwPred f T i S a.1 a.2.1 a.2.2 x == f i x)))
  rw [nwPred_avg f T S i hf] at ha
  exact ⟨a.1, a.2.1, a.2.2, ha⟩

/-! ### Locality of the predictor -/

