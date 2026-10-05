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

lemma nwPred_local (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) (i : Fin m)
    (S : Finset (Fin n)) (ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool)
    (x y : Fin n → Bool) (h : ∀ j ∈ S, x j = y j) :
    nwPred f T i S ui tail z x = nwPred f T i S ui tail z y := by
  have : maskMerge S x z = maskMerge S y z := by
    funext j
    by_cases hj : j ∈ S
    · simp [maskMerge, hj, h j hj]
    · simp [maskMerge, hj]
  simp [nwPred, this]

/-! ### Endpoints of the hybrid sequence -/

