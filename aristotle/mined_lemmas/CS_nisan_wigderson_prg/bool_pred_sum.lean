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

lemma bool_pred_sum (g : Bool → Bool) (c : Bool) :
    ∑ ui : Bool, bval ((if g ui then ui else !ui) == c)
      = 1 + 2 * bval (g c) - ∑ v : Bool, bval (g v) := by
  rw [Fintype.sum_bool, Fintype.sum_bool]
  cases c <;> cases hgt : g true <;> cases hgf : g false <;> simp [bval, hgt, hgf] <;> norm_num

/-! ### The main averaging identity -/

