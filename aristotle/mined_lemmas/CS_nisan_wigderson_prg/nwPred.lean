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

def nwPred (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) (i : Fin m)
    (S : Finset (Fin n)) (ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => if T (nwStr f i (maskMerge S x z) tail ui) then ui else !ui

/-- The acceptance probability of the test `T` on the `k`-th hybrid distribution. -/
