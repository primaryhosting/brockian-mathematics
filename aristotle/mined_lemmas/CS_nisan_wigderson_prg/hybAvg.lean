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

noncomputable def hybAvg (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (k : ℕ) : ℝ :=
  (∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f k x u))) / ((2 : ℝ) ^ n * 2 ^ m)

/-! ### Basic counting lemmas -/

