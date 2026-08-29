import Mathlib
/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
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

namespace Frontier

open Ordinal

/-! ### Arithmetic preliminaries -/


theorem Gv_lt_opow (b : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hw : (b : Ordinal) ≤ w) (n k : ℕ)
    (h : n < b ^ k) : Gv b w n < w ^ (Gv b w k) :=
  (Gv_key_and_mono b w hb hw n).1 k h

