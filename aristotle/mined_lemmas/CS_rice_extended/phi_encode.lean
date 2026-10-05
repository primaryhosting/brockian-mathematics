/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
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

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- `phi n` is the partial function computed by the program with index `n`
(the standard enumeration of partial recursive functions, obtained from the
Gödel numbering of `Nat.Partrec.Code`). -/

theorem phi_encode (c : Code) : phi (Encodable.encode c) = Code.eval c := by
  simp [phi, Denumerable.ofNat_encode]

/-- Every partial recursive function has an index. -/
