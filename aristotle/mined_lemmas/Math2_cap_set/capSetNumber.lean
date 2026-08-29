/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

namespace Math2

open Finset Filter Asymptotics

/-- The number of points of `𝔽₃ⁿ`, where `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`. -/

noncomputable def capSetNumber (n : ℕ) : ℕ :=
  addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))

/-- **The cap set theorem**: subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression
have size `o(3ⁿ)`.

Here `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`, a three-term arithmetic progression is a triple
`a, b, c` with `a + c = b + b` (equivalently `a + b + c = 0` in characteristic three), and
`capSetNumber n` is the largest size of a subset of `𝔽₃ⁿ` containing no non-trivial such triple.

The proof deduces the statement from Roth's theorem for finite abelian groups, `roth_3ap_theorem`,
applied to the group `𝔽₃ⁿ`, whose cardinality `3ⁿ` tends to infinity. -/
