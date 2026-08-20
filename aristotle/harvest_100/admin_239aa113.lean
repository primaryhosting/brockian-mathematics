/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The required header is kept at the very top of the file; Lean does not
-- allow a module docstring `/-! ... -/` to precede the `import` command,
-- so it is written as an ordinary block comment.)

import Mathlib

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

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial
`p` (i.e. one of positive degree) has a complex root. -/
theorem fta_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) :
    ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

end Math

