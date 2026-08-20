import Mathlib
/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header placement: Lean 4 requires `import` commands to be the very first
commands in a file, and a `/-! ... -/` module doc comment counts as a command.  The
requested header is therefore reproduced verbatim immediately after the single
`import Mathlib` line.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- **Closed form for the Catalan numbers.**
The `n`-th Catalan number equals `C(2n, n) / (n + 1)` (natural-number division,
which here is exact since `n + 1 ∣ C(2n, n)`).

This is Mathlib's `catalan_eq_centralBinom_div`, unfolded through
`Nat.centralBinom n = (2 * n).choose n`. -/

theorem succ_mul_catalan_closed (n : ℕ) : (n + 1) * catalan n = (2 * n).choose n :=
  succ_mul_catalan_eq_centralBinom n

/-- The closed form over the rationals, where the division is genuine field division. -/
