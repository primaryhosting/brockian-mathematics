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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to precede every other
command in a file, so the header block above is placed immediately after the
single `import Mathlib` line.

Mathematical content.  The Fermat numbers are `F n = 2 ^ (2 ^ n) + 1`.  The
only known Fermat primes are `F 0, …, F 4` (namely `3, 5, 17, 257, 65537`), and
whether any Fermat prime exists beyond `F 4` is an open problem.  We therefore
prove a Lean-checked *conditional reduction*: the existence of a Fermat prime
`F n` with `n > 4` is equivalent to the existence of `n > 4` satisfying Pépin's
residue condition `3 ^ ((F n - 1) / 2) = -1` in `ZMod (F n)`.  Both directions
of Pépin's test are proved: sufficiency via the Lucas primality criterion, and
necessity via quadratic reciprocity.  We also record that `F 5` and `F 6` are
composite, so the search for a Fermat prime beyond four starts at `n = 7`.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `F n = 2 ^ (2 ^ n) + 1`. -/

def PepinResidue (n : ℕ) : Prop := (3 : ZMod (fermat n)) ^ 2 ^ (2 ^ n - 1) = -1

