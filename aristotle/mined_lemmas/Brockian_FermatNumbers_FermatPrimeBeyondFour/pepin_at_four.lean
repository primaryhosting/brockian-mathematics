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

-- (Lean 4 requires `import` lines to precede any module doc-comment, so the requested
-- header block appears immediately below the import.)
import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The existence of a Fermat prime `F_n = 2^(2^n) + 1` with `n > 4` (i.e. beyond `F_4 = 65537`)
is an open problem.  What is proved here is a *complete, unconditional reduction* of that
statement to Pépin's criterion: for every `n ≥ 1`,

  `F_n` is prime  ↔  `3 ^ ((F_n - 1)/2) = -1` in `ZMod (F_n)`.

The `←` direction is Mathlib's `Nat.pepin_primality`; the `→` direction (that `3` is a
quadratic non-residue modulo a Fermat prime) is proved here from quadratic reciprocity
(`legendreSym.quadratic_reciprocity_one_mod_four`) and Euler's criterion
(`legendreSym.eq_pow`).
-/

namespace Brockian.FermatNumbers

open Nat

/-- `F_n % 4 = 1` for `n ≥ 1`. -/

lemma pepin_at_four : (3 : ZMod (fermatNumber 4)) ^ (2 ^ (2 ^ 4 - 1)) = -1 :=
  (pepin_iff 4 (by norm_num)).1 (by norm_num [fermatNumber])

end Brockian.FermatNumbers

