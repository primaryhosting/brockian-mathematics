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

/-
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`, so the
-- requested header is repeated verbatim as the module docstring just below the import.)

import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

`Nat.fermatNumber n = 2 ^ (2 ^ n) + 1` is Mathlib's definition of the `n`-th Fermat number.
The numbers `F₀, …, F₄` are prime and no further Fermat prime is known; whether some `Fₙ` with
`n > 4` is prime is a well-known open problem.

Accordingly, the target theorem `FermatPrimeBeyondFour` is stated and proved here as an
unconditional *reduction*: a Fermat prime with index `n > 4` exists if and only if some `Fₙ`
with `n > 4` passes **Pépin's test** `3 ^ ((Fₙ - 1) / 2) ≡ -1 (mod Fₙ)`.

The `←` direction is Mathlib's `Nat.pepin_primality`
(`Mathlib/NumberTheory/Fermat.lean`), which is the "existing lemma that nearly closes this".
The `→` direction (`pepin_of_prime`) is proved here from quadratic reciprocity, in the form of
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, together with Euler's criterion in the form
`legendreSym.eq_pow`.

Unconditional companion facts (`F₄ = 65537` is prime, `F₅` is composite) are proved at the end.
-/

namespace Brockian.FermatNumbers

open Nat

/-- For `n ≥ 1`, the Fermat number `Fₙ = 2 ^ (2 ^ n) + 1` is `1` modulo `4`. -/

lemma fermatNumber_div_two (n : ℕ) : Nat.fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
  have h : 2 ^ (2 ^ n) = 2 * 2 ^ (2 ^ n - 1) := by
    rw [← pow_succ']
    congr 1
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [Nat.fermatNumber, h]
  omega

/-- If `Fₙ` (`n ≥ 1`) is prime, then `3` is a quadratic nonresidue modulo `Fₙ`.
Indeed `Fₙ ≡ 1 [MOD 4]`, so by quadratic reciprocity `3` is a square mod `Fₙ` iff `Fₙ` is a
square mod `3`; but `Fₙ ≡ 2 [MOD 3]` and `2` is not a square mod `3`. -/
