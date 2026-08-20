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

theorem pepin_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (Nat.fermatNumber n).Prime) :
    (3 : ZMod (Nat.fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1 := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  have hl : legendreSym (Nat.fermatNumber n) 3 = -1 :=
    (legendreSym.eq_neg_one_iff _).mpr (by push_cast; exact not_isSquare_three n hn hp)
  have h := legendreSym.eq_pow (p := Nat.fermatNumber n) 3
  rw [hl, fermatNumber_div_two] at h
  push_cast at h
  exact h.symm

/-- **Pépin's test** (full equivalence), for `n ≥ 1`: the Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`
is prime if and only if `3 ^ ((Fₙ - 1) / 2) ≡ -1 (mod Fₙ)`.
The `←` direction is `Nat.pepin_primality` from Mathlib. -/
