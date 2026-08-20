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

import Mathlib

/-!
## Overview

The Fermat numbers are `Fₙ = 2 ^ (2 ^ n) + 1` (`Nat.fermatNumber` in Mathlib).  The
five numbers `F₀ = 3`, `F₁ = 5`, `F₂ = 17`, `F₃ = 257`, `F₄ = 65537` are prime, and no other
Fermat prime is known; whether some `Fₙ` with `n > 4` is prime is a famous open question.

This file does not settle that question.  Instead it gives a *Lean-checked conditional
reduction*: the main theorem `Brockian.FermatNumbers.FermatPrimeBeyondFour` shows that for
every `n > 4`,

  `Fₙ` is prime  ↔  `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`,

i.e. **Pépin's test** is not only sufficient but also necessary.  The sufficiency direction is
Mathlib's `Nat.pepin_primality'`; the necessity direction (`pepin_necessity` below) is proved
here from quadratic reciprocity: `Fₙ ≡ 1 [MOD 4]` and `Fₙ ≡ 2 [MOD 3]` for `n ≥ 1`, so `3` is a
quadratic non-residue modulo a prime `Fₙ`, and Euler's criterion gives the claim.

Consequently the existence of a Fermat prime beyond `F₄` is equivalent to a purely
computational statement (`exists_fermatPrime_beyond_four_iff_pepin`).

We also record the classical numerical facts framing the problem: `F₀, …, F₄` are prime while
`F₅, F₆, F₇` are composite.
-/

namespace Brockian.FermatNumbers

open Nat ZMod

/-! ### The known Fermat primes and the first composite Fermat numbers -/


theorem reduces it, for each individual `n > 4`, to the modular criterion of Pépin:
`Fₙ` is prime if and only if `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`.

The hypothesis `4 < n` is what the statement of the problem asks for; the proof in fact only
uses `0 < n` (see `pepin_test`). -/
