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

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- repeated below verbatim as this module's docstring.)
import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

open Nat

/-- Pépin's condition for the `n`-th Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/

theorem prime_fermatNumber_iff_pepinWitness (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fermatNumber n).Prime ↔ PepinWitness n :=
  ⟨pepinWitness_of_prime n hn, fun h => Nat.pepin_primality n h⟩

/-- The first five Fermat numbers `F₀ = 3, F₁ = 5, F₂ = 17, F₃ = 257, F₄ = 65537` are prime. -/
