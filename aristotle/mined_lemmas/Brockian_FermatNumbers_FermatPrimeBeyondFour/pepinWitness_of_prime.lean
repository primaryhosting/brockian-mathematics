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

theorem pepinWitness_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (Nat.fermatNumber n).Prime) :
    PepinWitness n := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  set p := Nat.fermatNumber n with hpdef
  have hleg : legendreSym p 3 = -1 :=
    legendreSym_three_eq_neg_one p (fermatNumber_mod_four n hn) (fermatNumber_mod_three n hn)
  -- Euler's criterion
  have heuler : ((legendreSym p 3 : ℤ) : ZMod p) = ((3 : ℤ) : ZMod p) ^ (p / 2) :=
    legendreSym.eq_pow (p := p) 3
  rw [hleg, fermatNumber_div_two n] at heuler
  unfold PepinWitness
  rw [← hpdef]
  push_cast at heuler
  rw [← heuler]

/-- **Pépin's test.** For `n ≥ 1`, the `n`-th Fermat number is prime if and only if
Pépin's condition `3 ^ ((Fₙ - 1) / 2) = -1 (mod Fₙ)` holds. -/
