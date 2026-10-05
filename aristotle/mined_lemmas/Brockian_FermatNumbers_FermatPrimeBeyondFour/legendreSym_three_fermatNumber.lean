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

namespace Brockian.FermatNumbers

private instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The Pépin condition for the `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/

lemma legendreSym_three_fermatNumber (n : ℕ) (hn : 1 ≤ n)
    (hp : Fact (Nat.Prime (Nat.fermatNumber n))) :
    legendreSym (Nat.fermatNumber n) 3 = -1 := by
  have hrec : legendreSym 3 (Nat.fermatNumber n : ℤ) = legendreSym (Nat.fermatNumber n) (3 : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (fermatNumber_mod_four n hn) (by norm_num)
  have hmod : (Nat.fermatNumber n : ℤ) % ((3 : ℕ) : ℤ) = 2 := by
    have h := fermatNumber_mod_three n hn
    push_cast
    omega
  rw [← hrec, legendreSym.mod, hmod]
  decide

/-- **Converse of Pépin's test.** If the Fermat number `Fₙ` (`n ≥ 1`) is prime, then it satisfies
the Pépin condition `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
