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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is a plain block comment and is repeated as a
-- module docstring after the import.)

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

lemma two_pow_sub_one_eq_one (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    ((2 : ZMod p)) ^ (p - 1) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ZMod.pow_card_sub_one_eq_one ?_
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h2
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

/-- **Fermat-type divisibility for Cullen numbers**: every odd prime `p` divides the
Cullen number `C (p - 1)`. -/
