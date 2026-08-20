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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRepr n` says that `4/n` is a sum of three positive unit fractions. -/

theorem repr_of_exists_prime_factor {n : ℕ} (hn : 2 ≤ n)
    (hex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 12 ≠ 1) : ErdosStrausRepr n := by
  obtain ⟨p, hp, hdvd, hmod⟩ := hex
  exact (repr_of_prime_of_mod_twelve_ne_one hp hmod).of_dvd hp.pos (by omega) hdvd

/-! ### Explicit representations for the small primes `≡ 1 [MOD 12]` -/

