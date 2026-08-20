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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-- The *spectral (prime-pair correlation) count* of `n`: the number of ways of writing
`n = p + q` with `p ≤ n` and both `p` and `n - p` prime.  This is the diagonal value of the
additive-correlation ("spectral") model of the primes: the self-convolution `(1_P * 1_P)(n)`
of the indicator function of the primes. -/

theorem spectralCount_pos_iff (n : ℕ) :
    0 < spectralCount n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Finset.card_pos.mp h
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hlt, hpp, hqp⟩ := hp
    exact ⟨p, n - p, hpp, hqp, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine Finset.card_pos.mpr ⟨p, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hp, ?_⟩
    simpa using hq

/-- **Target.**  Goldbach from the spectral model, stated with no assumed hypotheses: the
spectral model and the binary Goldbach statement are equivalent.  In particular Goldbach
follows from the spectral model (`.mp` direction).

This is the honest limit of an unconditional discharge: by this very equivalence, a proof of
`SpectralModel` outright would be a proof of the (open) Goldbach conjecture.  What is
discharged unconditionally here is the schema itself, together with its verified initial
segment `goldbach_of_le_two_hundred` below. -/
