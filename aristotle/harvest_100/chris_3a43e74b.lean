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
def spectralCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

/-- The *spectral model hypothesis*: the prime-pair correlation is positive at every even
`n ≥ 4`. -/
def SpectralModel : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → 0 < spectralCount n

/-- The binary Goldbach statement. -/
def Goldbach : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Pointwise dictionary between the spectral model and Goldbach representations: positivity
of the correlation count at `n` is equivalent to `n` being a sum of two primes.  The Mathlib
ingredients are `Finset.card_pos` (`0 < s.card ↔ s.Nonempty`) and `Finset.mem_filter`. -/
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
theorem goldbach_from_spectral_model : SpectralModel ↔ Goldbach := by
  constructor
  · intro h n hn h4
    exact (spectralCount_pos_iff n).mp (h n hn h4)
  · intro h n hn h4
    exact (spectralCount_pos_iff n).mpr (h n hn h4)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
/-- The spectral model, discharged unconditionally on the range `n ≤ 200` by kernel
computation of the prime-pair correlation counts. -/
theorem spectralModel_of_le_two_hundred :
    ∀ m ∈ Finset.range 201, (Even m ∧ 4 ≤ m) → 0 < spectralCount m := by
  decide

/-- An unconditional, kernel-checked initial segment of Goldbach: every even `n` with
`4 ≤ n ≤ 200` is a sum of two primes. -/
theorem goldbach_of_le_two_hundred (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) (hle : n ≤ 200) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rw [← spectralCount_pos_iff]
  exact spectralModel_of_le_two_hundred n (Finset.mem_range.mpr (by omega)) ⟨hn, h4⟩

end Brockian.GoldbachSchema

