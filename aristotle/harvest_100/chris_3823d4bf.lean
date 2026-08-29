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

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian.OreHarmonicNumbers

/-- `n` is an **Ore harmonic number** (harmonic divisor number) if it is positive and the
harmonic mean of its divisors, `n * σ₀(n) / σ₁(n)`, is a natural number, i.e.
`σ₁ n ∣ n * σ₀ n`. -/
def IsOreHarmonic (n : ℕ) : Prop :=
  0 < n ∧ Nat.sigma 1 n ∣ n * Nat.sigma 0 n

instance (n : ℕ) : Decidable (IsOreHarmonic n) := by
  unfold IsOreHarmonic; infer_instance

/-- The harmonic mean of the divisors of `n`, as a natural number (meaningful exactly when
`n` is an Ore harmonic number). -/
def harmonicMean (n : ℕ) : ℕ := n * Nat.sigma 0 n / Nat.sigma 1 n

/-- `1` is an Ore harmonic number, with harmonic mean `1`. -/
theorem isOreHarmonic_one : IsOreHarmonic 1 ∧ harmonicMean 1 = 1 := by
  refine ⟨⟨Nat.one_pos, by decide⟩, by decide⟩

/-- **There exists an odd Ore harmonic number.** -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, isOreHarmonic_one.1⟩

/-- Partial evidence towards Ore's conjecture (no odd Ore harmonic number exceeds `1`):
no odd `n` with `1 < n ≤ 300` is an Ore harmonic number. -/
theorem no_odd_harmonic_le_300 :
    ∀ n : ℕ, n ≤ 300 → 1 < n → Odd n → ¬ IsOreHarmonic n := by
  decide

end Brockian.OreHarmonicNumbers

