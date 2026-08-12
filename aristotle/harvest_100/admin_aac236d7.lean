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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace Brockian.OreHarmonicNumbers

open ArithmeticFunction

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if it is positive and the
harmonic mean of its divisors, namely `n * τ n / σ n`, is an integer.  Equivalently,
`σ 1 n ∣ n * σ 0 n`. -/
def IsOreHarmonic (n : ℕ) : Prop := 0 < n ∧ sigma 1 n ∣ n * sigma 0 n

instance : DecidablePred IsOreHarmonic := fun n => by unfold IsOreHarmonic; infer_instance

/-- The harmonic mean of the divisors of `n`, as a rational number. -/
noncomputable def harmonicMean (n : ℕ) : ℚ := (n * sigma 0 n : ℕ) / (sigma 1 n : ℕ)

/-- For positive `n`, being an Ore harmonic number means exactly that the harmonic mean of the
divisors of `n` is a natural number. -/
theorem isOreHarmonic_iff_harmonicMean_isNat {n : ℕ} (hn : 0 < n) :
    IsOreHarmonic n ↔ ∃ k : ℕ, harmonicMean n = (k : ℚ) := by
  have hσ : sigma 1 n ≠ 0 := by
    have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
    simp only [ArithmeticFunction.sigma_one_apply]
    intro h
    rw [Finset.sum_eq_zero_iff] at h
    simpa using h 1 h1
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    rw [harmonicMean, hk]
    push_cast
    field_simp
  · rintro ⟨k, hk⟩
    refine ⟨hn, ⟨k, ?_⟩⟩
    rw [harmonicMean] at hk
    have : ((n * sigma 0 n : ℕ) : ℚ) = ((sigma 1 n : ℕ) : ℚ) * (k : ℚ) := by
      field_simp at hk
      linarith [hk]
    exact_mod_cast this

/-- **Odd harmonic exists**: there is an odd Ore harmonic number, namely `n = 1`. -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, by decide⟩

/-- `1` is an odd Ore harmonic number. -/
theorem isOreHarmonic_one : IsOreHarmonic 1 := by decide

/-- A verified partial step towards Ore's conjecture: `1` is the only odd Ore harmonic number
below `300`. -/
theorem odd_isOreHarmonic_lt_300 :
    ∀ n ∈ Finset.range 300, IsOreHarmonic n → Odd n → n = 1 := by
  simp only [IsOreHarmonic, ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_zero_apply, Nat.odd_iff]
  decide

end Brockian.OreHarmonicNumbers

