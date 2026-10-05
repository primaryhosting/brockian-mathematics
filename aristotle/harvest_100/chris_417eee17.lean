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

namespace Brockian.OreHarmonicNumbers

open Finset

/-- The number of divisors of `n`, usually written `τ (n)` or `d (n)`. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- The sum of the divisors of `n`, usually written `σ (n)`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if `n > 0` and the harmonic
mean of the divisors of `n`, namely `n * τ (n) / σ (n)`, is an integer. -/
def IsHarmonic (n : ℕ) : Prop := 0 < n ∧ sigma n ∣ n * tau n

instance (n : ℕ) : Decidable (IsHarmonic n) := by
  unfold IsHarmonic; infer_instance

/-- The harmonic mean of the divisors of `n`, as a rational number. -/
noncomputable def harmonicMean (n : ℕ) : ℚ :=
  (tau n : ℚ) / ∑ d ∈ n.divisors, (d : ℚ)⁻¹

/-- The sum of the reciprocals of the divisors of `n` equals `σ (n) / n`. -/
theorem sum_inv_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (d : ℚ)⁻¹ = (sigma n : ℚ) / n := by
  rw [← Nat.sum_div_divisors n (fun d => ((d : ℚ))⁻¹)]
  rw [sigma, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd0 : (d : ℚ) ≠ 0 := by
    have : d ≠ 0 := by
      rintro rfl
      exact (Nat.mem_divisors.mp hd).2 (Nat.eq_zero_of_zero_dvd hdvd)
    exact Nat.cast_ne_zero.mpr this
  have hcast : ((n / d : ℕ) : ℚ) = (n : ℚ) / d := by
    rw [Nat.cast_div hdvd hd0]
  rw [hcast, inv_div]

/-- The harmonic mean of the divisors of `n` is indeed `n * τ (n) / σ (n)`. -/
theorem harmonicMean_eq (n : ℕ) :
    harmonicMean n = (n : ℚ) * tau n / sigma n := by
  rw [harmonicMean, sum_inv_divisors n, div_div_eq_mul_div]
  ring_nf

/-- `n` is harmonic exactly when the harmonic mean of its divisors is a natural number. -/
theorem isHarmonic_iff_harmonicMean_nat (n : ℕ) (hn : 0 < n) :
    IsHarmonic n ↔ ∃ k : ℕ, harmonicMean n = k := by
  have hsig : 0 < sigma n := by
    have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
    calc 0 < n := hn
      _ ≤ sigma n := Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) hmem
  have hsig' : (sigma n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsig.ne'
  rw [harmonicMean_eq n]
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    rw [div_eq_iff hsig', ← Nat.cast_mul, ← Nat.cast_mul, hk, mul_comm]
  · rintro ⟨k, hk⟩
    refine ⟨hn, k, ?_⟩
    rw [div_eq_iff hsig'] at hk
    have hcast : ((n * tau n : ℕ) : ℚ) = ((sigma n * k : ℕ) : ℚ) := by
      push_cast; rw [hk]; ring
    exact_mod_cast hcast

/-- **Main result.** There exists an odd Ore harmonic number. -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsHarmonic n := by
  refine ⟨1, odd_one, ?_⟩
  decide

/-- The harmonic mean of the divisors of the witness `1` is `1`. -/
theorem harmonicMean_one : harmonicMean 1 = 1 := by
  rw [harmonicMean_eq 1]
  norm_num [tau, sigma]

/-- `6` is a harmonic number (its divisor harmonic mean is `2`), but it is even. -/
theorem isHarmonic_six : IsHarmonic 6 := by decide

/-- `28` is a harmonic number, but it is even. -/
theorem isHarmonic_twentyEight : IsHarmonic 28 := by decide

/-- A perfect number with an even number of divisors is harmonic. -/
theorem isHarmonic_of_perfect (n : ℕ) (hn : 0 < n) (hperf : sigma n = 2 * n)
    (htau : Even (tau n)) : IsHarmonic n := by
  obtain ⟨k, hk⟩ := htau
  refine ⟨hn, ⟨k, ?_⟩⟩
  rw [hperf, hk]; ring

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- **Partial evidence for Ore's conjecture.** No odd number `n` with `1 < n < 1000`
is harmonic. -/
theorem no_odd_harmonic_lt_1000 :
    ∀ n ∈ Finset.range 1000, Odd n → 1 < n → ¬ IsHarmonic n := by
  decide

/-- Consequently, below `1000` the only odd harmonic number is `1`. -/
theorem odd_harmonic_lt_1000_eq_one (n : ℕ) (hlt : n < 1000) (hodd : Odd n)
    (h : IsHarmonic n) : n = 1 := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · exact absurd h.1 (lt_irrefl 0)
    · rfl
  · exact absurd h (no_odd_harmonic_lt_1000 n (Finset.mem_range.mpr hlt) hodd h2)

end Brockian.OreHarmonicNumbers

