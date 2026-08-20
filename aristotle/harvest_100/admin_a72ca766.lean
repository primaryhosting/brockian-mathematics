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

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OreHarmonicNumbers

/-- The harmonic mean of the (positive) divisors of `n`:
`τ(n) / ∑_{d ∣ n} 1/d`. -/
noncomputable def divisorHarmonicMean (n : ℕ) : ℚ :=
  (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, (1 : ℚ) / d

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if it is positive and the
harmonic mean of its divisors is a natural number. -/
def IsOreHarmonic (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, divisorHarmonicMean n = k

/-- The sum of the reciprocals of the divisors of `n` equals `σ(n) / n`. -/
theorem sum_inv_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (1 : ℚ) / d = (∑ d ∈ n.divisors, (d : ℚ)) / n := by
  rw [← Nat.sum_div_divisors n (fun d => (1 : ℚ) / d), Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Nat.mem_divisors] at hd
  obtain ⟨⟨c, rfl⟩, hne⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hne)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hne)
  rw [Nat.mul_div_cancel_left _ hd0]
  have : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0.ne'
  have : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  push_cast
  field_simp

/-- Closed form for the harmonic mean of the divisors: `n · τ(n) / σ(n)`. -/
theorem divisorHarmonicMean_eq (n : ℕ) (hn : 0 < n) :
    divisorHarmonicMean n = (n : ℚ) * n.divisors.card / (∑ d ∈ n.divisors, (d : ℚ)) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [divisorHarmonicMean, sum_inv_divisors, div_div_eq_mul_div]
  ring_nf

/-- Divisibility characterisation of Ore harmonic numbers: `n` is harmonic iff
`σ(n) ∣ n · τ(n)`. -/
theorem isOreHarmonic_iff (n : ℕ) (hn : 0 < n) :
    IsOreHarmonic n ↔ (∑ d ∈ n.divisors, d) ∣ n * n.divisors.card := by
  have hsum : 0 < ∑ d ∈ n.divisors, d :=
    Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd)
      ⟨n, Nat.mem_divisors_self n hn.ne'⟩
  have hsum0 : ((∑ d ∈ n.divisors, d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsum.ne'
  constructor
  · rintro ⟨-, k, hk⟩
    rw [divisorHarmonicMean_eq n hn, div_eq_iff (by push_cast at hsum0 ⊢; exact hsum0)] at hk
    refine ⟨k, ?_⟩
    have : ((n * n.divisors.card : ℕ) : ℚ) = (((∑ d ∈ n.divisors, d) * k : ℕ) : ℚ) := by
      push_cast
      rw [hk]
      ring
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    refine ⟨hn, k, ?_⟩
    rw [divisorHarmonicMean_eq n hn, div_eq_iff (by push_cast at hsum0 ⊢; exact hsum0)]
    have : ((n * n.divisors.card : ℕ) : ℚ) = (((∑ d ∈ n.divisors, d) * k : ℕ) : ℚ) := by
      rw [hk]
    push_cast at this
    linarith [this]

/-- The harmonic mean of the divisors of `1` is `1`. -/
theorem divisorHarmonicMean_one : divisorHarmonicMean 1 = 1 := by
  simp [divisorHarmonicMean]

/-- `1` is an Ore harmonic number. -/
theorem isOreHarmonic_one : IsOreHarmonic 1 :=
  ⟨Nat.one_pos, 1, by simpa using divisorHarmonicMean_one⟩

/-- **There exists an odd Ore harmonic number.**  (Ore's conjecture asserts that `1` is the
only one; here we only need its existence, witnessed by `n = 1`.) -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, isOreHarmonic_one⟩

/-- `6` is an (even) Ore harmonic number: its divisors have harmonic mean `2`. -/
theorem isOreHarmonic_six : IsOreHarmonic 6 := by
  rw [isOreHarmonic_iff 6 (by norm_num)]
  decide

/-- `28` is an (even) Ore harmonic number: its divisors have harmonic mean `3`. -/
theorem isOreHarmonic_twentyEight : IsOreHarmonic 28 := by
  rw [isOreHarmonic_iff 28 (by norm_num)]
  decide

section FiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A verified instance of Ore's conjecture in a finite range: `1` is the only odd Ore
harmonic number below `1000`. -/
theorem eq_one_of_odd_isOreHarmonic_lt_thousand (n : ℕ) (hn : n < 1000) (hodd : Odd n)
    (h : IsOreHarmonic n) : n = 1 := by
  have key : ∀ m < 1000, m % 2 = 1 →
      ((∑ d ∈ m.divisors, d) ∣ m * m.divisors.card) → m = 1 := by decide
  exact key n hn (Nat.odd_iff.mp hodd) ((isOreHarmonic_iff n h.1).mp h)

end FiniteCheck

end Brockian.OreHarmonicNumbers

