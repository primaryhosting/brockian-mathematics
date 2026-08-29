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

/-- `IsOreHarmonic n` says that `n` is an *Ore harmonic number* (harmonic divisor number):
`n` is positive and the harmonic mean of its divisors, `n * τ(n) / σ(n)`, is an integer.
Here `τ n = n.divisors.card` is the number of divisors and `σ n = ∑ d ∈ n.divisors, d`
is their sum. -/
def IsOreHarmonic (n : ℕ) : Prop :=
  0 < n ∧ (∑ d ∈ n.divisors, d) ∣ n * n.divisors.card

/-- The sum of the reciprocals of the divisors of a positive `n` equals `σ(n)/n`. -/
theorem sum_inv_divisors (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (1 : ℚ) / d = ((∑ d ∈ n.divisors, d : ℕ) : ℚ) / n := by
  have h : ∀ d ∈ n.divisors, (1 : ℚ) / d = ((n / d : ℕ) : ℚ) / n := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd0 : (d : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Nat.cast_div hdvd hd0]
    field_simp
  have hsum : (∑ x ∈ n.divisors, n / x) = ∑ d ∈ n.divisors, d :=
    Nat.sum_div_divisors n (fun d => d)
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, ← Nat.cast_sum, hsum]

/-- `n` is Ore harmonic exactly when the harmonic mean of its divisors,
`τ(n) / ∑_{d ∣ n} (1/d)`, is a natural number. -/
theorem isOreHarmonic_iff_harmonicMean_isNat {n : ℕ} (hn : 0 < n) :
    IsOreHarmonic n ↔
      ∃ k : ℕ, (n.divisors.card : ℚ) / (∑ d ∈ n.divisors, (1 : ℚ) / d) = k := by
  have hσpos : 0 < ∑ d ∈ n.divisors, d :=
    Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd)
      ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hσ0 : ((∑ d ∈ n.divisors, d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hσpos.ne'
  rw [sum_inv_divisors n hn, div_div_eq_mul_div]
  constructor
  · rintro ⟨-, k, hk⟩
    have hk' : (n : ℚ) * n.divisors.card = ((∑ d ∈ n.divisors, d : ℕ) : ℚ) * k := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hk
    exact ⟨k, by rw [div_eq_iff hσ0]; linear_combination hk'⟩
  · rintro ⟨k, hk⟩
    rw [div_eq_iff hσ0] at hk
    have hnat : n * n.divisors.card = (∑ d ∈ n.divisors, d) * k := by
      have hq : ((n * n.divisors.card : ℕ) : ℚ) = (((∑ d ∈ n.divisors, d) * k : ℕ) : ℚ) := by
        push_cast at hk ⊢
        linear_combination hk
      exact_mod_cast hq
    exact ⟨hn, ⟨k, hnat⟩⟩

/-- `1` is an Ore harmonic number. -/
theorem isOreHarmonic_one : IsOreHarmonic 1 := ⟨Nat.one_pos, by decide⟩

/-- `6` is an Ore harmonic number (its divisors `1, 2, 3, 6` have harmonic mean `2`). -/
theorem isOreHarmonic_six : IsOreHarmonic 6 := ⟨by norm_num, by decide⟩

/-- **Odd Harmonic Exists**: there is an odd Ore harmonic number. -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, isOreHarmonic_one⟩

set_option maxRecDepth 100000 in
/-- Ore's conjecture states that `1` is the *only* odd Ore harmonic number.  Here we verify
it for all `n ≤ 300`. -/
theorem odd_isOreHarmonic_eq_one_of_le_300 (n : ℕ) (hn : n ≤ 300) (hodd : Odd n)
    (h : IsOreHarmonic n) : n = 1 := by
  have key : ∀ m ∈ Finset.Icc 1 300, Odd m →
      (∑ d ∈ m.divisors, d) ∣ m * m.divisors.card → m = 1 := by decide
  exact key n (Finset.mem_Icc.mpr ⟨h.1, hn⟩) hodd h.2

end Brockian.OreHarmonicNumbers

