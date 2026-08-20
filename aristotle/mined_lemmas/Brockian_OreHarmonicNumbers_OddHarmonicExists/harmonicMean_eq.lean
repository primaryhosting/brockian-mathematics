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

An *Ore harmonic number* (harmonic divisor number) is a positive integer `n` for which the
harmonic mean of the divisors of `n`, namely `n * τ n / σ n`, is an integer.  Ore's conjecture
states that `1` is the only odd harmonic number; here we prove that an odd harmonic number
does exist (namely `1`), that it is the only one below `1000`, and record the basic
characterisation of the definition in terms of the harmonic mean.
-/

namespace Brockian.OreHarmonicNumbers

open Finset

/-- The sum of the divisors of `n`. -/

lemma harmonicMean_eq {n : ℕ} (hn : 0 < n) :
    harmonicMean n = (tau n : ℚ) / (∑ d ∈ n.divisors, (1 : ℚ) / d) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : (sigmaOne n : ℚ) ≠ 0 := by exact_mod_cast (sigmaOne_pos hn).ne'
  have key : (∑ d ∈ n.divisors, (1 : ℚ) / d) * n = (sigmaOne n : ℚ) := by
    rw [Finset.sum_mul]
    have hcongr : ∀ d ∈ n.divisors, (1 : ℚ) / d * n = ((n / d : ℕ) : ℚ) := by
      intro d hd
      obtain ⟨hdvd, hn'⟩ := Nat.mem_divisors.mp hd
      have hd0 : (d : ℚ) ≠ 0 := by
        have : d ≠ 0 := by rintro rfl; exact hn' (zero_dvd_iff.mp hdvd)
        exact_mod_cast this
      rw [Nat.cast_div hdvd hd0]
      field_simp
    rw [Finset.sum_congr rfl hcongr, ← Nat.cast_sum]
    exact_mod_cast Nat.sum_div_divisors n (fun x => x)
  have hsum : (∑ d ∈ n.divisors, (1 : ℚ) / d) = (sigmaOne n : ℚ) / n := by
    rw [eq_div_iff hn0]; exact key
  rw [hsum, harmonicMean]
  field_simp

/-- `n` is Ore harmonic exactly when the harmonic mean of its divisors is a natural number. -/
