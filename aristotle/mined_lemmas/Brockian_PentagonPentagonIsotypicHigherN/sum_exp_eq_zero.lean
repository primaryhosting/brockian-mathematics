/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The cosine coordinate of the `k`-th Fourier mode on the vertices of a regular `n`-gon:
`ngonCos n k j = cos (2π k j / n)`. -/

theorem sum_exp_eq_zero (n : ℕ) (k : ℤ) (hn : 0 < n) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, Complex.exp (2 * Real.pi * Complex.I * k * j / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : Complex.exp (2 * Real.pi * Complex.I * k / n) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    field_simp at hm
    exact hk ⟨m, by exact_mod_cast hm⟩
  have key : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * j / n)
      = (Complex.exp (2 * Real.pi * Complex.I * k / n)) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    ring_nf
  simp only [key]
  rw [geom_sum_eq hz]
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * k / n)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul]
    have harg : (n : ℂ) * (2 * Real.pi * Complex.I * k / n)
        = (k : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  rw [hpow]
  simp

