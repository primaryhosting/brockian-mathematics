import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma sum_sigmaOne_div_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (sigmaOne n : ℝ) / n ≤ 2 * N := by
  have step1 : ∑ n ∈ Finset.Icc 1 N, (sigmaOne n : ℝ) / n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (1:ℝ)/d := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_Icc] at hn
    exact sigmaOne_div_eq_sum_inv_divisors (by omega)
  have step2 : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (1:ℝ)/d
      = ∑ d ∈ Finset.Icc 1 N, ∑ _n ∈ {n ∈ Finset.Icc 1 N | d ∣ n}, (1:ℝ)/d := by
    refine Finset.sum_comm' ?_
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, _⟩
      have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      exact ⟨⟨⟨h1, h2⟩, hdvd⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, hdvd, by omega⟩
  rw [step1, step2]
  have step3 : ∀ d ∈ Finset.Icc 1 N, ∑ _n ∈ {n ∈ Finset.Icc 1 N | d ∣ n}, (1:ℝ)/d
      ≤ (N:ℝ) * ((1:ℝ)/(d:ℝ)^2) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [Finset.sum_const, card_multiples_Icc, nsmul_eq_mul]
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd.1
    have hle : ((N / d : ℕ) : ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    calc ((N / d : ℕ) : ℝ) * (1/d) ≤ ((N:ℝ)/d) * (1/d) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (N:ℝ) * ((1:ℝ)/(d:ℝ)^2) := by field_simp
  calc ∑ d ∈ Finset.Icc 1 N, ∑ _n ∈ {n ∈ Finset.Icc 1 N | d ∣ n}, (1:ℝ)/d
      ≤ ∑ d ∈ Finset.Icc 1 N, (N:ℝ) * ((1:ℝ)/(d:ℝ)^2) := Finset.sum_le_sum step3
    _ = (N:ℝ) * ∑ d ∈ Finset.Icc 1 N, (1:ℝ)/(d:ℝ)^2 := by rw [Finset.mul_sum]
    _ ≤ (N:ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_one_div_sq_le N) (by positivity)
    _ = 2 * N := by ring

/-- Markov bound: at most `2N/K` integers `n ≤ N` have abundancy `σ(n)/n > K`. -/
