import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/

lemma dirichlet_lower (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (hsum : ∑ j, x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 1))) * (∑ j, (x j) ^ 2)
      ≤ ∑ j, (x j - x (j - 1)) ^ 2 := by
  have hn0 : (m + 1) ≠ 0 := Nat.succ_ne_zero m
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  set L : ℝ := 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 1)) with hL
  have hterm : ∀ k ∈ Finset.range (m + 1),
      L * Complex.normSq (dft (m + 1) x k)
        ≤ Complex.normSq (dft (m + 1) (fun j => x j - x (j - 1)) k) := by
    intro k hk
    rw [dft_diff hm, Complex.normSq_mul, normSq_one_sub_zeta_pow hn0, hc]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hz : dft (m + 1) x 0 = 0 := by rw [dft_zero, hsum]; simp
      rw [hz]
      simp
    · have hk2 : k ≤ m := by
        have := Finset.mem_range.mp hk
        omega
      have hcos := cos_arg_le hm hk1 hk2
      have hnn : 0 ≤ Complex.normSq (dft (m + 1) x k) := Complex.normSq_nonneg _
      nlinarith [hcos, hnn]
  have hsum1 : L * (∑ k ∈ Finset.range (m + 1), Complex.normSq (dft (m + 1) x k))
      ≤ ∑ k ∈ Finset.range (m + 1),
          Complex.normSq (dft (m + 1) (fun j => x j - x (j - 1)) k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  rw [parseval hn0 x, parseval hn0 (fun j => x j - x (j - 1)), hc] at hsum1
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : ((m : ℝ) + 1) * (L * ∑ j, (x j) ^ 2)
      ≤ ((m : ℝ) + 1) * (∑ j, (x j - x (j - 1)) ^ 2) := by
    calc ((m : ℝ) + 1) * (L * ∑ j, (x j) ^ 2)
        = L * (((m : ℝ) + 1) * ∑ j, (x j) ^ 2) := by ring
      _ ≤ ((m : ℝ) + 1) * (∑ j, (x j - x (j - 1)) ^ 2) := hsum1
  exact le_of_mul_le_mul_left h2 hpos

end Dirichlet

end Frontier.Spectral

