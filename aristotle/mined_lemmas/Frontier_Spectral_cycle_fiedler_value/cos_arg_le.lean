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

lemma cos_arg_le (hm : 2 ≤ m) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m) :
    Real.cos (2 * Real.pi * k / ((m : ℝ) + 1)) ≤ Real.cos (2 * Real.pi / ((m : ℝ) + 1)) := by
  have hpi := Real.pi_pos
  have hN : (3 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hNpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk2
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hA0 : 0 ≤ 2 * Real.pi / N := by positivity
  have hApi : 2 * Real.pi / N ≤ Real.pi := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hAT : 2 * Real.pi / N ≤ 2 * Real.pi * k / N := by
    apply div_le_div_of_nonneg_right ?_ hNpos.le
    nlinarith
  have hT2 : 2 * Real.pi * k / N ≤ 2 * Real.pi - 2 * Real.pi / N := by
    rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hNpos]
    nlinarith
  by_cases hTpi : 2 * Real.pi * k / N ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hA0 hTpi hAT
  · push_neg at hTpi
    have h1 : 2 * Real.pi - 2 * Real.pi * k / N ≤ Real.pi := by linarith
    have h2 : 2 * Real.pi / N ≤ 2 * Real.pi - 2 * Real.pi * k / N := by linarith
    have h3 := Real.cos_le_cos_of_nonneg_of_le_pi hA0 h1 h2
    rwa [Real.cos_two_pi_sub] at h3

/-- **Discrete Poincaré / Wirtinger inequality on the cycle.**  For a mean-zero vector on the
cycle `C_{m+1}`, the Dirichlet energy is at least `2 - 2 cos (2π/(m+1))` times the squared norm. -/
