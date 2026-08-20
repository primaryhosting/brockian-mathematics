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

import Mathlib

/-!
# Weyl's equidistribution criterion, via reduction of BV (indicator) test functions

This file proves the classical **Weyl criterion** (sufficiency direction):
if all nontrivial exponential sums along a real sequence `x : ℕ → ℝ` have vanishing
Cesàro averages, then `x` is equidistributed modulo one in the counting sense.

The proof proceeds by the *BV reduction*: the characteristic function of an interval
(a function of bounded variation) is squeezed between continuous trapezoidal functions
on the circle, and continuous functions on the circle are approximated uniformly by
trigonometric polynomials.

As an application, the sequence `n ↦ n * α` is equidistributed mod one for irrational `α`.
-/

open Filter Topology MeasureTheory Finset

namespace Brockian
namespace EquidistributionBVReduction

noncomputable section

open scoped Classical

instance factOnePos : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circ := AddCircle (1:ℝ)

/-- `x : ℕ → ℝ` is equidistributed modulo one: for every subinterval `[a, b) ⊆ [0,1]`,
the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
`b - a`. -/

lemma tendsto_count_of_weyl {x : ℕ → ℝ} (hW : WeylCondition x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hlt : b - a < 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set p : ℝ := (a + b - 1)/2 with hpdef
  obtain ⟨ε, hε, hε1, hε2, hε3⟩ :
      ∃ ε : ℝ, 0 < ε ∧ 4*ε ≤ 1 - (b - a) ∧ 2*ε ≤ b - a ∧ 4*ε < δ := by
    refine ⟨min ((1 - (b-a))/4) (min ((b-a)/2) (δ/5)), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    · have := min_le_left ((1 - (b-a))/4) (min ((b-a)/2) (δ/5)); linarith
    · have := le_trans (min_le_right ((1 - (b-a))/4) (min ((b-a)/2) (δ/5))) (min_le_left _ _)
      linarith
    · have := le_trans (min_le_right ((1 - (b-a))/4) (min ((b-a)/2) (δ/5))) (min_le_right _ _)
      linarith
  have hpa : p ≤ a - ε := by rw [hpdef]; linarith
  have hpb : b + ε ≤ p + 1 := by rw [hpdef]; linarith
  have hcont_hi : Continuous (circTrap p (a - ε) (b + ε) ε) :=
    continuous_circTrap (trap_eq_zero_of_le hε (by linarith))
      (trap_eq_zero_of_ge hε (by linarith))
  have hcont_lo : Continuous (circTrap p a b ε) :=
    continuous_circTrap (trap_eq_zero_of_le hε (by linarith))
      (trap_eq_zero_of_ge hε (by linarith))
  have hIhi : (∫ z : Circ, circTrap p (a - ε) (b + ε) ε z) ≤ (b - a) + 2*ε := by
    rw [integral_circTrap]
    have := integral_trap_le (u := a - ε) (v := b + ε) (p := p) hε (by linarith) (by linarith)
      (by linarith)
    linarith
  have hIlo : (b - a) - 2*ε ≤ ∫ z : Circ, circTrap p a b ε z := by
    rw [integral_circTrap]
    have := le_integral_trap (u := a) (v := b) (p := p) hε (by linarith) (by linarith)
      (by linarith)
    linarith
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (avgTendsto_real hW hcont_hi) ε hε
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (avgTendsto_real hW hcont_lo) ε hε
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₁ N (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hN)
  have h2 := hN₂ N (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  have hcu : (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N:ℝ)
      ≤ (∑ n ∈ Finset.range N, circTrap p (a - ε) (b + ε) ε ((x n : ℝ) : Circ)) / (N:ℝ) := by
    gcongr
    exact count_le_sum_circTrap hε hpa hpb N
  have hcl : (∑ n ∈ Finset.range N, circTrap p a b ε ((x n : ℝ) : Circ)) / (N:ℝ)
      ≤ (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N:ℝ) := by
    gcongr
    exact sum_circTrap_le_count hε ha hb N
  constructor
  · linarith [h2.1, hIlo, hcl]
  · linarith [h1.2, hIhi, hcu]

/-- **Weyl's equidistribution criterion.** If all nontrivial exponential sums along `x` have
vanishing Cesàro averages, then `x` is equidistributed modulo one.  The BV (indicator) test
functions are reduced to continuous ones by a trapezoidal sandwich, and continuous test
functions are handled by Fourier approximation. -/
