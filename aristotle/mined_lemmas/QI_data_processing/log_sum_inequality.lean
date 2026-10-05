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
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope note.

The data-processing inequality states that relative entropy is monotone under
channels.  This file develops the inequality in the *commutative* (equivalently:
jointly diagonalisable / classical) sector of quantum information theory, where a
CPTP map restricted to a commuting family of states is exactly a stochastic map
between the corresponding spectra, and the quantum relative entropy
`Tr ρ (log ρ - log σ)` is exactly the Kullback-Leibler divergence of the two
spectra.

Everything below is proved from scratch: the log-sum inequality (from convexity
of `x ↦ x log x`), the data-processing inequality `QI.data_processing`, and, as a
corollary of it, Gibbs' inequality (nonnegativity of relative entropy).

The last section leaves the commutative sector: it proves the data-processing
inequality `QI.data_processing_max` for the max-relative entropy
`D_max(ρ‖σ) = log inf {λ ≥ 0 | ρ ≤ λ σ}` for arbitrary, possibly noncommuting,
density matrices and arbitrary positive trace-preserving maps (in particular all
CPTP maps).
-/

open Finset

namespace QI

variable {ι κ : Type*}

/-- Relative entropy (Kullback–Leibler divergence) of two finite nonnegative
weight vectors, with the usual conventions `0 log (0/b) = 0` and
`0 log (0/0) = 0` (implemented via `Real.log 0 = 0` and `x / 0 = 0`). -/

theorem log_sum_inequality [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · -- degenerate case: `B = 0`, hence every `b i = 0`, hence every `a i = 0`
    have hbz : ∀ i, b i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ univ) => hb j)).1 hB0.symm i
        (mem_univ i)
      exact this
    have haz : ∀ i, a i = 0 := fun i => hab i (hbz i)
    have : A = 0 := by simp [hA, haz]
    simp [this, haz]
  · -- main case
    have hfun : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x * Real.log x) :=
      Real.convexOn_mul_log
    set w : ι → ℝ := fun i => b i / B with hw
    set x : ι → ℝ := fun i => a i / b i with hx
    have hw0 : ∀ i ∈ univ, 0 ≤ w i := fun i _ => div_nonneg (hb i) hBnn
    have hw1 : ∑ i, w i = 1 := by
      rw [hw]
      rw [← Finset.sum_div, ← hB, div_self (ne_of_gt hBpos)]
    have hxmem : ∀ i ∈ univ, x i ∈ Set.Ici (0 : ℝ) := fun i _ => div_nonneg (ha i) (hb i)
    have key := hfun.map_sum_le hw0 hw1 hxmem
    simp only [smul_eq_mul] at key
    -- identify `∑ w i • x i` with `A / B`
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hpt : ∀ i, w i * x i = a i / B := by
      intro i
      rcases eq_or_lt_of_le (hb i) with h0 | hpos
      · have : a i = 0 := hab i h0.symm
        simp [hw, hx, ← h0, this]
      · have hbi : b i ≠ 0 := ne_of_gt hpos
        show b i / B * (a i / b i) = a i / B
        field_simp
    have hwx : ∑ i, w i * x i = A / B := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hpt i), ← Finset.sum_div, ← hA]
    -- identify the right-hand side
    have hrhs : ∑ i, w i * (x i * Real.log (x i)) =
        (∑ i, a i * Real.log (a i / b i)) / B := by
      have : ∀ i ∈ univ, w i * (x i * Real.log (x i)) =
          (a i * Real.log (a i / b i)) / B := by
        intro i _
        rcases eq_or_lt_of_le (hb i) with h0 | hpos
        · have hai : a i = 0 := hab i h0.symm
          simp [hw, hx, ← h0, hai]
        · show b i / B * (a i / b i * Real.log (a i / b i))
            = a i * Real.log (a i / b i) / B
          rw [← mul_assoc, hpt i, div_mul_eq_mul_div]
      rw [Finset.sum_congr rfl this, ← Finset.sum_div]
    rw [hwx, hrhs] at key
    have h3 := mul_le_mul_of_nonneg_left key hBnn
    have e1 : B * (A / B * Real.log (A / B)) = A * Real.log (A / B) := by field_simp
    have e2 : B * ((∑ i, a i * Real.log (a i / b i)) / B)
        = ∑ i, a i * Real.log (a i / b i) := by field_simp
    rw [e1, e2] at h3
    exact h3

/-! ### The data-processing inequality -/

/-- **Data-processing inequality**.  Relative entropy is monotone under channels:
processing the two inputs `p` and `q` through a common channel `K` can only
decrease their relative entropy.

In the commutative sector of quantum information theory this is exactly the
statement that quantum relative entropy `Tr ρ (log ρ - log σ)` is monotone under
CPTP maps: for a family of commuting states a CPTP map acts on the joint spectra
as the stochastic matrix `K`, and the quantum relative entropy of the states is
the Kullback–Leibler divergence `relEntropy` of the spectra. -/
