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
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We work with finite-dimensional quantum systems, i.e. complex matrices `Matrix n n ℂ`.

* `QI.Channel ι n m` is a CPTP map (quantum channel) given in Kraus form: a family of Kraus
  operators `K i : Matrix m n ℂ` with `∑ i, (K i)ᴴ * K i = 1`.  `QI.Channel.map` is the
  Schrödinger picture action `X ↦ ∑ i, K i * X * (K i)ᴴ`; it is proved to be positive
  (`QI.Channel.map_posSemidef`) and trace preserving (`QI.Channel.trace_map`).
* `QI.posPartTrace X` is the trace of the positive part of a Hermitian matrix, defined
  variationally as `sup { Re Tr (X P) : 0 ≤ P ≤ 1 }` and valued in `ℝ≥0∞`.  Theorem
  `QI.posPartTrace_eq_sum_eigenvalues` identifies it with `∑ᵢ (λᵢ)₊`, the usual
  `Tr X₊`, for Hermitian `X`.
* `QI.posPartTrace_map_le` is the data processing inequality for the hockey-stick
  divergence: `Tr (Φ(X))₊ ≤ Tr X₊` for every channel `Φ`.
* `QI.relEntropy ρ σ` is the quantum relative entropy, expressed through Frenkel's integral
  formula
  `D(ρ ‖ σ) = ∫_0^∞ (Tr (ρ - tσ)₊ - (Tr ρ) (1 - t)₊) dt / t`,
  written as a lower Lebesgue integral (so its value lies in `ℝ≥0∞`, with `∞` allowed).
* `QI.data_processing` is the **data processing inequality**: `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`
  for every channel `Φ` and all `ρ`, `σ`.

## Remarks on the definition of relative entropy

That the integral formula above computes `Tr ρ (log ρ - log σ)` for arbitrary (in particular
non-commuting) density matrices is a theorem of P. E. Frenkel, *Integral formula for quantum
relative entropy implies data processing inequality*, J. Phys. A **56** (2023) 385303;
that identification is *not* formalised here.  What is formalised, besides the data processing
inequality itself, are the following consistency results:

* `QI.relEntropy_diagonal` (in `RequestProject.ClassicalCase`): for commuting states, i.e. for
  diagonal density matrices with entries given by probability vectors `p`, `q` with `q > 0`,
  the formula returns the classical Kullback-Leibler divergence `∑ᵢ pᵢ log (pᵢ / qᵢ)`.
* `QI.relEntropy_self`: `D(ρ ‖ ρ) = 0`.
* `QI.relEntropy_conj_unitary`: invariance under simultaneous unitary conjugation.

The data processing inequality proved here is in fact slightly stronger than the standard
statement in two ways: the integrand inequality only uses that the dual of the channel maps
effects to effects, and the states `ρ`, `σ` are arbitrary matrices.
-/

open scoped ENNReal ComplexOrder
open Matrix MeasureTheory

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- An *effect* (or *test operator*) is a matrix `P` with `0 ≤ P ≤ 1`. -/

theorem integral_fren (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    ∫ t in Ioi (0 : ℝ), fren p q t = p * Real.log (p / q) := by
  rcases hp.eq_or_lt with hp0 | hp0
  · have hpz : p = 0 := hp0.symm
    have hz : ∀ t ∈ Ioi (0 : ℝ), fren p q t = 0 := by
      intro t ht
      have h1 : min p (t * p) = 0 := by simp [hpz]
      have h2 : min p (t * q) = 0 := by
        rw [hpz]; exact min_eq_left (le_of_lt (mul_pos ht hq))
      rw [fren, h1, h2]; simp
    rw [setIntegral_congr_fun measurableSet_Ioi hz]
    simp [hpz]
  · set a := p / q with ha
    have ha0 : 0 < a := div_pos hp0 hq
    have haq : a * q = p := div_mul_cancel₀ p (ne_of_gt hq)
    have hint := integrableOn_fren p q hp hq
    have hB0 : (0 : ℝ) ≤ max 1 a := le_trans zero_le_one (le_max_left _ _)
    have hmain := integral_Ioi_of_eventually_zero hint hB0
      (fun t ht => fren_eq_zero p q hp hq ht)
    have hii : ∀ x y : ℝ, 0 ≤ x → x ≤ y → IntervalIntegrable (fren p q) volume x y := by
      intro x y hx hxy
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
      exact hint.mono_set (fun t ht => lt_of_le_of_lt hx ht.1)
    rcases le_total a 1 with hle | hle
    · rw [max_eq_left hle] at hmain
      rw [hmain, ← intervalIntegral.integral_add_adjacent_intervals
        (hii 0 a (le_refl 0) ha0.le) (hii a 1 ha0.le hle)]
      have e1 : ∫ t in (0 : ℝ)..a, fren p q t = ∫ _t in (0 : ℝ)..a, (p - q) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
        rw [Set.uIoc_of_le ha0.le] at ht
        exact fren_small p q hp hq ht.1 (le_trans ht.2 hle) ht.2
      have e2 : ∫ t in a..(1 : ℝ), fren p q t = ∫ t in a..(1 : ℝ), (p - p * t⁻¹) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hle] at ht
        exact fren_mid1 p q hp hq (lt_of_lt_of_le ha0 ht.1) ht.2 ht.1
      have h1 : IntervalIntegrable (fun t : ℝ => p * t⁻¹) volume a 1 := by
        refine (ContinuousOn.mul continuousOn_const
          (ContinuousOn.inv₀ continuousOn_id ?_)).intervalIntegrable
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
      rw [e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const h1,
        intervalIntegral.integral_const, intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 zero_lt_one,
        one_div, Real.log_inv]
      simp only [smul_eq_mul, sub_zero]
      nlinarith [haq]
    · rw [max_eq_right hle] at hmain
      rw [hmain, ← intervalIntegral.integral_add_adjacent_intervals
        (hii 0 1 (le_refl 0) zero_le_one) (hii 1 a zero_le_one hle)]
      have e1 : ∫ t in (0 : ℝ)..1, fren p q t = ∫ _t in (0 : ℝ)..1, (p - q) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact fren_small p q hp hq ht.1 ht.2 (le_trans ht.2 hle)
      have e2 : ∫ t in (1 : ℝ)..a, fren p q t = ∫ t in (1 : ℝ)..a, (p * t⁻¹ - q) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hle] at ht
        exact fren_mid2 p q hp hq (lt_of_lt_of_le zero_lt_one ht.1) ht.1 ht.2
      have h1 : IntervalIntegrable (fun t : ℝ => p * t⁻¹) volume 1 a := by
        refine (ContinuousOn.mul continuousOn_const
          (ContinuousOn.inv₀ continuousOn_id ?_)).intervalIntegrable
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
      rw [e1, e2, intervalIntegral.integral_sub h1 intervalIntegral.intervalIntegrable_const,
        intervalIntegral.integral_const, intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one ha0]
      simp only [smul_eq_mul, sub_zero, div_one]
      nlinarith [haq]

/-- The sum over `i` of the scalar Frenkel integrands. -/
