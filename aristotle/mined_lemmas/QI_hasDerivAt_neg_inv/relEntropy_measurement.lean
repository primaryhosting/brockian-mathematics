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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem relEntropy_measurement (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace)
    (hE : IsPOVM E) :
    ∑ y, ((ρ * E y).trace.re * Real.log ((ρ * E y).trace.re)
        - (ρ * E y).trace.re * Real.log ((σ * E y).trace.re)) ≤ relEntropy ρ σ := by
  classical
  set P : Y → ℝ := fun y => (ρ * E y).trace.re with hP
  set Q : Y → ℝ := fun y => (σ * E y).trace.re with hQ
  set S : Finset Y := Finset.univ.filter (fun y => E y ≠ 0) with hS
  have hPnn : ∀ y, 0 ≤ P y := fun y => trace_mul_nonneg hρ (hE.posSemidef y)
  have hQnn : ∀ y, 0 ≤ Q y := fun y => trace_mul_nonneg hσ (hE.posSemidef y)
  have hmemS : ∀ y, y ∈ S ↔ E y ≠ 0 := by intro y; simp [hS]
  have hPpos : ∀ y ∈ S, 0 < P y := by
    intro y hy
    rcases eq_or_lt_of_le (hPnn y) with h | h
    · exact absurd (eq_zero_of_trace_mul_eq_zero hρ (hE.posSemidef y) h.symm) ((hmemS y).mp hy)
    · exact h
  have hQpos : ∀ y ∈ S, 0 < Q y := by
    intro y hy
    rcases eq_or_lt_of_le (hQnn y) with h | h
    · exact absurd (eq_zero_of_trace_mul_eq_zero hσ (hE.posSemidef y) h.symm) ((hmemS y).mp hy)
    · exact h
  have hEzero : ∀ y ∉ S, E y = 0 := by
    intro y hy
    by_contra h
    exact hy ((hmemS y).mpr h)
  have hPzero : ∀ y ∉ S, P y = 0 := by intro y hy; simp [hP, hEzero y hy]
  have hQzero : ∀ y ∉ S, Q y = 0 := by intro y hy; simp [hQ, hEzero y hy]
  -- the two outcome distributions have equal total mass
  have htotal : ∀ (A : Mat n), ∑ y, (A * E y).trace.re = A.trace.re := by
    intro A
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hE.sum_eq_one, mul_one]
  have hsumP : ∑ y ∈ S, P y = ρ.trace.re := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => hPzero y hy)]
    exact htotal ρ
  have hsumQ : ∑ y ∈ S, Q y = σ.trace.re := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => hQzero y hy)]
    exact htotal σ
  have hsum_eq : ∑ y ∈ S, P y = ∑ y ∈ S, Q y := by rw [hsumP, hsumQ, htr]
  -- rewrite the left hand side as a sum of integrals
  have hLHS : ∑ y, (P y * Real.log (P y) - P y * Real.log (Q y))
      = ∑ y ∈ S, (P y * Real.log (P y) - P y * Real.log (Q y)) :=
    (Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => by simp [hPzero y hy])).symm
  have hterm : ∀ y ∈ S, P y * Real.log (P y) - P y * Real.log (Q y)
      = (∫ s in Ioo (0:ℝ) 1, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)))
          + (P y - Q y) := by
    intro y hy
    rw [classical_path_identity (hPpos y hy) (hQpos y hy)]
    ring
  have hsplit : ∑ y ∈ S, (P y * Real.log (P y) - P y * Real.log (Q y))
      = ∑ y ∈ S, ∫ s in Ioo (0:ℝ) 1, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum_eq]
    ring
  have hswap : ∑ y ∈ S, (∫ s in Ioo (0:ℝ) 1, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)))
      = ∫ s in Ioo (0:ℝ) 1, ∑ y ∈ S, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) :=
    (MeasureTheory.integral_finset_sum S
      (fun y hy => integrableOn_classical_path (hPpos y hy) (hQpos y hy))).symm
  rw [hLHS, hsplit, hswap, relEntropy_eq_path hρ hσ htr]
  refine MeasureTheory.setIntegral_mono_on
    (MeasureTheory.integrable_finset_sum S
      (fun y hy => integrableOn_classical_path (hPpos y hy) (hQpos y hy)))
    (integrableOn_path hρ hσ htr) measurableSet_Ioo (fun s hs => ?_)
  obtain ⟨hs0, hs1⟩ := hs
  have hωs : (pathState ρ σ s).PosDef := pathState_posDef hρ hσ hs0.le hs1.le
  have hΔ : (ρ - σ).IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  have hnum : ∀ y, ((ρ - σ) * E y).trace.re = P y - Q y := by
    intro y
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  have hden : ∀ y, ((pathState ρ σ s) * E y).trace.re = Q y + s * (P y - Q y) := by
    intro y
    rw [trace_pathState, Complex.add_re, Complex.mul_re]
    simp [hP, hQ, Complex.sub_re]
  have key := meas_le_bkm hωs hΔ hE
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => by
    rw [hnum y, hden y] : ∀ _, _)] at key
  have hsubset : ∑ y ∈ S, (P y - Q y) ^ 2 / (Q y + s * (P y - Q y))
      = ∑ y, (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) :=
    Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => by
      simp [hPzero y hy, hQzero y hy])
  have hfac : ∑ y ∈ S, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y))
      = (1 - s) * ∑ y ∈ S, (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hfac, hsubset]
  exact mul_le_mul_of_nonneg_left key (by linarith)

end QI

import RequestProject.QI.Bkm

/-!
# Uniform estimates on resolvents

Bounds on the traces `Tr (A R B R)` with `R = (ω + t)⁻¹`, uniform over families of matrices
whose spectra are bounded below.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω : Mat n}

/-- The squared Frobenius norm of a matrix. -/
