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
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the Pusey–Barrett–Rudolph (PBR) theorem: in any ontological
(hidden-variable) model reproducing the quantum predictions, under the
*preparation independence* assumption, the probability distributions over ontic
states associated with two distinct (non-orthogonal) quantum preparations cannot
overlap.  Equivalently, the quantum state is *ontic* rather than *epistemic*.

Two ingredients are given.

* `QI.pbr_orthogonality` : the quantum input.  The four (unnormalised) PBR
  measurement vectors on `ℂ² ⊗ ℂ²` are pairwise orthogonal and each of them is
  orthogonal to exactly one of the four product preparations `|0⟩|0⟩`,
  `|0⟩|+⟩`, `|+⟩|0⟩`, `|+⟩|+⟩`.  Hence a quantum model predicts probability `0`
  for outcome `(i,j)` on preparation `(i,j)`.

* `QI.pbr_theorem` : the ontological conclusion.  Given an ontological model
  with response functions summing to one, preparation independence (the ontic
  state of two independently prepared systems is distributed according to the
  product measure) and the above zero predictions, any common component `q • ν`
  of the two preparation distributions must be trivial, i.e. `q = 0`.
-/

namespace QI

open MeasureTheory
open scoped ENNReal

/-! ## The quantum input: the PBR measurement -/

/-- Hermitian inner product on `ℂ⁴ = ℂ² ⊗ ℂ²`, whose index set is `Fin 2 × Fin 2`. -/

theorem pbr_theorem {Λ : Type*} [MeasurableSpace Λ]
    (μ : Fin 2 → Measure Λ) [∀ i, IsProbabilityMeasure (μ i)]
    (ξ : Fin 2 × Fin 2 → Λ × Λ → ℝ≥0∞) (hmeas : ∀ k, Measurable (ξ k))
    (hnorm : ∀ x, ∑ k : Fin 2 × Fin 2, ξ k x = 1)
    (hborn : ∀ i j : Fin 2, ∫⁻ x, ξ (i, j) x ∂((μ i).prod (μ j)) = 0)
    (ν : Measure Λ) [IsProbabilityMeasure ν] (q : ℝ≥0)
    (hoverlap : ∀ i : Fin 2, (q : ℝ≥0∞) • ν ≤ μ i) : q = 0 := by
  by_contra hq
  have hq0 : ((q : ℝ≥0∞)) ≠ 0 := by simpa using hq
  -- Each outcome has zero probability on the "overlap" product preparation.
  have key : ∀ k : Fin 2 × Fin 2, ∫⁻ x, ∫⁻ y, ξ k (x, y) ∂ν ∂ν = 0 := by
    rintro ⟨i, j⟩
    have h1 : ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂(μ j) ∂(μ i) = 0 := by
      rw [← lintegral_prod _ (hmeas (i, j)).aemeasurable]
      exact hborn i j
    have h2 : ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂((q : ℝ≥0∞) • ν) ∂((q : ℝ≥0∞) • ν)
        ≤ ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂(μ j) ∂(μ i) :=
      lintegral_mono' (hoverlap i) (fun _ => lintegral_mono' (hoverlap j) le_rfl)
    rw [h1, lintegral_smul_measure] at h2
    simp only [lintegral_smul_measure] at h2
    have h3 : (q : ℝ≥0∞) * ((q : ℝ≥0∞) * ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂ν ∂ν) = 0 :=
      le_antisymm h2 (zero_le _)
    simpa [hq0] using h3
  -- But the response functions sum to one, so the total is one.
  have hone : ∫⁻ x, ∫⁻ y, (∑ k : Fin 2 × Fin 2, ξ k (x, y)) ∂ν ∂ν = 1 := by
    simp [hnorm]
  rw [show (fun x : Λ => ∫⁻ y, (∑ k : Fin 2 × Fin 2, ξ k (x, y)) ∂ν)
        = fun x : Λ => ∑ k : Fin 2 × Fin 2, ∫⁻ y, ξ k (x, y) ∂ν from
      funext fun x => lintegral_finset_sum _ (fun k _ => (hmeas k).comp measurable_prodMk_left),
    lintegral_finset_sum _
      (fun k _ => (hmeas k).lintegral_prod_right' (μ := ν))] at hone
  simp [key] at hone

end QI
