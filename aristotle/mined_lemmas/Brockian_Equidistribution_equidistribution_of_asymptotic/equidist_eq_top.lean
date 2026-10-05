import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

lemma equidist_eq_top (x : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 → Tendsto (cavg x (fourier h)) atTop (𝓝 0)) :
    Equidist x = ⊤ := by
  have hfour : ∀ h : ℤ, (fourier h : C(𝕋, ℂ)) ∈ Equidist x := by
    intro h
    rw [mem_equidist_iff, integral_fourier]
    by_cases hh : h = 0
    · subst hh
      have hev : ∀ N : ℕ, 1 ≤ N → cavg x (fourier (0 : ℤ)) N = 1 := by
        intro N hN
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp [cavg, hN0]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop))
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hev N hN).symm
    · simpa [hh] using hw h hh
  have hspan : Submodule.span ℂ (Set.range (fourier : ℤ → C(𝕋, ℂ))) ≤ Equidist x :=
    Submodule.span_le.mpr (by rintro f ⟨h, rfl⟩; exact hfour h)
  have hcl := Submodule.topologicalClosure_mono hspan
  rw [span_fourier_closure_eq_top] at hcl
  have hc : (Equidist x).topologicalClosure = Equidist x :=
    SetLike.ext' (isClosed_equidist x).closure_eq
  rw [hc] at hcl
  exact top_le_iff.mp hcl

/-- Weyl's criterion for real-valued continuous test functions. -/
