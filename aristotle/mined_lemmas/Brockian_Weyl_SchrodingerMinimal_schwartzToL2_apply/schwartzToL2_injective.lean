/-
  Corpus declarations (reproduced verbatim from the Brockian modules, restricted to
  what is needed) together with the new bridge theorem

      freeSchrodingerPMap ≤ spectralFreeLaplacian.
-/
import Mathlib

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace ENNReal

/-! ## From `Brockian/WeylSchrodingerMinimal.lean` -/

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **The Schwartz core, embedded in `L²`.** -/

theorem schwartzToL2_injective : Function.Injective schwartzToL2 := by
  intro a b hab
  have hae : (a : ℝ → ℂ) =ᵐ[volume] b := by
    calc (a : ℝ → ℂ) =ᵐ[volume] (schwartzToL2 a : ℝ → ℂ) := (coeFn_schwartzToL2 a).symm
      _ = (schwartzToL2 b : ℝ → ℂ) := by rw [hab]
      _ =ᵐ[volume] b := coeFn_schwartzToL2 b
  have hEq : (a : ℝ → ℂ) = b := (a.continuous.ae_eq_iff_eq volume b.continuous).mp hae
  exact DFunLike.coe_injective hEq

/-- The second-derivative operator on Schwartz space. -/
