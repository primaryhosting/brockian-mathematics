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

noncomputable def maximalMul (g : α → ℂ) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalMulDomain (μ := μ) g
  toFun :=
    { toFun := maximalMulValue g
      map_add' := by
        intro f h
        apply Lp.ext
        have ein : (((f + h : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
            ((f : Lp ℂ 2 μ) : α → ℂ) + ((h : Lp ℂ 2 μ) : α → ℂ) := by
          simpa using Lp.coeFn_add (f : Lp ℂ 2 μ) (h : Lp ℂ 2 μ)
        filter_upwards [coeFn_maximalMulValue g (f + h), coeFn_maximalMulValue g f,
          coeFn_maximalMulValue g h,
          Lp.coeFn_add (maximalMulValue g f) (maximalMulValue g h), ein]
            with x e0 e1 e2 esum einx
        simp only [Pi.add_apply, Pi.mul_apply] at e0 e1 e2 esum einx ⊢
        rw [e0, einx, esum, e1, e2]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        have ein : (((c • f : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
            c • ((f : Lp ℂ 2 μ) : α → ℂ) := by
          simpa using Lp.coeFn_smul c (f : Lp ℂ 2 μ)
        filter_upwards [coeFn_maximalMulValue g (c • f), coeFn_maximalMulValue g f,
          Lp.coeFn_smul c (maximalMulValue g f), ein] with x e0 e1 esr einx
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, RingHom.id_apply]
          at e0 e1 esr einx ⊢
        rw [e0, einx, esr, e1]
        ring }

