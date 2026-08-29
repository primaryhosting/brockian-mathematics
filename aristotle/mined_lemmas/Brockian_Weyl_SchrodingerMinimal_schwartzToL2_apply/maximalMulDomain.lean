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

noncomputable def maximalMulDomain (g : α → ℂ) :
    Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (g * (f : α → ℂ)) 2 μ}
  zero_mem' := by
    refine (MemLp.zero' : MemLp (0 : α → ℂ) 2 μ).ae_eq ?_
    filter_upwards [Lp.coeFn_zero (α := α) (E := ℂ) (p := 2) (μ := μ)] with x hx
    simp only [Pi.mul_apply]
    rw [hx]
    simp
  add_mem' := by
    intro f h hf hh
    refine (hf.add hh).ae_eq ?_
    filter_upwards [Lp.coeFn_add f h] with x hx
    simp only [Pi.add_apply, Pi.mul_apply] at hx ⊢
    rw [hx]
    ring
  smul_mem' := by
    intro c f hf
    refine (hf.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    ring

