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

theorem schwartzToL2_mem_freeSymbolMaximal_domain (f : SchwartzMap Real Complex) :
    schwartzToL2 f ∈ freeSymbolMaximal.domain := by
  change MemLp (freeSymbol * (schwartzToL2 f : Real -> Complex)) 2 volume
  have hm : MemLp (freeSymbolMulSchwartz f : Real -> Complex) 2 volume :=
    (freeSymbolMulSchwartz f).memLp 2 volume
  refine hm.ae_eq ?_
  filter_upwards [coeFn_schwartzToL2 f] with xi hxi
  simp only [Pi.mul_apply, freeSymbolMulSchwartz_apply]
  rw [hxi]

/-- The normalized spectral free Laplacian `F^{-1} M_{4*pi^2*xi^2} F`. -/
