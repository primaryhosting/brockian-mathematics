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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real ComplexConjugate InnerProductSpace
open Complex MeasureTheory Submodule AddCircle Module

namespace Brockian.Weyl.DeficiencyODE

/-! ## Abstract setting: symmetric operators, deficiency vectors, essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

/-- A densely defined operator `T` with domain `D` is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

theorem diagOp_essentiallySelfAdjoint (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    EssentiallySelfAdjoint (diagOp b lam) := by
  have hdef : ∀ (z : ℂ), z.re = 0 → z ≠ 0 →
      ∀ u : H, IsDeficiencyVector (diagOp b lam) z u → u = 0 := by
    intro z hz hz0 u hu
    have hcoeff : ∀ i, ⟪b i, u⟫_ℂ = 0 := by
      intro i
      have h := hu (spanBasis b i)
      rw [diagOp_basis, spanBasis_apply, ← sub_smul, inner_smul_left] at h
      rcases mul_eq_zero.1 h with h1 | h2
      · exfalso
        have : ((lam i : ℂ) - z) = 0 := by
          simpa using congrArg (starRingEnd ℂ) h1
        have him : z.im = 0 := by
          have := congrArg Complex.im this
          simpa using this
        exact hz0 (Complex.ext hz him)
      · exact h2
    have : b.repr u = 0 := by
      ext i
      rw [b.repr_apply_apply]
      simpa using hcoeff i
    have := congrArg b.repr.symm this
    simpa using this
  refine ⟨?_, diagOp_isSymmetric b lam, ?_, ?_⟩
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact b.dense_span
  · exact hdef Complex.I (by simp) Complex.I_ne_zero
  · exact hdef (-Complex.I) (by simp) (by simp [Complex.I_ne_zero])

end Abstract

/-! ## The one-dimensional Schrödinger operator on a circle

We work on `L²` of the circle `AddCircle T` of circumference `T > 0`, with the Schrödinger
operator `-d²/dx² + V` for a constant potential `V : ℝ`, defined on the domain of trigonometric
polynomials (the algebraic span of the Fourier basis).  The Fourier modes are genuine classical
eigenfunctions of this differential expression, as certified by `schrodingerExpr_fourier` below.
-/

section Schrodinger

variable (T : ℝ) [hT : Fact (0 < T)] (V : ℝ)

/-- The eigenvalue of `-d²/dx² + V` on the `n`-th Fourier mode of the circle `AddCircle T`. -/
