/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology
open scoped ComplexInnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Aux


theorem hasGenerator_of_adjoint (hU : IsUnitaryGroup U) (w z : H)
    (h : ∀ x y, HasGenerator U x y → ⟪y, w⟫ = ⟪x, z⟫) : HasGenerator U w z := by
  obtain ⟨u, yu, hu, hue⟩ := surjective_sub_I hU (z - Complex.I • w)
  have hzero : z - yu - Complex.I • w + Complex.I • u = 0 := by
    have h2 : z - Complex.I • w - (yu - Complex.I • u) = 0 := by rw [hue]; abel
    rw [← h2]; abel
  have key : ∀ x y : H, HasGenerator U x y → ⟪y + Complex.I • x, w - u⟫ = 0 := by
    intro x y hy
    have hz : ⟪y, w⟫ = ⟪x, z⟫ := h x y hy
    have hs : ⟪y, u⟫ = ⟪x, yu⟫ := hasGenerator_symmetric hU hy hu
    have hexp : ⟪x, z⟫ - ⟪x, yu⟫ - Complex.I * ⟪x, w⟫ + Complex.I * ⟪x, u⟫ = 0 := by
      have h3 : (⟪x, z - yu - Complex.I • w + Complex.I • u⟫ : ℂ) = 0 := by
        rw [hzero, inner_zero_right]
      simpa [inner_add_right, inner_sub_right, inner_smul_right] using h3
    simp only [inner_add_left, inner_sub_right, inner_smul_left, Complex.conj_I]
    linear_combination hz - hs + hexp
  have hwu : w = u := by
    obtain ⟨p, yp, hp, hpe⟩ := surjective_add_I hU (w - u)
    have h4 := key p yp hp
    rw [hpe] at h4
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h4)
  have hyz : yu = z := by
    rw [hwu] at hzero
    have hz0 : z - yu = 0 := by simpa using hzero
    exact (sub_eq_zero.mp hz0).symm
  rw [← hwu] at hu
  rwa [hyz] at hu

/-- **Stone's theorem**: a strongly continuous one-parameter unitary group `U` on a complex
Hilbert space has a self-adjoint generator `A`, characterized by
`d/dt (U t x)|_{t=0} = i • A x` (so that formally `U t = exp (i t A)`).

Explicitly:
1. the generator is well defined as an operator (the derivative determines `A x` uniquely);
2. its domain is a linear subspace on which `A` acts linearly;
3. its domain is dense;
4. `A` is symmetric;
5. `A` is self-adjoint: any `w` such that `⟪A x, w⟫ = ⟪x, z⟫` for all `x` in the domain
   already lies in the domain, and `A w = z`. -/
