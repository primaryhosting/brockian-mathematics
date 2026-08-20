import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Noether identity.**  If the potential `V` (with gradient field `G`) is invariant under a
one-parameter flow `Φ` whose infinitesimal generator is `K` (i.e. `Φ 0 = id` and
`(d/dt) Φ t x |_{t=0} = K x`), then the gradient of `V` is everywhere orthogonal to the
direction of the symmetry orbit. -/

theorem hasFDerivAt_grad : HasFDerivAt grad hess 1 := by
  have h1 : HasFDerivAt (fun x : ℂ => 4 * (⟪x, x⟫ - 1))
      ((4 : ℝ) • ((2 : ℝ) • innerSL ℝ (1 : ℂ))) (1 : ℂ) := by
    simpa using (((hasFDerivAt_normSq 1).sub_const 1).const_mul (4 : ℝ))
  have h2 := h1.smul (hasFDerivAt_id (1 : ℂ))
  convert h2 using 1
  ext w
  have h3 : ⟪(1 : ℂ), (1 : ℂ)⟫ = (1 : ℝ) := by simp
  simp only [hess, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul, h3, id_eq, sub_self, mul_zero, zero_smul, zero_add,
    smul_smul]
  ring_nf

