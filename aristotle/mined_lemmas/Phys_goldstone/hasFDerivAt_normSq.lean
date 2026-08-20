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

theorem hasFDerivAt_normSq (z : ℂ) :
    HasFDerivAt (fun x : ℂ => ⟪x, x⟫) ((2 : ℝ) • innerSL ℝ z) z := by
  have h := (hasFDerivAt_id z).inner ℝ (hasFDerivAt_id z)
  convert h using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, id_eq, real_inner_comm w z]
  ring

