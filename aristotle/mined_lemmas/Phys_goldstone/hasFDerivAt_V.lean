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

theorem hasFDerivAt_V (z : ℂ) : HasFDerivAt V (innerSL ℝ (grad z)) z := by
  have h := (((hasFDerivAt_normSq z).sub_const 1).pow 2)
  convert h using 1
  ext w
  simp only [grad, innerSL_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

