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

theorem V_flow (t : ℝ) (z : ℂ) : V (flow t z) = V z := by
  simp only [V, flow, real_inner_self_eq_norm_sq, norm_mul, Complex.norm_exp]
  simp

