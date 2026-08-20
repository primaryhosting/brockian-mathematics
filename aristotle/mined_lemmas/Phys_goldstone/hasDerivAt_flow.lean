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

theorem hasDerivAt_flow (z : ℂ) : HasDerivAt (fun t : ℝ => flow t z) (gen z) 0 := by
  have h : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I)) Complex.I 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).cexp
    simpa using this
  simpa [flow, gen] using h.mul_const z

