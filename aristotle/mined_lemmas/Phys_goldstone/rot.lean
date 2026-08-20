import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Goldstone's theorem** (classical field-theory / mechanical form).

Setting: `V : E → ℝ` is a potential on a real normed space `E`, invariant under a
one-parameter family `g : ℝ → (E ≃L[ℝ] E)` of continuous linear symmetries
(`hinv : ∀ t x, V (g t x) = V x`).  The vacuum `v` minimises `V` (`hmin`).
The symmetry is *spontaneously broken*: the orbit `t ↦ g t v` of the vacuum moves,
i.e. it has a nonzero velocity `w ≠ 0` at `t = 0`.

Conclusion: the mass matrix, i.e. the Hessian `fderiv ℝ (fderiv ℝ V) v` of the potential
at the vacuum, annihilates the nonzero vector `w`.  Thus there is a massless mode
(a Goldstone boson): a nonzero fluctuation direction with vanishing mass term. -/

noncomputable def rot (t : ℝ) : ℂ ≃L[ℝ] ℂ :=
  (rotation (Circle.exp t)).toContinuousLinearEquiv

