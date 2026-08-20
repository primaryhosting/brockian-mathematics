/-
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Goldstone's theorem** (classical / field-theoretic form).

Setting: a real normed space `E` of field configurations (order parameters), a potential
`V : E → ℝ` with first derivative `D x = dV x` at every point and second derivative
(Hessian) `H = d(dV) v` at a vacuum `v`.

The continuous global symmetry is a one-parameter family of transformations `Φ t : E → E`
with `Φ 0 = id`, infinitesimal generator `A` (so `d/dt (Φ t x)|_{t=0} = A x`), leaving the
potential invariant: `V (Φ t x) = V x`.

`v` is a vacuum: it is a critical point of `V` (`D v = 0`).
The symmetry is *spontaneously broken* at `v`: the vacuum is not invariant, `A v ≠ 0`.

Conclusion: there is a nonzero mode `w` (namely `w = A v`, the direction along the orbit of
the vacuum) that is annihilated by the Hessian — a massless (zero-frequency) excitation. -/

lemma mhFlow_hasDerivAt (p : ℝ × ℝ) : HasDerivAt (fun t => mhFlow t p) (mhA p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p.1 * Real.cos t - p.2 * Real.sin t) (-p.2) 0 := by
    simpa using ((Real.hasDerivAt_cos 0).const_mul p.1).sub ((Real.hasDerivAt_sin 0).const_mul p.2)
  have h2 : HasDerivAt (fun t : ℝ => p.1 * Real.sin t + p.2 * Real.cos t) p.1 0 := by
    simpa using ((Real.hasDerivAt_sin 0).const_mul p.1).add ((Real.hasDerivAt_cos 0).const_mul p.2)
  simpa [mhFlow, mhA] using h1.prodMk h2

/-- **Goldstone mode of the Mexican-hat potential.** Applying `Phys.goldstone` to the rotation
symmetry of `V (x, y) = (x² + y² - 1)²` at the vacuum `(1, 0)` yields a nonzero mode annihilated
by the Hessian. Together with `mexicanHat_radial_massive`, this exhibits a genuine massless
direction of a Hessian that is not identically zero. -/
