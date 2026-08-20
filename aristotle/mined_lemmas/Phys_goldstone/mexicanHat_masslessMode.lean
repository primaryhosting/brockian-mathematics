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

theorem mexicanHat_masslessMode :
    ∃ w : ℝ × ℝ, w ≠ 0 ∧ (∀ u : ℝ × ℝ, mhH u w = 0) ∧ mhH w w = 0 := by
  refine goldstone mhV mhD mhH mhFlow mhA ((1 : ℝ), (0 : ℝ)) mhV_hasFDerivAt
    mhD_hasFDerivAt_vacuum mhFlow_zero mhFlow_hasDerivAt mhV_invariant ?_ ?_
  · refine ContinuousLinearMap.ext fun q => ?_
    simp [mhD]
  · simp [mhA, Prod.ext_iff]

/-- The radial direction at the Mexican-hat vacuum is massive: the Hessian does not vanish
identically, so the massless mode of `mexicanHat_masslessMode` is a genuine statement. -/
