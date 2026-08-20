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

lemma mhV_hasFDerivAt (p : ℝ × ℝ) : HasFDerivAt mhV (mhD p) p := by
  have hx : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hy : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 - 1)
      ((2 * p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (2 * p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have h := ((hx.mul hx).add (hy.mul hy)).sub_const 1
    simp only [← pow_two] at h
    convert h using 1
    refine ContinuousLinearMap.ext fun q => ?_
    simp [two_mul]
    ring
  have h2 := hf.mul hf
  simp only [← pow_two] at h2
  convert h2 using 1
  refine ContinuousLinearMap.ext fun q => ?_
  simp [mhD]
  ring

