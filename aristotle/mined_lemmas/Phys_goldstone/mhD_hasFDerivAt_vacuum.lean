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

lemma mhD_hasFDerivAt_vacuum : HasFDerivAt mhD mhH ((1 : ℝ), (0 : ℝ)) := by
  set p : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with hp
  have hx : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hy : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hf : HasFDerivAt (fun q : ℝ × ℝ => 4 * (q.1 ^ 2 + q.2 ^ 2 - 1))
      ((8 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (0 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have h := (((hx.mul hx).add (hy.mul hy)).sub_const 1).const_mul (4 : ℝ)
    simp only [← pow_two] at h
    convert h using 1
    refine ContinuousLinearMap.ext fun q => ?_
    simp [hp]
    ring
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => (4 * (q.1 ^ 2 + q.2 ^ 2 - 1)) * q.1)
      ((8 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have h := hf.mul hx
    convert h using 1
    refine ContinuousLinearMap.ext fun q => ?_
    simp [hp]
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => (4 * (q.1 ^ 2 + q.2 ^ 2 - 1)) * q.2)
      (0 : ℝ × ℝ →L[ℝ] ℝ) p := by
    have h := hf.mul hy
    convert h using 1
    refine ContinuousLinearMap.ext fun q => ?_
    simp [hp]
  have hD := (h1.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
    (h2.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hfun : mhD = fun q : ℝ × ℝ =>
      ((4 * (q.1 ^ 2 + q.2 ^ 2 - 1)) * q.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + ((4 * (q.1 ^ 2 + q.2 ^ 2 - 1)) * q.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    funext q; simp [mhD]
  rw [hfun]
  convert hD using 1
  refine ContinuousLinearMap.ext fun q => ContinuousLinearMap.ext fun r => ?_
  simp [mhH]

