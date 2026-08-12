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
theorem goldstone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (D : E → (E →L[ℝ] ℝ)) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (Φ : ℝ → E → E) (A : E →L[ℝ] E) (v : E)
    (hV : ∀ x, HasFDerivAt V (D x) x)
    (hD : HasFDerivAt D H v)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hflow : ∀ x, HasDerivAt (fun t => Φ t x) (A x) 0)
    (hinv : ∀ t x, V (Φ t x) = V x)
    (hcrit : D v = 0)
    (hbroken : A v ≠ 0) :
    ∃ w : E, w ≠ 0 ∧ (∀ u : E, H u w = 0) ∧ H w w = 0 := by
  -- Infinitesimal invariance: the derivative of `V` annihilates the generator direction.
  have key : ∀ x, D x (A x) = 0 := by
    intro x
    have h1 : HasDerivAt (fun t => V (Φ t x)) (D x (A x)) 0 := by
      have h := (hV (Φ 0 x)).comp_hasDerivAt 0 (hflow x)
      rwa [hΦ0 x] at h
    have h2 : HasDerivAt (fun t => V (Φ t x)) 0 0 := by
      simp only [hinv]
      exact hasDerivAt_const _ _
    exact h1.unique h2
  -- Differentiate the identity `x ↦ D x (A x) = 0` at the vacuum.
  have hg : HasFDerivAt (fun x => D x (A x)) ((D v).comp A + H.flip (A v)) v :=
    hD.clm_apply (A.hasFDerivAt)
  have hg0 : HasFDerivAt (fun x : E => D x (A x)) (0 : E →L[ℝ] ℝ) v := by
    have : (fun x => D x (A x)) = fun _ : E => (0 : ℝ) := funext key
    rw [this]
    exact hasFDerivAt_const _ _
  have heq : (D v).comp A + H.flip (A v) = 0 := hg.unique hg0
  rw [hcrit] at heq
  simp only [ContinuousLinearMap.zero_comp, zero_add] at heq
  refine ⟨A v, hbroken, ?_, ?_⟩
  · intro u
    have : (H.flip (A v)) u = 0 := by rw [heq]; rfl
    simpa using this
  · have : (H.flip (A v)) (A v) = 0 := by rw [heq]; rfl
    simpa using this

/-! ## A concrete instance: the Mexican-hat potential

`V (x, y) = (x² + y² - 1)²` on `E = ℝ × ℝ`, invariant under the rotation group, with vacuum
`v = (1, 0)`. Rotations move the vacuum, so the symmetry is spontaneously broken, and
`Phys.goldstone` produces the massless angular (Goldstone) mode. The Hessian at `v` is
`H u w = 8 * u.1 * w.1`: massive in the radial direction, massless along the vacuum circle. -/

/-- The Mexican-hat potential on `ℝ × ℝ`. -/
noncomputable def mhV : ℝ × ℝ → ℝ := fun p => (p.1 ^ 2 + p.2 ^ 2 - 1) ^ 2

/-- The differential of the Mexican-hat potential. -/
noncomputable def mhD : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
  (4 * (p.1 ^ 2 + p.2 ^ 2 - 1) * p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
    + (4 * (p.1 ^ 2 + p.2 ^ 2 - 1) * p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The Hessian of the Mexican-hat potential at the vacuum `(1, 0)`: `H u w = 8 * u.1 * w.1`. -/
noncomputable def mhH : ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) :=
  (((8 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ))

/-- The rotation flow on `ℝ × ℝ`, the continuous global symmetry of the Mexican hat. -/
noncomputable def mhFlow : ℝ → ℝ × ℝ → ℝ × ℝ := fun t p =>
  (p.1 * Real.cos t - p.2 * Real.sin t, p.1 * Real.sin t + p.2 * Real.cos t)

/-- The infinitesimal generator of the rotation flow: `A (x, y) = (-y, x)`. -/
def mhA : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

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

lemma mhFlow_zero (p : ℝ × ℝ) : mhFlow 0 p = p := by simp [mhFlow]

lemma mhV_invariant (t : ℝ) (p : ℝ × ℝ) : mhV (mhFlow t p) = mhV p := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [mhV, mhFlow]
  linear_combination ((p.1 ^ 2 + p.2 ^ 2) ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2 + 1)
    - 2 * (p.1 ^ 2 + p.2 ^ 2)) * h

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
theorem mexicanHat_masslessMode :
    ∃ w : ℝ × ℝ, w ≠ 0 ∧ (∀ u : ℝ × ℝ, mhH u w = 0) ∧ mhH w w = 0 := by
  refine goldstone mhV mhD mhH mhFlow mhA ((1 : ℝ), (0 : ℝ)) mhV_hasFDerivAt
    mhD_hasFDerivAt_vacuum mhFlow_zero mhFlow_hasDerivAt mhV_invariant ?_ ?_
  · refine ContinuousLinearMap.ext fun q => ?_
    simp [mhD]
  · simp [mhA, Prod.ext_iff]

/-- The radial direction at the Mexican-hat vacuum is massive: the Hessian does not vanish
identically, so the massless mode of `mexicanHat_masslessMode` is a genuine statement. -/
theorem mexicanHat_radial_massive : mhH ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) = 8 := by
  simp [mhH]

/-- The hypotheses of `Phys.goldstone` are satisfiable (the theorem is not vacuous):
here is a simple instance of the whole hypothesis package, with a flat potential on `E = ℝ`
whose scaling symmetry is broken by the vacuum `v = 1`. -/
theorem goldstone_hypotheses_satisfiable :
    ∃ (V : ℝ → ℝ) (D : ℝ → (ℝ →L[ℝ] ℝ)) (H : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (Φ : ℝ → ℝ → ℝ)
      (A : ℝ →L[ℝ] ℝ) (v : ℝ),
      (∀ x, HasFDerivAt V (D x) x) ∧ HasFDerivAt D H v ∧ (∀ x, Φ 0 x = x) ∧
      (∀ x, HasDerivAt (fun t => Φ t x) (A x) 0) ∧ (∀ t x, V (Φ t x) = V x) ∧
      D v = 0 ∧ A v ≠ 0 := by
  refine ⟨fun _ => 0, fun _ => 0, 0, fun t x => (1 + t) * x, ContinuousLinearMap.id ℝ ℝ, 1,
    fun x => ?_, ?_, fun x => by ring, fun x => ?_, fun t x => rfl, rfl, one_ne_zero⟩
  · simpa using hasFDerivAt_const (0 : ℝ) x
  · simpa using hasFDerivAt_const (0 : ℝ →L[ℝ] ℝ) (1 : ℝ)
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const x

end Phys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

