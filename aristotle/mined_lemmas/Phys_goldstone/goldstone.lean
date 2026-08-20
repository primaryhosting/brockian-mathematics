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
