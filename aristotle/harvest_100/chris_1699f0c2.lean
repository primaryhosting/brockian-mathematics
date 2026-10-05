/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/
noncomputable def pd1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun u v => deriv (fun t => f t v) u

/-- Partial derivative with respect to the second variable. -/
noncomputable def pd2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun u v => deriv (fun t => f u t) v

lemma pd1_eq {f g : ℝ → ℝ → ℝ} (h : ∀ u v, HasDerivAt (fun t => f t v) (g u v) u) :
    pd1 f = g := by
  funext u v; exact (h u v).deriv

lemma pd2_eq {f g : ℝ → ℝ → ℝ} (h : ∀ u v, HasDerivAt (fun t => f u t) (g u v) v) :
    pd2 f = g := by
  funext u v; exact (h u v).deriv

/-! ## Parametrized surfaces in `ℝ³` and their Willmore energy

A parametrized surface is given by its three real coordinate functions of two parameters
`(u, v)`.  All the classical local invariants (first and second fundamental forms, mean
curvature, area element) are defined by the standard formulas of classical surface theory. -/

/-- A parametrized surface in `ℝ³`, given by its three coordinate functions. -/
structure ParamSurface where
  /-- First coordinate function. -/
  x : ℝ → ℝ → ℝ
  /-- Second coordinate function. -/
  y : ℝ → ℝ → ℝ
  /-- Third coordinate function. -/
  z : ℝ → ℝ → ℝ

namespace ParamSurface

variable (S : ParamSurface)

/-- Coefficient `E = ⟨f_u, f_u⟩` of the first fundamental form. -/
noncomputable def Efst (u v : ℝ) : ℝ :=
  pd1 S.x u v ^ 2 + pd1 S.y u v ^ 2 + pd1 S.z u v ^ 2

/-- Coefficient `F = ⟨f_u, f_v⟩` of the first fundamental form. -/
noncomputable def Ffst (u v : ℝ) : ℝ :=
  pd1 S.x u v * pd2 S.x u v + pd1 S.y u v * pd2 S.y u v + pd1 S.z u v * pd2 S.z u v

/-- Coefficient `G = ⟨f_v, f_v⟩` of the first fundamental form. -/
noncomputable def Gfst (u v : ℝ) : ℝ :=
  pd2 S.x u v ^ 2 + pd2 S.y u v ^ 2 + pd2 S.z u v ^ 2

/-- First component of the (unnormalized) normal `f_u × f_v`. -/
noncomputable def nrm1 (u v : ℝ) : ℝ := pd1 S.y u v * pd2 S.z u v - pd1 S.z u v * pd2 S.y u v

/-- Second component of the (unnormalized) normal `f_u × f_v`. -/
noncomputable def nrm2 (u v : ℝ) : ℝ := pd1 S.z u v * pd2 S.x u v - pd1 S.x u v * pd2 S.z u v

/-- Third component of the (unnormalized) normal `f_u × f_v`. -/
noncomputable def nrm3 (u v : ℝ) : ℝ := pd1 S.x u v * pd2 S.y u v - pd1 S.y u v * pd2 S.x u v

/-- Length `‖f_u × f_v‖` of the unnormalized normal. -/
noncomputable def nrmLen (u v : ℝ) : ℝ :=
  Real.sqrt (S.nrm1 u v ^ 2 + S.nrm2 u v ^ 2 + S.nrm3 u v ^ 2)

/-- Coefficient `L = ⟨f_uu, n⟩` of the second fundamental form. -/
noncomputable def Lsnd (u v : ℝ) : ℝ :=
  (pd1 (pd1 S.x) u v * S.nrm1 u v + pd1 (pd1 S.y) u v * S.nrm2 u v
      + pd1 (pd1 S.z) u v * S.nrm3 u v) / S.nrmLen u v

/-- Coefficient `M = ⟨f_uv, n⟩` of the second fundamental form. -/
noncomputable def Msnd (u v : ℝ) : ℝ :=
  (pd2 (pd1 S.x) u v * S.nrm1 u v + pd2 (pd1 S.y) u v * S.nrm2 u v
      + pd2 (pd1 S.z) u v * S.nrm3 u v) / S.nrmLen u v

/-- Coefficient `N = ⟨f_vv, n⟩` of the second fundamental form. -/
noncomputable def Nsnd (u v : ℝ) : ℝ :=
  (pd2 (pd2 S.x) u v * S.nrm1 u v + pd2 (pd2 S.y) u v * S.nrm2 u v
      + pd2 (pd2 S.z) u v * S.nrm3 u v) / S.nrmLen u v

/-- The mean curvature `H = (EN - 2FM + GL) / (2(EG - F²))`. -/
noncomputable def meanCurvature (u v : ℝ) : ℝ :=
  (S.Efst u v * S.Nsnd u v - 2 * S.Ffst u v * S.Msnd u v + S.Gfst u v * S.Lsnd u v) /
    (2 * (S.Efst u v * S.Gfst u v - S.Ffst u v ^ 2))

/-- The area element `√(EG - F²)`. -/
noncomputable def areaElement (u v : ℝ) : ℝ :=
  Real.sqrt (S.Efst u v * S.Gfst u v - S.Ffst u v ^ 2)

/-- The Willmore energy `∫∫ H² dA` of a surface parametrized by the square `[0, 2π]²`. -/
noncomputable def willmoreEnergy : ℝ :=
  ∫ v in (0 : ℝ)..(2 * π), ∫ u in (0 : ℝ)..(2 * π),
    S.meanCurvature u v ^ 2 * S.areaElement u v

end ParamSurface

/-- The torus of revolution in `ℝ³` with distance `R` from the axis to the core circle and
tube radius `r`, parametrized by the square `[0, 2π]²`.  For `R = √2 * r` this is (up to
scaling) the stereographic image of the Clifford torus. -/
noncomputable def torusOfRevolution (R r : ℝ) : ParamSurface where
  x := fun u v => (R + r * Real.cos u) * Real.cos v
  y := fun u v => (R + r * Real.cos u) * Real.sin v
  z := fun u _ => r * Real.sin u

/-! ## Derivatives of the torus parametrization -/

section TorusDerivatives

variable (R r : ℝ)

lemma pd1_torus_x :
    pd1 (torusOfRevolution R r).x = fun u v => -(r * sin u) * cos v := by
  apply pd1_eq; intro u v
  simpa [torusOfRevolution] using
    (((Real.hasDerivAt_cos u).const_mul r).const_add R).mul_const (Real.cos v)

lemma pd1_torus_y :
    pd1 (torusOfRevolution R r).y = fun u v => -(r * sin u) * sin v := by
  apply pd1_eq; intro u v
  simpa [torusOfRevolution] using
    (((Real.hasDerivAt_cos u).const_mul r).const_add R).mul_const (Real.sin v)

lemma pd1_torus_z :
    pd1 (torusOfRevolution R r).z = fun u _ => r * cos u := by
  apply pd1_eq; intro u v
  simpa [torusOfRevolution] using (Real.hasDerivAt_sin u).const_mul r

lemma pd2_torus_x :
    pd2 (torusOfRevolution R r).x = fun u v => -((R + r * cos u) * sin v) := by
  apply pd2_eq; intro u v
  simpa [torusOfRevolution] using (Real.hasDerivAt_cos v).const_mul (R + r * cos u)

lemma pd2_torus_y :
    pd2 (torusOfRevolution R r).y = fun u v => (R + r * cos u) * cos v := by
  apply pd2_eq; intro u v
  simpa [torusOfRevolution] using (Real.hasDerivAt_sin v).const_mul (R + r * cos u)

lemma pd2_torus_z :
    pd2 (torusOfRevolution R r).z = fun _ _ => 0 := by
  apply pd2_eq; intro u v
  simpa [torusOfRevolution] using hasDerivAt_const v (r * sin u)

lemma pd1_pd1_torus_x :
    pd1 (pd1 (torusOfRevolution R r).x) = fun u v => -(r * cos u) * cos v := by
  rw [pd1_torus_x]
  apply pd1_eq; intro u v
  simpa using (((Real.hasDerivAt_sin u).const_mul r).neg).mul_const (Real.cos v)

lemma pd1_pd1_torus_y :
    pd1 (pd1 (torusOfRevolution R r).y) = fun u v => -(r * cos u) * sin v := by
  rw [pd1_torus_y]
  apply pd1_eq; intro u v
  simpa using (((Real.hasDerivAt_sin u).const_mul r).neg).mul_const (Real.sin v)

lemma pd1_pd1_torus_z :
    pd1 (pd1 (torusOfRevolution R r).z) = fun u _ => -(r * sin u) := by
  rw [pd1_torus_z]
  apply pd1_eq; intro u v
  simpa using (Real.hasDerivAt_cos u).const_mul r

lemma pd2_pd1_torus_x :
    pd2 (pd1 (torusOfRevolution R r).x) = fun u v => (r * sin u) * sin v := by
  rw [pd1_torus_x]
  apply pd2_eq; intro u v
  simpa using (Real.hasDerivAt_cos v).const_mul (-(r * sin u))

lemma pd2_pd1_torus_y :
    pd2 (pd1 (torusOfRevolution R r).y) = fun u v => -(r * sin u) * cos v := by
  rw [pd1_torus_y]
  apply pd2_eq; intro u v
  simpa using (Real.hasDerivAt_sin v).const_mul (-(r * sin u))

lemma pd2_pd1_torus_z :
    pd2 (pd1 (torusOfRevolution R r).z) = fun _ _ => 0 := by
  rw [pd1_torus_z]
  apply pd2_eq; intro u v
  simpa using hasDerivAt_const v (r * cos u)

lemma pd2_pd2_torus_x :
    pd2 (pd2 (torusOfRevolution R r).x) = fun u v => -((R + r * cos u) * cos v) := by
  rw [pd2_torus_x]
  apply pd2_eq; intro u v
  simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * cos u)).neg

lemma pd2_pd2_torus_y :
    pd2 (pd2 (torusOfRevolution R r).y) = fun u v => -((R + r * cos u) * sin v) := by
  rw [pd2_torus_y]
  apply pd2_eq; intro u v
  simpa using (Real.hasDerivAt_cos v).const_mul (R + r * cos u)

lemma pd2_pd2_torus_z :
    pd2 (pd2 (torusOfRevolution R r).z) = fun _ _ => 0 := by
  rw [pd2_torus_z]
  apply pd2_eq; intro u v
  simpa using hasDerivAt_const v (0 : ℝ)

end TorusDerivatives

/-! ## Fundamental forms of the torus of revolution -/

section TorusForms

variable {R r : ℝ}

lemma torus_Efst (u v : ℝ) : (torusOfRevolution R r).Efst u v = r ^ 2 := by
  simp only [ParamSurface.Efst, pd1_torus_x, pd1_torus_y, pd1_torus_z]
  linear_combination (r ^ 2 * sin u ^ 2) * Real.sin_sq_add_cos_sq v
    + r ^ 2 * Real.sin_sq_add_cos_sq u

lemma torus_Ffst (u v : ℝ) : (torusOfRevolution R r).Ffst u v = 0 := by
  simp only [ParamSurface.Ffst, pd1_torus_x, pd1_torus_y, pd1_torus_z, pd2_torus_x,
    pd2_torus_y, pd2_torus_z]
  ring

lemma torus_Gfst (u v : ℝ) : (torusOfRevolution R r).Gfst u v = (R + r * cos u) ^ 2 := by
  simp only [ParamSurface.Gfst, pd2_torus_x, pd2_torus_y, pd2_torus_z]
  linear_combination (R + r * cos u) ^ 2 * Real.sin_sq_add_cos_sq v

lemma torus_nrm1 (u v : ℝ) :
    (torusOfRevolution R r).nrm1 u v = -(r * cos u * ((R + r * cos u) * cos v)) := by
  simp only [ParamSurface.nrm1, pd1_torus_y, pd1_torus_z, pd2_torus_y, pd2_torus_z]
  ring

lemma torus_nrm2 (u v : ℝ) :
    (torusOfRevolution R r).nrm2 u v = -(r * cos u * ((R + r * cos u) * sin v)) := by
  simp only [ParamSurface.nrm2, pd1_torus_x, pd1_torus_z, pd2_torus_x, pd2_torus_z]
  ring

lemma torus_nrm3 (u v : ℝ) :
    (torusOfRevolution R r).nrm3 u v = -(r * sin u * (R + r * cos u)) := by
  simp only [ParamSurface.nrm3, pd1_torus_x, pd1_torus_y, pd2_torus_x, pd2_torus_y]
  linear_combination (-(r * sin u * (R + r * cos u))) * Real.sin_sq_add_cos_sq v

lemma torus_nrmLen (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).nrmLen u v = r * (R + r * cos u) := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.nrmLen, torus_nrm1, torus_nrm2, torus_nrm3]
  rw [show (-(r * cos u * ((R + r * cos u) * cos v))) ^ 2
        + (-(r * cos u * ((R + r * cos u) * sin v))) ^ 2
        + (-(r * sin u * (R + r * cos u))) ^ 2 = (r * (R + r * cos u)) ^ 2 by
    linear_combination (r ^ 2 * cos u ^ 2 * (R + r * cos u) ^ 2) * Real.sin_sq_add_cos_sq v
      + (r ^ 2 * (R + r * cos u) ^ 2) * Real.sin_sq_add_cos_sq u]
  exact Real.sqrt_sq (by positivity)

lemma torus_Lsnd (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).Lsnd u v = r := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.Lsnd, pd1_pd1_torus_x, pd1_pd1_torus_y, pd1_pd1_torus_z,
    torus_nrm1, torus_nrm2, torus_nrm3, torus_nrmLen hr hR]
  rw [div_eq_iff (by positivity)]
  linear_combination (r ^ 2 * cos u ^ 2 * (R + r * cos u)) * Real.sin_sq_add_cos_sq v
    + (r ^ 2 * (R + r * cos u)) * Real.sin_sq_add_cos_sq u

lemma torus_Msnd (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).Msnd u v = 0 := by
  simp only [ParamSurface.Msnd, pd2_pd1_torus_x, pd2_pd1_torus_y, pd2_pd1_torus_z,
    torus_nrm1, torus_nrm2, torus_nrm3, torus_nrmLen hr hR]
  rw [div_eq_zero_iff]
  left; ring

lemma torus_Nsnd (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).Nsnd u v = (R + r * cos u) * cos u := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.Nsnd, pd2_pd2_torus_x, pd2_pd2_torus_y, pd2_pd2_torus_z,
    torus_nrm1, torus_nrm2, torus_nrm3, torus_nrmLen hr hR]
  rw [div_eq_iff (by positivity)]
  linear_combination (r * cos u * (R + r * cos u) ^ 2) * Real.sin_sq_add_cos_sq v

lemma torus_meanCurvature (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).meanCurvature u v
      = (R + 2 * r * cos u) / (2 * r * (R + r * cos u)) := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.meanCurvature, torus_Efst, torus_Ffst, torus_Gfst,
    torus_Lsnd hr hR, torus_Msnd hr hR, torus_Nsnd hr hR]
  rw [show r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2 = (r * (R + r * cos u)) ^ 2 by ring]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

lemma torus_areaElement (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).areaElement u v = r * (R + r * cos u) := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.areaElement, torus_Efst, torus_Ffst, torus_Gfst]
  rw [show r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2 = (r * (R + r * cos u)) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- The pointwise Willmore integrand of the torus of revolution. -/
lemma torus_integrand (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).meanCurvature u v ^ 2 * (torusOfRevolution R r).areaElement u v
      = (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)) := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  rw [torus_meanCurvature hr hR, torus_areaElement hr hR, div_pow, div_mul_eq_mul_div,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

end TorusForms

/-! ## The Willmore energy of the torus of revolution -/

section TorusIntegral

variable {R r : ℝ}

/-- An explicit primitive of the Willmore integrand of the torus of revolution. -/
noncomputable def torusPrimitive (R r : ℝ) : ℝ → ℝ := fun t =>
  1 / (4 * r) * (4 * (r * sin t) + R ^ 2 / Real.sqrt (R ^ 2 - r ^ 2) *
    (t - 2 * arctan (r * sin t / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * cos t))))

/-- The key algebraic identity behind the antiderivative. -/
lemma arctan_deriv_identity {s c sn : ℝ} (hr : 0 < r) (hR : r < R) (hs0 : 0 < s)
    (hs2 : s ^ 2 = R ^ 2 - r ^ 2) (hsc : sn ^ 2 + c ^ 2 = 1) (hw : 0 < R + r * c) :
    1 - 2 * ((1 / (1 + (r * sn / (R + s + r * c)) ^ 2)) *
      ((r * c * (R + s + r * c) - r * sn * (-(r * sn))) / (R + s + r * c) ^ 2))
      = s / (R + r * c) := by
  have hD : 0 < R + s + r * c := by linarith
  have hK : 0 < 2 * (R + s) * (R + r * c) := by nlinarith
  have h1 : 1 + (r * sn / (R + s + r * c)) ^ 2
      = (2 * (R + s) * (R + r * c)) / (R + s + r * c) ^ 2 := by
    field_simp
    linear_combination hs2 + r ^ 2 * hsc
  have h1' : 1 / (1 + (r * sn / (R + s + r * c)) ^ 2)
      = (R + s + r * c) ^ 2 / (2 * (R + s) * (R + r * c)) := by
    rw [h1, one_div_div]
  rw [h1']
  have hstep : (R + s + r * c) ^ 2 / (2 * (R + s) * (R + r * c)) *
      ((r * c * (R + s + r * c) - r * sn * (-(r * sn))) / (R + s + r * c) ^ 2)
      = (r * c * (R + s) + r ^ 2) / (2 * (R + s) * (R + r * c)) := by
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring_nf
    linear_combination (r ^ 2 * (R + s + r * c) ^ 2 * (2 * (R + s) * (R + r * c))) * hsc
  rw [hstep]
  have hRs : (R + s) ≠ 0 := by nlinarith
  have hw' : (R + r * c) ≠ 0 := ne_of_gt hw
  field_simp
  linear_combination -hs2

lemma hasDerivAt_torusPrimitive (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (torusPrimitive R r)
      ((R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u))) u := by
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hRr
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hRr.le
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  have hD : 0 < R + s + r * cos u := by linarith
  have hN : HasDerivAt (fun t : ℝ => r * sin t) (r * cos u) u :=
    (Real.hasDerivAt_sin u).const_mul r
  have hDd : HasDerivAt (fun t : ℝ => R + s + r * cos t) (-(r * sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + s)
  have hq : HasDerivAt (fun t : ℝ => r * sin t / (R + s + r * cos t))
      ((r * cos u * (R + s + r * cos u) - r * sin u * (-(r * sin u)))
        / (R + s + r * cos u) ^ 2) u := hN.div hDd (ne_of_gt hD)
  have ha := (Real.hasDerivAt_arctan (r * sin u / (R + s + r * cos u))).comp u hq
  have h1 : HasDerivAt (fun t : ℝ => t - 2 * arctan (r * sin t / (R + s + r * cos t)))
      (1 - 2 * ((1 / (1 + (r * sin u / (R + s + r * cos u)) ^ 2)) *
        ((r * cos u * (R + s + r * cos u) - r * sin u * (-(r * sin u)))
          / (R + s + r * cos u) ^ 2))) u :=
    (hasDerivAt_id u).sub (ha.const_mul 2)
  have h2 := ((hN.const_mul 4).add (h1.const_mul (R ^ 2 / s))).const_mul (1 / (4 * r))
  have hkey := arctan_deriv_identity (R := R) (r := r) (s := s) (c := cos u) (sn := sin u)
    hr hR hs0 hs2 (Real.sin_sq_add_cos_sq u) hw
  rw [hkey] at h2
  have hval : 1 / (4 * r) * (4 * (r * cos u) + R ^ 2 / s * (s / (R + r * cos u)))
      = (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)) := by
    field_simp
    ring
  rw [hval] at h2
  exact h2

lemma torus_integrand_continuous (hr : 0 < r) (hR : r < R) :
    Continuous (fun u : ℝ => (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u))) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  have hw : 0 < R + r * cos x := by nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  positivity

/-- The integral of the Willmore integrand over one period in `u`. -/
lemma torus_u_integral (hr : 0 < r) (hR : r < R) :
    (∫ u in (0 : ℝ)..(2 * π), (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)))
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hRr
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_torusPrimitive hr hR x)
      ((torus_integrand_continuous hr hR).intervalIntegrable _ _)]
  simp only [torusPrimitive, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  rw [show (r : ℝ) * 0 = 0 by ring]
  simp only [zero_div, Real.arctan_zero]
  field_simp
  ring

/-- **The Willmore energy of the torus of revolution.** -/
theorem willmoreEnergy_torusOfRevolution (hr : 0 < r) (hR : r < R) :
    (torusOfRevolution R r).willmoreEnergy = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hRr
  have hinner : ∀ v : ℝ, (∫ u in (0 : ℝ)..(2 * π),
      (torusOfRevolution R r).meanCurvature u v ^ 2 * (torusOfRevolution R r).areaElement u v)
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    intro v
    rw [show (fun u : ℝ => (torusOfRevolution R r).meanCurvature u v ^ 2 *
        (torusOfRevolution R r).areaElement u v)
        = fun u : ℝ => (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)) from
      funext fun u => torus_integrand hr hR u v]
    exact torus_u_integral hr hR
  rw [ParamSurface.willmoreEnergy]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)))
    (fun v _ => hinner v)]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

end TorusIntegral

/-! ## The Willmore conjecture for tori of revolution -/

/-- The lower bound `2π²` for the energy of a torus of revolution, with the equality case. -/
lemma willmore_bound_of_revolution {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * π ^ 2 ≤ π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) ∧
      (π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r) := by
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hRr
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hRr.le
  have hpi : 0 < π ^ 2 := by positivity
  have hden : 0 < r * s := by positivity
  -- the key inequality `R⁴ ≥ 4r²(R² - r²)`, i.e. `R² ≥ 2rs`
  have hsq : R ^ 2 - 2 * (r * s) ≥ 0 := by
    nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (R ^ 2 - 2 * (r * s)), sq_nonneg (r * s)]
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · constructor
    · intro h
      rw [div_eq_iff (ne_of_gt hden)] at h
      have hR2 : R ^ 2 = 2 * (r * s) := by nlinarith
      have h2r : R ^ 2 = 2 * r ^ 2 := by nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2)]
      have h1 : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      have hfac : (R - Real.sqrt 2 * r) * (R + Real.sqrt 2 * r) = 0 := by nlinarith
      have hpos : 0 < R + Real.sqrt 2 * r := by
        have : 0 ≤ Real.sqrt 2 * r := by positivity
        linarith
      rcases mul_eq_zero.mp hfac with h' | h'
      · linarith
      · linarith
    · intro h
      subst h
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsr : s = r := by
        rw [hs, show (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 by nlinarith]
        exact Real.sqrt_sq hr.le
      rw [hsr]
      field_simp
      nlinarith

/-- **The Willmore conjecture for tori of revolution.**

For a torus of revolution in `ℝ³` with core radius `R` and tube radius `r` (`0 < r < R`),
the Willmore energy `∫∫ H² dA` — defined through the classical formulas for the first and
second fundamental forms of a parametrized surface — is at least `2π²`, the Clifford torus
(`R = √2 · r`) realizes the value `2π²`, and it is the unique minimizer in this family.

This is the axially symmetric case of the Willmore conjecture, proved here in full; the
general case for all immersed tori is the theorem of Marques and Neves. -/
theorem willmore_conjecture :
    (∀ R r : ℝ, 0 < r → r < R → 2 * π ^ 2 ≤ (torusOfRevolution R r).willmoreEnergy) ∧
    (∀ r : ℝ, 0 < r → (torusOfRevolution (Real.sqrt 2 * r) r).willmoreEnergy = 2 * π ^ 2) ∧
    (∀ R r : ℝ, 0 < r → r < R →
      ((torusOfRevolution R r).willmoreEnergy = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r)) := by
  have hclifford : ∀ r : ℝ, 0 < r → r < Real.sqrt 2 * r := by
    intro r hr
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      have : Real.sqrt 1 < Real.sqrt 2 := by
        apply Real.sqrt_lt_sqrt <;> norm_num
      simpa using this
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro R r hr hR
    rw [willmoreEnergy_torusOfRevolution hr hR]
    exact (willmore_bound_of_revolution hr hR).1
  · intro r hr
    rw [willmoreEnergy_torusOfRevolution hr (hclifford r hr)]
    exact ((willmore_bound_of_revolution hr (hclifford r hr)).2).2 rfl
  · intro R r hr hR
    rw [willmoreEnergy_torusOfRevolution hr hR]
    exact (willmore_bound_of_revolution hr hR).2

end Frontier

