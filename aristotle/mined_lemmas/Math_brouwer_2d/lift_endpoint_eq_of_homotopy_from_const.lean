/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Every continuous self-map of the closed 2-disk has a fixed point.

Mathlib does not contain Brouwer's fixed point theorem, so it is developed here.  The proof is the
classical degree-theoretic argument, carried out through the homotopy lifting property for
covering maps (`IsCoveringMap.liftHomotopy`) applied to the covering `Circle.exp : ℝ → Circle`:

* `Math.sub_eq_sub_of_circleExp_eq`: two continuous real functions on a preconnected space with
  the same image under `Circle.exp` differ by a constant (lifts are unique up to a constant).
* `Math.lift_endpoint_eq_of_homotopy_from_const`: if a homotopy of loops in the circle starts at
  a constant loop, then any continuous lift of its terminal loop has equal endpoints, i.e. the
  terminal loop has winding number `0`.
* `Math.brouwer_2d_complex`: if a continuous self-map `f` of the closed unit disk in `ℂ` had no
  fixed point, then `v z = (z - f z)/‖z - f z‖` would define a map of the disk into the circle;
  restricted to the boundary circle it is never antipodal to the identity, so it has winding
  number `1`, contradicting the previous lemma applied to the homotopy `(t, s) ↦ v (t e^{2πis})`.
* `Math.brouwer_2d`: transported to `EuclideanSpace ℝ (Fin 2)` along the linear isometry
  equivalence `Complex.orthonormalBasisOneI.repr`.
-/

namespace Math

open Complex Metric Set unitInterval

/-- Two continuous real functions on a preconnected space whose images under `Circle.exp` agree
differ by a constant. -/

theorem lift_endpoint_eq_of_homotopy_from_const (H : C(I × I, Circle))
    (hconst : ∀ s : I, H (0, s) = H (0, 0))
    (hloop : ∀ t : I, H (t, 0) = H (t, 1))
    (θ : I → ℝ) (hθ : Continuous θ) (hlift : ∀ s : I, Circle.exp (θ s) = H (1, s)) :
    θ 1 = θ 0 := by
  set c : ℝ := Complex.arg ((H (0, 0) : Circle) : ℂ) with hc
  have H_0 : ∀ a : I, H (0, a) = Circle.exp c := by
    intro a; rw [hconst a, hc, Circle.exp_arg]
  set F : C(I, ℝ) := ContinuousMap.const I c with hF
  set Ht := Circle.isCoveringMap_exp.liftHomotopy H F H_0 with hHt
  have hlifts : ∀ p : I × I, Circle.exp (Ht p) = H p := fun p =>
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H F H_0) p
  have hz : ∀ a : I, Ht (0, a) = c := fun a =>
    Circle.isCoveringMap_exp.liftHomotopy_zero H F H_0 a
  have hcont1 : Continuous fun t : I => Ht (t, 1) := Ht.continuous.comp (by fun_prop)
  have hcont0 : Continuous fun t : I => Ht (t, 0) := Ht.continuous.comp (by fun_prop)
  have hd := sub_eq_sub_of_circleExp_eq hcont1 hcont0
    (fun t => by rw [hlifts, hlifts, hloop t]) 1 0
  have hd0 : Ht ((0 : I), (1 : I)) - Ht ((0 : I), (0 : I)) = 0 := by rw [hz, hz]; ring
  have hd1 : Ht ((1 : I), (1 : I)) = Ht ((1 : I), (0 : I)) := by
    simp only at hd; linarith [hd, hd0]
  have hcontH1 : Continuous fun s : I => Ht (1, s) := Ht.continuous.comp (by fun_prop)
  have h2 := sub_eq_sub_of_circleExp_eq hθ hcontH1 (fun s => by rw [hlift, hlifts]) 1 0
  simp only at h2
  linarith

/-- A complex number of norm one other than `-1` lies in the slit plane. -/
