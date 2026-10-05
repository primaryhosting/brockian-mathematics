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

theorem sub_eq_sub_of_circleExp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {θ φ : X → ℝ} (hθ : Continuous θ) (hφ : Continuous φ)
    (h : ∀ x, Circle.exp (θ x) = Circle.exp (φ x)) (x y : X) :
    θ x - φ x = θ y - φ y := by
  set g : X → ℝ := fun z => θ z - φ z with hg
  have hgc : Continuous g := hθ.sub hφ
  have hint : ∀ z, ∃ m : ℤ, g z = m * (2 * Real.pi) := by
    intro z
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (h z)
    exact ⟨m, by simp [hg, hm]⟩
  have hpi := Real.pi_pos
  have key : ∀ a b : X, ¬ (g a < g b) := by
    intro a b hlt
    obtain ⟨m, hm⟩ := hint a
    obtain ⟨n, hn⟩ := hint b
    have hmn : (m : ℝ) < n := by nlinarith
    have hmn' : m < n := by exact_mod_cast hmn
    have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn'
    have hle : g a + Real.pi ≤ g b := by nlinarith
    obtain ⟨z, hz⟩ := intermediate_value_univ a b hgc
      (show g a + Real.pi ∈ Icc (g a) (g b) from ⟨by linarith, hle⟩)
    obtain ⟨k, hk⟩ := hint z
    rw [hk, hm] at hz
    have hhalf : (2 * (k - m) : ℝ) = 1 := by
      have : ((k : ℝ) - m) * (2 * Real.pi) = Real.pi := by linarith
      nlinarith
    have : (2 * (k - m) : ℤ) = 1 := by exact_mod_cast hhalf
    omega
  have h1 := key x y
  have h2 := key y x
  simp only [not_lt] at h1 h2
  linarith

/-- If a homotopy of loops `H` in the circle starts at a constant loop, then any continuous
lift of its terminal loop has equal endpoints. -/
