import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Math

/-- Algebraic identity: the positive root of `‖a + t v‖² = 1` (with `‖a‖ ≤ 1`, `v ≠ 0`)
is `t = (-⟪a,v⟫ + √(⟪a,v⟫² + ‖v‖²(1-‖a‖²)))/‖v‖²`. -/

theorem no_retraction_of_plane_onto_circle (r : ℂ → ℂ) (hr : Continuous r)
    (hnorm : ∀ z, ‖r z‖ = 1) (hfix : ∀ z, ‖z‖ = 1 → r z = z) : False := by
  have hmem : ∀ z : ℂ, r z ∈ Metric.sphere (0 : ℂ) 1 := by
    intro z; simp [hnorm z]
  let R : C(ℂ, Circle) := ⟨fun z => ⟨r z, hmem z⟩, Continuous.subtype_mk hr _⟩
  obtain ⟨g, ⟨-, hg⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts R 0
    (Complex.arg (R 0)) (Circle.exp_arg _)
  have key : ∀ t : ℝ, Circle.exp (g (Complex.exp (t * I))) = Circle.exp t := by
    intro t
    have h1 : Circle.exp (g (Complex.exp (t * I))) = R (Complex.exp (t * I)) := congrFun hg _
    rw [h1]
    apply Subtype.ext
    show r (Complex.exp (t * I)) = _
    rw [hfix _ (Complex.norm_exp_ofReal_mul_I t), Circle.coe_exp]
  set φ : ℝ → ℝ := fun t => g (Complex.exp (t * I)) with hφ
  have hφc : Continuous φ := by
    apply g.continuous.comp; fun_prop
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hint : ∀ t : ℝ, ∃ n : ℤ, φ t - t = n * (2 * Real.pi) := by
    intro t
    rw [← Circle.exp_eq_one, Circle.exp_sub, key t, div_self']
  set ψ : ℝ → ℝ := fun t => (φ t - t) / (2 * Real.pi) with hψ
  have hψc : Continuous ψ := by fun_prop
  have hψint : ∀ t, ∃ n : ℤ, ψ t = n := by
    intro t
    obtain ⟨n, hn⟩ := hint t
    refine ⟨n, ?_⟩
    rw [hψ]
    field_simp [hn]
    linarith [hn]
  have hper : φ (2 * Real.pi) = φ 0 := by simp [hφ]
  have hend : ψ (2 * Real.pi) = ψ 0 - 1 := by
    rw [hψ]; simp only [hper]; field_simp; ring
  obtain ⟨m, hm⟩ := hψint 0
  have hmem2 : ψ 0 - 1 / 2 ∈ Set.Icc (ψ (2 * Real.pi)) (ψ 0) := by
    rw [hend]; constructor <;> linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc' hpi.le hψc.continuousOn hmem2
  obtain ⟨n, hn⟩ := hψint t
  rw [hn, hm] at ht
  have h2 : (2 * n : ℝ) = 2 * m - 1 := by linarith
  have h3 : (2 * n : ℤ) = 2 * m - 1 := by exact_mod_cast h2
  omega

/-- **Brouwer's fixed point theorem in dimension 2**, complex-plane version:
every continuous self-map of the closed unit disk in `ℂ` has a fixed point. -/
