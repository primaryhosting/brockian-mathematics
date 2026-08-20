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
-/

open Metric Set Complex

namespace Math

noncomputable section

/-! ## Step 1: the radial projection onto the closed unit disk of `ℂ`. -/

/-- Radial projection of `ℂ` onto the closed unit disk. -/

theorem no_retraction (g : ℂ → ℂ) (hg : Continuous g) (hnorm : ∀ z, ‖g z‖ = 1)
    (hbdry : ∀ z, ‖z‖ = 1 → g z = z) : False := by
  -- Upgrade `g` to a continuous map into the circle.
  have hmem : ∀ z : ℂ, g z ∈ Submonoid.unitSphere ℂ := by
    intro z
    simpa [Submonoid.unitSphere, mem_sphere_iff_norm] using hnorm z
  let G : C(ℂ, Circle) := ⟨fun z => ⟨g z, hmem z⟩, by fun_prop⟩
  -- Since `ℂ` is simply connected and locally path connected, `G` lifts along the
  -- covering map `Circle.exp : ℝ → Circle`.
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      G 0 (Complex.arg ((G 0 : Circle) : ℂ)) (Circle.exp_arg (G 0))
  -- The boundary circle, parametrized by angle.
  set w : ℝ → ℂ := fun s => ((Circle.exp s : Circle) : ℂ) with hw
  have hwc : Continuous w := by fun_prop
  have hwnorm : ∀ s, ‖w s‖ = 1 := fun s => Circle.norm_coe _
  have hGw : ∀ s, G (w s) = Circle.exp s := fun s =>
    Circle.coe_inj.mp (hbdry (w s) (hwnorm s))
  -- The lift differs from the angle by an integer multiple of `2 * π`.
  have key : ∀ s : ℝ, ∃ m : ℤ, F (w s) = s + m * (2 * Real.pi) := by
    intro s
    rw [← Circle.exp_eq_exp]
    have hFs : Circle.exp (F (w s)) = G (w s) := congrFun hFlift (w s)
    rw [hFs, hGw s]
  have hw0 : w (2 * Real.pi) = w 0 := by
    have : Circle.exp (2 * Real.pi) = Circle.exp 0 :=
      Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
    simp only [hw, this]
  -- The normalized difference is a continuous integer-valued function, which is
  -- impossible since it drops by exactly `1` along the loop.
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  set h : ℝ → ℝ := fun s => (F (w s) - s) / (2 * Real.pi) with hh
  have hcont : Continuous h := by fun_prop
  have hint : ∀ s, ∃ m : ℤ, h s = m := by
    intro s
    obtain ⟨m, hm⟩ := key s
    refine ⟨m, ?_⟩
    have hd : F (w s) - s = (m:ℝ) * (2*Real.pi) := by rw [hm]; ring
    simp only [hh, hd]
    field_simp
  have hend : h (2 * Real.pi) = h 0 - 1 := by
    simp only [hh, hw0]
    field_simp
    ring
  obtain ⟨k, hk⟩ := hint 0
  have hsub := intermediate_value_uIcc (f := h) (a := (0:ℝ)) (b := 2*Real.pi) hcont.continuousOn
  obtain ⟨s, -, hs⟩ := hsub (show (k:ℝ) - 1/2 ∈ uIcc (h 0) (h (2*Real.pi)) by
    rw [Set.mem_uIcc]; right; rw [hend, hk]; constructor <;> linarith)
  obtain ⟨m, hm⟩ := hint s
  rw [hm] at hs
  have h2 : (2*m + 1 : ℤ) = 2*k := by
    have : ((2*m+1 : ℤ) : ℝ) = ((2*k : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ## Step 3: a fixed-point-free self map of the disk yields a retraction. -/

/-- If a continuous self-map `f` of the closed unit disk has no fixed point, then the map
sending `z` to the point where the ray from `f z` through `z` meets the unit circle is a
continuous retraction of `ℂ` onto the unit circle. -/
