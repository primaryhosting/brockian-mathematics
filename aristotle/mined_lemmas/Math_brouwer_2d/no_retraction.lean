import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
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

set_option grind.warning false

namespace Math

/-- The squared norm of a complex number, in coordinates. -/

private lemma no_retraction (g : ℂ → ℂ) (hg : Continuous g) (h1 : ∀ z, ‖g z‖ = 1)
    (hb : ∀ z, ‖z‖ = 1 → g z = z) : False := by
  have hmem : ∀ z : ℂ, g z ∈ Metric.sphere (0 : ℂ) 1 := by
    intro z; simpa [mem_sphere_zero_iff_norm] using h1 z
  set G : C(ℂ, Circle) := ⟨fun z => ⟨g z, hmem z⟩, hg.subtype_mk _⟩ with hG
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts G 0
      (Complex.arg (g 0)) (Circle.exp_arg ⟨g 0, hmem 0⟩)
  have hFlift : ∀ z, Circle.exp (F z) = ⟨g z, hmem z⟩ := fun z => congrFun hF z
  set phi : ℝ → ℝ := fun t => F ((Circle.exp t : Circle) : ℂ) with hphi
  have hphicont : Continuous phi := F.continuous.comp (by fun_prop)
  have key : ∀ t : ℝ, ∃ m : ℤ, phi t = t + m * (2 * π) := by
    intro t
    have hz : g ((Circle.exp t : Circle) : ℂ) = ((Circle.exp t : Circle) : ℂ) := hb _ (by simp)
    have hexp : Circle.exp (phi t) = Circle.exp t := by
      rw [hphi]; simp only []; rw [hFlift]; exact Subtype.ext hz
    exact Circle.exp_eq_exp.mp hexp
  set psi : ℝ → ℝ := fun t => phi t - t with hpsi
  have hpsicont : Continuous psi := hphicont.sub continuous_id
  have hper : phi (2 * π) = phi 0 := by rw [hphi]; norm_num
  have hpi : 0 < π := Real.pi_pos
  have hmem2 : phi 0 - π ∈ Set.Icc (psi (2 * π)) (psi 0) := by
    constructor <;> simp [hpsi, hper] <;> linarith
  obtain ⟨t, -, ht⟩ :=
    intermediate_value_Icc' (by linarith : (0:ℝ) ≤ 2 * π) hpsicont.continuousOn hmem2
  obtain ⟨m, hm⟩ := key t
  obtain ⟨n, hn⟩ := key 0
  rw [hpsi] at ht
  simp only [] at ht
  have h3 : π * ((2 * n - 1 - 2 * m : ℤ) : ℝ) = 0 := by push_cast; linarith
  have h4 : ((2 * n - 1 - 2 * m : ℤ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (by positivity)
    · exact h
  have h5 : (2 * n - 1 - 2 * m : ℤ) = 0 := by exact_mod_cast h4
  omega

/-- **Brouwer's fixed point theorem for the closed unit disk in `ℂ`.**

If `f` had no fixed point, the map sending `z` to the point where the ray from `f z` through `z`
meets the unit circle would be a retraction of the disk onto the circle; composing with the
radial retraction of `ℂ` onto the disk contradicts `no_retraction`. -/
