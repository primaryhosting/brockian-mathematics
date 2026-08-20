import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

theorem isNSSolution_scale {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (h : IsNSSolution ν u p) (c : ℝ) :
    IsNSSolution ν (fun t x => c • u (c ^ 2 * t) (c • x))
      (fun t x => c ^ 2 * p (c ^ 2 * t) (c • x)) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E3 => ((c ^ 2 * q.1 : ℝ), c • q.2)) :=
    (contDiff_const.mul contDiff_fst).prodMk (contDiff_snd.const_smul c)
  have hspace : ∀ t : ℝ, ContDiff ℝ (2 : ℕ) (u t) := fun t =>
    (h.contDiff_space t).of_le (WithTop.coe_le_coe.mpr le_top)
  have hspaceD : ∀ t : ℝ, Differentiable ℝ (u t) := fun t =>
    (hspace t).differentiable (by norm_num)
  have hpD : ∀ t : ℝ, Differentiable ℝ (p t) := fun t =>
    (h.contDiff_space_pressure t).differentiable (by simp)
  refine ⟨(h.smooth_u.comp hscale).const_smul c, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (h.smooth_p.comp hscale)
  · intro t ht x
    rw [divg_comp_smul (u (c ^ 2 * t)) (hspaceD _) c x,
      h.div_free _ (by positivity) (c • x), mul_zero]
  · intro t ht x
    have ht' : (0 : ℝ) ≤ c ^ 2 * t := by positivity
    have hmom := h.momentum (c ^ 2 * t) ht' (c • x)
    -- time derivative
    have hA : deriv (fun s => c • u (c ^ 2 * s) (c • x)) t
        = c ^ 3 • deriv (fun s => u s (c • x)) (c ^ 2 * t) := by
      have h1 : HasDerivAt (fun s : ℝ => c ^ 2 * s) (c ^ 2) t := by
        simpa using (hasDerivAt_id t).const_mul (c ^ 2)
      have h2 : HasDerivAt (fun s : ℝ => u (c ^ 2 * s) (c • x))
          (c ^ 2 • deriv (fun s => u s (c • x)) (c ^ 2 * t)) t :=
        ((h.differentiable_time (c • x) (c ^ 2 * t)).hasDerivAt).scomp t h1
      have h3 := (h2.const_smul c).deriv
      rw [show (fun s => c • u (c ^ 2 * s) (c • x))
          = (c • fun s => u (c ^ 2 * s) (c • x)) from rfl, h3, smul_smul]
      ring_nf
    have hB : convective (fun y => c • u (c ^ 2 * t) (c • y)) x
        = c ^ 3 • convective (u (c ^ 2 * t)) (c • x) :=
      convective_scale _ (hspaceD _) c x
    have hC : lapl (fun y => c • u (c ^ 2 * t) (c • y)) x
        = c ^ 3 • lapl (u (c ^ 2 * t)) (c • x) := by
      rw [lapl_const_smul (fun y => u (c ^ 2 * t) (c • y))
        ((hspace _).comp ((contDiff_id.const_smul c))) c x,
        lapl_comp_smul (u (c ^ 2 * t)) (hspace _) c x, smul_smul]
      ring_nf
    have hD : grad (fun y => c ^ 2 * p (c ^ 2 * t) (c • y)) x
        = c ^ 3 • grad (p (c ^ 2 * t)) (c • x) := by
      rw [grad_const_smul (fun y => p (c ^ 2 * t) (c • y)) (c ^ 2) x
          (((hpD _) (c • x)).comp x ((differentiable_id.const_smul c) x)),
        grad_comp_smul (p (c ^ 2 * t)) (hpD _) c x, smul_smul]
      ring_nf
    simp only [hA, hB, hC, hD]
    rw [← smul_add, hmom, smul_sub, smul_comm (c ^ 3) ν]

/-- Kinetic energy under the Navier–Stokes scaling of a velocity field on `ℝ³`. -/
