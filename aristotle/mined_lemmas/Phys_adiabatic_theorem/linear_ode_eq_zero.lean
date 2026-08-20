/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

open Set

/-- **Uniqueness for a linear ODE in a Banach algebra.**
If `X : ℝ → F` solves the linear differential equation `X' t = A t * X t` with continuous
coefficient `A` and vanishing initial datum, then `X` vanishes identically. -/

theorem linear_ode_eq_zero {F : Type*} [NormedRing F] [NormedAlgebra ℝ F]
    {A : ℝ → F} (hA : Continuous A) {X : ℝ → F}
    (hX : ∀ t, HasDerivAt X (A t * X t) t) (h0 : X 0 = 0) :
    ∀ t, X t = 0 := by
  intro t
  set b : ℝ := |t| + 1 with hb
  set a : ℝ := -b with ha
  have habs : |t| < b := by simp [hb]
  have ht : t ∈ Ioo a b := by
    constructor
    · have := neg_abs_le t
      have : -b < -|t| := by simpa using habs
      linarith [neg_abs_le t]
    · exact lt_of_le_of_lt (le_abs_self t) habs
  have ht0 : (0 : ℝ) ∈ Ioo a b := by
    have h1 : (0 : ℝ) < b := by positivity
    exact ⟨by simpa [ha] using h1, h1⟩
  -- a uniform bound for `‖A ·‖` on the compact interval `[a, b]`
  obtain ⟨x₀, -, hx₀⟩ : ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖A y‖ ≤ ‖A x‖ :=
    let ⟨x, hx, hmax⟩ := IsCompact.exists_isMaxOn (isCompact_Icc (a := a) (b := b))
      ⟨0, ht0.1.le, ht0.2.le⟩ hA.norm.continuousOn
    ⟨x, hx, fun y hy => hmax hy⟩
  set C : ℝ≥0 := ⟨‖A x₀‖, norm_nonneg _⟩ with hC
  have hlip : ∀ s ∈ Ioo a b, LipschitzOnWith C (fun x : F => A s * x) (univ : Set F) := by
    intro s hs
    refine (LipschitzWith.of_dist_le_mul ?_).lipschitzOnWith
    intro x y
    have h1 : ‖A s * x - A s * y‖ ≤ ‖A s‖ * ‖x - y‖ := by
      rw [← mul_sub]; exact norm_mul_le _ _
    have h2 : ‖A s‖ ≤ (C : ℝ) := hx₀ s ⟨hs.1.le, hs.2.le⟩
    calc dist (A s * x) (A s * y) = ‖A s * x - A s * y‖ := dist_eq_norm _ _
      _ ≤ ‖A s‖ * ‖x - y‖ := h1
      _ ≤ (C : ℝ) * ‖x - y‖ := by
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = (C : ℝ) * dist x y := by rw [dist_eq_norm]
  have key : EqOn X (fun _ : ℝ => (0 : F)) (Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo (v := fun s x => A s * x) (s := fun _ => univ)
      hlip ht0 (fun s _ => ⟨hX s, mem_univ _⟩) (fun s _ => ⟨?_, mem_univ _⟩) (by simpa using h0)
    simpa using (hasDerivAt_const s (0 : F))
  simpa using key ht

/-- If `p` is an idempotent in a ring and `d` satisfies the Leibniz identity coming from
differentiating `p * p = p`, then `p * d * p = 0`. -/
