/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

open NormedSpace

namespace Frontier

section

variable {A : Type*} [CStarAlgebra A]

/-- A `ℚ`-normed-algebra structure, obtained by restricting scalars from `ℂ`; it is needed
to talk about `NormedSpace.exp` in a C⋆-algebra. -/
noncomputable local instance normedAlgebraRatOfCStarAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

/-- `exp (t • H)` commutes with `H`. -/
lemma commute_exp_smul (H : A) (t : ℝ) : Commute (exp (t • H)) H :=
  ((Commute.refl H).smul_left t).exp_left

lemma exp_smul_mul_exp_neg_smul (H : A) (t : ℝ) :
    exp (t • H) * exp ((-t) • H) = 1 := by
  rw [← exp_add_of_commute (((Commute.refl H).smul_left t).smul_right (-t))]
  simp

lemma exp_neg_smul_mul_exp_smul (H : A) (t : ℝ) :
    exp ((-t) • H) * exp (t • H) = 1 := by
  simpa using exp_smul_mul_exp_neg_smul H (-t)

/-- If `H` is anti-self-adjoint then `exp (t • H)` is unitary. -/
lemma exp_smul_mem_unitary {H : A} (hH : star H = -H) (t : ℝ) :
    exp (t • H) ∈ unitary A := by
  refine exp_mem_unitary_of_mem_skewAdjoint ?_
  rw [skewAdjoint.mem_iff, star_smul, hH]
  simp

/-- Conjugation by the unitary `exp (t • H)` preserves the norm. -/
lemma norm_conj_exp {H : A} (hH : star H = -H) (t : ℝ) (x : A) :
    ‖exp (t • H) * x * exp ((-t) • H)‖ = ‖x‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (exp_smul_mem_unitary hH (-t)),
    CStarRing.norm_mem_unitary_mul _ (exp_smul_mem_unitary hH t)]

/-- Crude bound on the norm of a commutator. -/
lemma norm_lie_le (x y : A) : ‖⁅x, y⁆‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rw [Ring.lie_def]
  calc ‖x * y - y * x‖ ≤ ‖x * y‖ + ‖y * x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- Derivative of the backwards Heisenberg evolution `r ↦ exp (-r • H) * b * exp (r • H)`. -/
lemma hasDerivAt_conj (H b : A) (s : ℝ) :
    HasDerivAt (fun r : ℝ => exp ((-r) • H) * b * exp (r • H))
      (exp ((-s) • H) * ⁅b, H⁆ * exp (s • H)) s := by
  have hneg : ∀ r : ℝ, exp ((-r) • H) = exp (r • (-H)) := by
    intro r; rw [neg_smul, smul_neg]
  have h1 : HasDerivAt (fun r : ℝ => exp (r • H)) (exp (s • H) * H) s :=
    hasDerivAt_exp_smul_const H s
  have h2 : HasDerivAt (fun r : ℝ => exp ((-r) • H)) (-(exp ((-s) • H) * H)) s := by
    have h := hasDerivAt_exp_smul_const (-H) s
    simp only [hneg]
    simpa [mul_neg] using h
  have h3 := (h2.mul_const b).mul h1
  refine h3.congr_deriv ?_
  have hc : exp (s • H) * H = H * exp (s • H) := commute_exp_smul H s
  rw [Ring.lie_def, hc]
  noncomm_ring

/-- Conjugation by the unitary `exp (-t • H)` preserves the norm. -/
lemma norm_conj_exp' {H : A} (hH : star H = -H) (t : ℝ) (x : A) :
    ‖exp ((-t) • H) * x * exp (t • H)‖ = ‖x‖ := by
  simpa using norm_conj_exp hH (-t) x

/-- **Key intermediate lemma (Lieb–Robinson estimate for the backwards evolution).**
The commutator of `a` with the backwards-evolved `b` moves away from its initial value
at most linearly in time, with speed controlled by `‖⁅b, H⁆‖`. -/
lemma norm_lie_conj_sub_lie_le {H : A} (hH : star H = -H) (a b : A) (t : ℝ) :
    ‖⁅a, exp ((-t) • H) * b * exp (t • H)⁆ - ⁅a, b⁆‖ ≤ 2 * ‖a‖ * ‖⁅b, H⁆‖ * |t| := by
  set f : ℝ → A := fun r : ℝ => ⁅a, exp ((-r) • H) * b * exp (r • H)⁆ with hf
  set f' : ℝ → A := fun r : ℝ => ⁅a, exp ((-r) • H) * ⁅b, H⁆ * exp (r • H)⁆ with hf'
  have hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s := by
    intro s
    have h := hasDerivAt_conj H b s
    have h2 := (h.const_mul a).sub (h.mul_const a)
    simpa only [hf, hf', Ring.lie_def] using h2
  have hbound : ∀ s : ℝ, ‖f' s‖ ≤ 2 * ‖a‖ * ‖⁅b, H⁆‖ := by
    intro s
    have h1 : ‖f' s‖ ≤ 2 * ‖a‖ * ‖exp ((-s) • H) * ⁅b, H⁆ * exp (s • H)‖ :=
      norm_lie_le _ _
    rwa [norm_conj_exp' hH s ⁅b, H⁆] at h1
  have hmvt := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := 2 * ‖a‖ * ‖⁅b, H⁆‖)
    (fun x _ => (hderiv x).hasDerivWithinAt) (fun x _ => hbound x)
    (Set.mem_univ 0) (Set.mem_univ t)
  have h0 : f 0 = ⁅a, b⁆ := by simp [hf]
  have hft : f t = ⁅a, exp ((-t) • H) * b * exp (t • H)⁆ := rfl
  rw [h0, hft] at hmvt
  simpa only [Real.norm_eq_abs, sub_zero] using hmvt

/-- **Lieb–Robinson bound (base case): an effective light cone for local dynamics.**

Let `A` be a unital C⋆-algebra and `H` an anti-self-adjoint element (`H = i·(Hamiltonian)`),
so that `U t = exp (t • H)` is the unitary time-evolution group.  For observables `a` and `b`,
the Heisenberg-evolved observable `a t = U t * a * U (-t)` satisfies

`‖⁅a t, b⁆‖ ≤ ‖⁅a, b⁆‖ + 2 ‖a‖ ‖⁅b, H⁆‖ |t|`.

Thus the commutator of `b` with the evolved observable can become nonzero only at a rate
governed by the interaction strength `‖⁅b, H⁆‖` felt by `b`: outside the resulting light cone
the dynamics is (approximately) local.  In particular, if `b` commutes both with `a` and with
the generator `H`, then `⁅a t, b⁆ = 0` for all times. -/
theorem lieb_robinson {A : Type*} [CStarAlgebra A] (H a b : A) (hH : star H = -H) (t : ℝ) :
    ‖⁅exp (t • H) * a * exp ((-t) • H), b⁆‖ ≤ ‖⁅a, b⁆‖ + 2 * ‖a‖ * ‖⁅b, H⁆‖ * |t| := by
  have e1 : exp (t • H) * exp ((-t) • H) = 1 := exp_smul_mul_exp_neg_smul H t
  have hconj : ⁅exp (t • H) * a * exp ((-t) • H), b⁆
      = exp (t • H) * ⁅a, exp ((-t) • H) * b * exp (t • H)⁆ * exp ((-t) • H) := by
    rw [Ring.lie_def, Ring.lie_def]
    calc exp (t • H) * a * exp ((-t) • H) * b - b * (exp (t • H) * a * exp ((-t) • H))
        = exp (t • H) * a * exp ((-t) • H) * b * (exp (t • H) * exp ((-t) • H))
          - (exp (t • H) * exp ((-t) • H)) * (b * (exp (t • H) * a * exp ((-t) • H))) := by
          rw [e1]; noncomm_ring
      _ = exp (t • H) * (a * (exp ((-t) • H) * b * exp (t • H))
            - exp ((-t) • H) * b * exp (t • H) * a) * exp ((-t) • H) := by noncomm_ring
  rw [hconj, norm_conj_exp hH]
  have h := norm_lie_conj_sub_lie_le hH a b t
  have htri : ‖⁅a, exp ((-t) • H) * b * exp (t • H)⁆‖
      ≤ ‖⁅a, exp ((-t) • H) * b * exp (t • H)⁆ - ⁅a, b⁆‖ + ‖⁅a, b⁆‖ := by
    simpa using norm_add_le (⁅a, exp ((-t) • H) * b * exp (t • H)⁆ - ⁅a, b⁆) ⁅a, b⁆
  calc ‖⁅a, exp ((-t) • H) * b * exp (t • H)⁆‖
      ≤ ‖⁅a, exp ((-t) • H) * b * exp (t • H)⁆ - ⁅a, b⁆‖ + ‖⁅a, b⁆‖ := htri
    _ ≤ 2 * ‖a‖ * ‖⁅b, H⁆‖ * |t| + ‖⁅a, b⁆‖ := by gcongr
    _ = ‖⁅a, b⁆‖ + 2 * ‖a‖ * ‖⁅b, H⁆‖ * |t| := by ring

/-- Strict light cone: if `b` commutes with `a` and with the generator, then the commutator
of `b` with the evolved observable vanishes at all times. -/
theorem lie_evolve_eq_zero {A : Type*} [CStarAlgebra A] (H a b : A) (hH : star H = -H)
    (hab : ⁅a, b⁆ = 0) (hbH : ⁅b, H⁆ = 0) (t : ℝ) :
    ⁅exp (t • H) * a * exp ((-t) • H), b⁆ = 0 := by
  have h := lieb_robinson H a b hH t
  rw [hab, hbH] at h
  simp only [norm_zero, mul_zero, zero_mul, add_zero] at h
  exact norm_le_zero_iff.mp h

end

end Frontier

