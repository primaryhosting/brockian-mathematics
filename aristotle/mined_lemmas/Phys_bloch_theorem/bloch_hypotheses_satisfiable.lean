/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Eigenstates of a periodic Hamiltonian are Bloch waves `e^{ikx} u_k(x)`.

The development is organised as follows.

* `Phys.schrodinger` : the one-dimensional Schrödinger operator `ψ ↦ -ψ'' + V ψ`.
* `Phys.IsEigenstate` : `ψ` solves `-ψ'' + V ψ = E ψ`.
* `Phys.isEigenstate_translate` : the Hamiltonian commutes with translation by a period of `V`.
* `Phys.norm_eq_one_of_bounded` : a bounded nonzero `ψ` with `ψ (x + a) = c ψ (x)` has `‖c‖ = 1`.
* `Phys.bloch_theorem` : the main result.
* `Phys.bloch_theorem_of_translation_eigenvalue` : the same conclusion starting directly from
  the translation-eigenvalue property.
* `Phys.bloch_hypotheses_satisfiable` : the hypotheses of `bloch_theorem` are consistent
  (they are met by the constant potential with the constant eigenstate).
-/

namespace Phys

open Complex

/-- The one-dimensional Schrödinger operator with potential `V` (units `ℏ²/2m = 1`),
acting on functions `ψ : ℝ → ℂ`. -/

theorem bloch_hypotheses_satisfiable :
    ∃ (a : ℝ) (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ),
      0 < a ∧ (∀ x, V (x + a) = V x) ∧ ContDiff ℝ 2 psi ∧ IsEigenstate V E psi ∧
      (∃ x₀, psi x₀ ≠ 0) ∧ (∃ C, ∀ x, ‖psi x‖ ≤ C) ∧
      (∀ φ : ℝ → ℂ, ContDiff ℝ 2 φ → IsEigenstate V E φ →
        (∃ C, ∀ x, ‖φ x‖ ≤ C) → ∃ c : ℂ, ∀ x, φ x = c * psi x) := by
  refine ⟨1, fun _ => 0, 0, fun _ => 1, one_pos, fun _ => rfl, contDiff_const, ?_,
    ⟨0, one_ne_zero⟩, ⟨1, fun _ => by simp⟩, ?_⟩
  · intro x
    simp [schrodinger]
  · rintro φ hφ hE ⟨C, hC⟩
    -- `φ'' = 0` pointwise
    have hzero : ∀ x, deriv (deriv φ) x = 0 := by
      intro x
      have := hE x
      simp only [schrodinger, zero_mul] at this
      simpa using this
    have hdiff1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hdiff2 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
    -- hence `φ'` is a constant `b`
    set b : ℂ := deriv φ 0 with hb
    have hconst : ∀ x, deriv φ x = b := fun x => is_const_of_deriv_eq_zero hdiff2 hzero x 0
    -- hence `φ x = φ 0 + b * x`
    have hlin : ∀ x : ℝ, φ x = φ 0 + b * x := by
      have hg : Differentiable ℝ (fun x : ℝ => φ x - b * (x : ℂ)) := by
        refine hdiff1.sub ?_
        intro x
        exact ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul b).differentiableAt
      have hgz : ∀ x : ℝ, deriv (fun x : ℝ => φ x - b * (x : ℂ)) x = 0 := by
        intro x
        have h1 : HasDerivAt (fun t : ℝ => b * (t : ℂ)) b x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul b
        have h2 : HasDerivAt φ b x := by
          have := (hdiff1 x).hasDerivAt
          rwa [hconst x] at this
        simpa using (h2.sub h1).deriv
      intro x
      have := is_const_of_deriv_eq_zero hg hgz x 0
      simp only [Complex.ofReal_zero, mul_zero, sub_zero] at this
      linear_combination this
    -- boundedness forces `b = 0`
    have hb0 : b = 0 := by
      by_contra hbne
      have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hbne
      obtain ⟨n, hn⟩ := exists_nat_gt ((C + ‖φ 0‖) / ‖b‖)
      have hnb : C + ‖φ 0‖ < ‖b‖ * n := by
        rw [div_lt_iff₀ hbpos] at hn
        linarith
      have hle := hC (n : ℝ)
      rw [hlin (n : ℝ)] at hle
      have h1 : ‖b * ((n : ℝ) : ℂ)‖ - ‖φ 0‖ ≤ ‖φ 0 + b * ((n : ℝ) : ℂ)‖ := by
        have := norm_sub_norm_le (b * ((n : ℝ) : ℂ)) (-(φ 0))
        simpa [sub_neg_eq_add, add_comm] using this
      have h2 : ‖b * ((n : ℝ) : ℂ)‖ = ‖b‖ * n := by
        simp
      rw [h2] at h1
      linarith
    refine ⟨φ 0, fun x => ?_⟩
    rw [hlin x, hb0]
    ring

end Phys

import Mathlib

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

