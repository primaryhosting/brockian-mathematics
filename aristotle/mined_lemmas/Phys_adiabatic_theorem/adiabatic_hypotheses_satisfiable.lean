/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Phys

/-! ## The pure ring algebra behind Kato's construction -/

/-- The algebraic heart of the adiabatic theorem.  In a ring, let `p` be an idempotent,
`k` an element annihilating `p` on both sides (think of `k = H - E` with `p` the spectral
projection of the eigenvalue `E`), `d` the derivative of `p` (so that `d = d*p + p*d`), and `b`
a two-sided inverse of `k + p`.  Then the explicitly constructed element
`b*(1-p)*d*p - p*d*(1-p)*b` has commutator with `k` equal to `d`. -/

theorem adiabatic_hypotheses_satisfiable :
    ∃ (Ham P : ℝ → (Qubit →L[ℂ] Qubit)) (Ev : ℝ → ℝ) (gap : ℝ),
      (∀ s, IsSelfAdjoint (Ham s)) ∧ (∀ s, IsSelfAdjoint (P s)) ∧
      (∀ s, P s * P s = P s) ∧
      (∀ s, Module.finrank ℂ (LinearMap.range (P s : Qubit →ₗ[ℂ] Qubit)) = 1) ∧
      (∀ s, Ham s * P s = (Ev s : ℂ) • P s) ∧ (∀ s, Ham s * P s = P s * Ham s) ∧
      0 < gap ∧
      (∀ s, ∀ v : Qubit, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖) ∧
      ContDiff ℝ 1 Ham ∧ ContDiff ℝ 1 Ev ∧ ContDiff ℝ 2 P := by
  have hnorm0 : ‖qubitVec‖ = 1 := by simp [qubitVec]
  have hidem : qubitProj * qubitProj = qubitProj := by
    ext v
    simp [qubitProj, hnorm0]
  have hPsa : IsSelfAdjoint qubitProj := by
    have h : qubitProj = ContinuousLinearMap.adjoint qubitProj := by
      refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 ?_
      intro x y
      simp [qubitProj, inner_smul_left, inner_smul_right, mul_comm]
    exact (h.symm : ContinuousLinearMap.adjoint qubitProj = qubitProj)
  have hHsa : IsSelfAdjoint qubitHam := by
    have h : qubitHam = ContinuousLinearMap.adjoint qubitHam := by
      refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 ?_
      intro x y
      simp [qubitHam, qubitProj, inner_smul_left, inner_smul_right, inner_sub_left,
        inner_sub_right, mul_comm, Complex.conj_ofNat]
    exact (h.symm : ContinuousLinearMap.adjoint qubitHam = qubitHam)
  have hrank : Module.finrank ℂ (LinearMap.range (qubitProj : Qubit →ₗ[ℂ] Qubit)) = 1 := by
    have hrange : LinearMap.range (qubitProj : Qubit →ₗ[ℂ] Qubit)
        = Submodule.span ℂ {qubitVec} := by
      apply le_antisymm
      · rintro x ⟨v, rfl⟩
        exact Submodule.mem_span_singleton.2 ⟨⟪qubitVec, v⟫_ℂ, rfl⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact ⟨qubitVec, by simp [qubitProj, hnorm0]⟩
    rw [hrange, finrank_span_singleton]
    simp [qubitVec]
  refine ⟨fun _ => qubitHam, fun _ => qubitProj, fun _ => 1, 2, fun _ => hHsa, fun _ => hPsa,
    fun _ => hidem, fun _ => hrank, ?_, ?_, by norm_num, ?_, contDiff_const, contDiff_const,
    contDiff_const⟩
  · intro _
    simp only [qubitHam, sub_mul, smul_mul_assoc, hidem, one_mul]
    push_cast
    module
  · intro _
    simp only [qubitHam, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hidem, one_mul, mul_one]
  · intro _ v hv
    have hv2 : qubitHam v - ((1 : ℝ) : ℂ) • v = (-2 : ℂ) • v := by
      simp only [qubitHam, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, hv, smul_zero]
      push_cast
      module
    rw [hv2, norm_smul]
    simp

end Phys

