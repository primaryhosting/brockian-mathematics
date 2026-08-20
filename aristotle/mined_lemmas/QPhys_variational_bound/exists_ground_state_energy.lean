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

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- Expansion of the expectation value `⟪ψ, H ψ⟫` in an orthonormal eigenbasis `b` of `H`
with (real) eigenvalues `E`. -/

theorem exists_ground_state_energy [Nontrivial V] (H : V →ₗ[ℂ] V) (hH : H.IsSymmetric) :
    ∃ E0 : ℝ, End.HasEigenvalue H (E0 : ℂ) ∧ (∀ μ : ℝ, End.HasEigenvalue H (μ : ℂ) → E0 ≤ μ) ∧
      ∀ ψ : V, ψ ≠ 0 → E0 ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  have hpos : 0 < finrank ℂ V := finrank_pos
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (finrank ℂ V)))
      (hH.eigenvalues (rfl : finrank ℂ V = finrank ℂ V)) ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  refine ⟨hH.eigenvalues rfl i0, hH.hasEigenvalue_eigenvalues rfl i0, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨i, hi⟩ := hH.exists_eigenvalues_eq (rfl : finrank ℂ V = finrank ℂ V) hμ
    have : hH.eigenvalues rfl i = μ := Complex.ofReal_inj.mp hi
    exact this ▸ hi0 i (Finset.mem_univ i)
  · intro ψ hψ
    refine variational_bound H hH _ (fun μ hμ => ?_) ψ hψ
    obtain ⟨i, hi⟩ := hH.exists_eigenvalues_eq (rfl : finrank ℂ V = finrank ℂ V) hμ
    have : hH.eigenvalues rfl i = μ := Complex.ofReal_inj.mp hi
    exact this ▸ hi0 i (Finset.mem_univ i)

end QPhys

