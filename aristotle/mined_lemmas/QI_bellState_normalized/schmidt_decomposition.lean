import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

theorem schmidt_decomposition (psi : Fin m × Fin n → ℂ) (hpsi : ∑ x, ‖psi x‖ ^ 2 = 1) :
    (∃ D : SchmidtDecomp psi, ∑ k, D.lam k ^ 2 = 1) ∧
      ∀ D D' : SchmidtDecomp psi, D.coeffs = D'.coeffs := by
  constructor
  · obtain ⟨D⟩ := exists_schmidtDecomp psi
    refine ⟨D, ?_⟩
    have h1 := trace_pow_rho D 0
    rw [pow_one, trace_rho, hpsi] at h1
    have : ∑ k, ((D.lam k : ℂ)) ^ 2 = 1 := by
      rw [← h1]; norm_num
    exact_mod_cast this
  · intro D D'
    have hsum : ∀ (E : SchmidtDecomp psi) (p : ℕ),
        ((Multiset.map (· ^ 2) E.coeffs).map (· ^ p)).sum = ∑ k, (E.lam k ^ 2) ^ p := by
      intro E p
      simp [SchmidtDecomp.coeffs, Function.comp_def, Finset.sum]
    have hpos : ∀ (E : SchmidtDecomp psi), ∀ x ∈ Multiset.map (· ^ 2) E.coeffs, 0 < x := by
      intro E x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hy
      exact pow_pos (E.lam_pos k) 2
    have key : Multiset.map (· ^ 2) D.coeffs = Multiset.map (· ^ 2) D'.coeffs := by
      refine multiset_eq_of_powerSum_eq (hpos D) (hpos D') fun p hp => ?_
      rw [hsum D p, hsum D' p]
      exact sum_lam_pow D D' p hp
    have hsqrt : ∀ (E : SchmidtDecomp psi),
        Multiset.map Real.sqrt (Multiset.map (· ^ 2) E.coeffs) = E.coeffs := by
      intro E
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
      intro x hx
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
      simpa using Real.sqrt_sq (E.lam_pos k).le
    rw [← hsqrt D, ← hsqrt D', key]

end QI

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

