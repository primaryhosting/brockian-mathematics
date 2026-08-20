import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem models_infinityAx (hA : A.IsTransitive) (hom : ZFSet.omega.{u} ∈ A) :
    (A : Type (u+1)) ⊨ infinityAx := by
  rw [infinityAx]; realize_simp
  refine ⟨ZFSet.omega, ⟨∅, ZFSet.omega_zero, hA _ hom ZFSet.omega_zero,
    fun w _ => ZFSet.notMem_empty w⟩, hom, ?_⟩
  intro y _ hyo
  refine ⟨insert y y, ZFSet.omega_succ hyo, hA _ hom (ZFSet.omega_succ hyo), fun w _ => ?_⟩
  rw [ZFSet.mem_insert_iff]
  tauto

