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

theorem models_unionAx (hA : A.IsTransitive) (hun : ∀ x ∈ A, (⋃₀ x) ∈ A) :
    (A : Type (u+1)) ⊨ unionAx := by
  rw [unionAx]; realize_simp
  intro a ha
  refine ⟨⋃₀ a, hun a ha, fun w _ => ?_⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨fun ⟨y, hy, hwy⟩ => ⟨y, hy, hA a ha hy, hwy⟩, fun ⟨y, hy, _, hwy⟩ => ⟨y, hy, hwy⟩⟩

