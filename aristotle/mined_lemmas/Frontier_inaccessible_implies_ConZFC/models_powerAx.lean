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

theorem models_powerAx (hA : A.IsTransitive) (hpow : ∀ x ∈ A, x.powerset ∈ A) :
    (A : Type (u+1)) ⊨ powerAx := by
  rw [powerAx]; realize_simp
  intro a ha
  refine ⟨a.powerset, hpow a ha, fun w hw => ?_⟩
  rw [ZFSet.mem_powerset]
  exact ⟨fun hsub y _ hyw => hsub hyw, fun h y hyw => h y (hA w hw hyw) hyw⟩

