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

theorem models_sepAx (hsep : ∀ p : ZFSet.{u} → Prop, ∀ x ∈ A, ZFSet.sep p x ∈ A)
    (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 1)) : (A : Type (u+1)) ⊨ sepAx k φ := by
  rw [sepAx]; realize_simp; realize_simp
  intro i x hx
  classical
  refine ⟨ZFSet.sep (fun y => ∃ h : y ∈ A, φ.Realize (Sum.elim i fun _ => ⟨y, h⟩)) x,
    hsep _ x hx, fun w hw => ?_⟩
  rw [ZFSet.mem_sep]
  exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hw, h⟩⟩

