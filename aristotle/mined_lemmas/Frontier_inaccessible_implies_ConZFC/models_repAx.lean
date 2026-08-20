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

theorem models_repAx (h0 : (∅ : ZFSet.{u}) ∈ A)
    (hsep : ∀ p : ZFSet.{u} → Prop, ∀ x ∈ A, ZFSet.sep p x ∈ A)
    (hrange : ∀ x ∈ A, ∀ f : ↥x → ZFSet.{u}, (∀ i, f i ∈ A) → ZFSet.range f ∈ A)
    (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : (A : Type (u+1)) ⊨ repAx k φ := by
  rw [repAx, repHyp, repConcl]; realize_simp; realize_simp
  intro i x hx hfun
  classical
  set P : ZFSet.{u} → ZFSet.{u} → Prop := fun w v =>
    ∃ hw : w ∈ A, ∃ hv : v ∈ A, φ.Realize (Sum.elim i ![⟨w, hw⟩, ⟨v, hv⟩]) with hP
  have huniq : ∀ w ∈ x, ∀ v₁ v₂, P w v₁ → P w v₂ → v₁ = v₂ := by
    rintro w hw v₁ v₂ ⟨hwA, hv₁, h₁⟩ ⟨hwA', hv₂, h₂⟩
    exact hfun w hwA v₁ hv₁ v₂ hv₂ hw h₁ h₂
  set f : ↥x → ZFSet.{u} := fun j => if h : ∃ v, P (j : ZFSet) v then h.choose else ∅ with hf
  have hfA : ∀ j : ↥x, f j ∈ A := by
    intro j
    rw [hf]
    by_cases h : ∃ v, P (j : ZFSet) v
    · simp only [h, dif_pos]
      obtain ⟨_, hv, _⟩ := h.choose_spec
      exact hv
    · simpa [h] using h0
  refine ⟨ZFSet.sep (fun v => ∃ w ∈ x, P w v) (ZFSet.range f), hsep _ _ (hrange x hx f hfA),
    fun v hv => ?_⟩
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨-, w, hwx, hwA, hvA, hφ⟩
    exact ⟨w, hwx, hwA, hφ⟩
  · rintro ⟨w, hwx, hwA, hφ⟩
    have hPwv : P w v := ⟨hwA, hv, hφ⟩
    have hex : ∃ v', P ((⟨w, hwx⟩ : ↥x) : ZFSet) v' := ⟨v, hPwv⟩
    have hfeq : f ⟨w, hwx⟩ = v := by
      have hspec := hex.choose_spec
      have : f ⟨w, hwx⟩ = hex.choose := by rw [hf]; simp only [hex, dif_pos]
      rw [this]
      exact huniq w hwx _ _ hspec hPwv
    exact ⟨hfeq ▸ ZFSet.mem_range_self (⟨w, hwx⟩ : ↥x), w, hwx, hPwv⟩

/-! ## `V_κ` models ZFC for `κ` inaccessible -/

