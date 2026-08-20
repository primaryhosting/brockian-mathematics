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

theorem models_choiceAx (hA : A.IsTransitive)
    (hrange : ∀ x ∈ A, ∀ f : ↥x → ZFSet.{u}, (∀ i, f i ∈ A) → ZFSet.range f ∈ A) :
    (A : Type (u+1)) ⊨ choiceAx := by
  rw [choiceAx, choiceHyp1, choiceHyp2, choiceConcl]; realize_simp
  intro a ha h1 h2
  classical
  have hchoice : ∀ i : ↥a, ∃ w, w ∈ (i : ZFSet) := by
    intro i
    obtain ⟨w, _, hw⟩ := h1 i (hA a ha i.2) i.2
    exact ⟨w, hw⟩
  set f : ↥a → ZFSet.{u} := fun i => (hchoice i).choose with hf
  have hfmem : ∀ i : ↥a, f i ∈ (i : ZFSet) := fun i => (hchoice i).choose_spec
  have hfA : ∀ i : ↥a, f i ∈ A := fun i => hA _ (hA a ha i.2) (hfmem i)
  refine ⟨ZFSet.range f, hrange a ha f hfA, ?_⟩
  intro y hy hya
  refine ⟨f ⟨y, hya⟩, hfmem ⟨y, hya⟩, ZFSet.mem_range_self _, hfA _, ?_⟩
  intro w _ hwy hwr
  obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hwr
  have hjy : (j : ZFSet) = y :=
    h2 j (hA a ha j.2) y hy j.2 hya (f j) (hfmem j) (hfA j) (hj ▸ hwy)
  have : j = ⟨y, hya⟩ := Subtype.ext hjy
  rw [← hj, this]

