/-
Models of ZFC given by suitable classes of ZFC sets.
-/
import RequestProject.SetLanguage

/-!
# Classes of sets that model ZFC

We isolate a set of closure conditions on a class `P : ZFSet.{u} → Prop`
(`Frontier.IsZFCClass`) which guarantee that the structure with domain `{x : ZFSet // P x}`
and the real membership relation is a model of the first-order theory `Frontier.ZFC`.

The conditions are: transitivity, closure under pairing, unions, power sets, the presence of
`ω`, and closure under (second-order) replacement.

The class of *all* sets satisfies these conditions, so `ZFSet.{u}` itself is a model of ZFC.
-/

universe u w

namespace Frontier

open FirstOrder Language ZFSet

/-- The `setLang`-structure on a type equipped with a binary relation. -/

theorem models_replAx (k : ℕ) (φ : setLang.{u + 1}.Formula (Fin k ⊕ Fin 2)) :
    VClass P ⊨ replAx k φ := by
  classical
  rw [realize_replAx]
  rintro p ⟨a, ha⟩ hfun
  set Φ : VClass P → VClass P → Prop := fun x y => φ.Realize (Sum.elim p ![x, y]) with hΦ
  set g : ZFSet.{u} → ZFSet.{u} := fun w =>
    if hw : ∃ y : VClass P, ∃ hw : P w, Φ ⟨w, hw⟩ y then (hw.choose : {x : ZFSet.{u} // P x}).1
    else ∅ with hg
  have hgP : ∀ y ∈ a, P (g y) := by
    intro y _
    by_cases hy : ∃ y' : VClass P, ∃ hy : P y, Φ ⟨y, hy⟩ y'
    · simp only [hg, dif_pos hy]
      exact (hy.choose : {x : ZFSet.{u} // P x}).2
    · simp only [hg, dif_neg hy]
      exact h.empty
  obtain ⟨b₀, hb₀, hb₀mem⟩ := h.replacement g ha hgP
  refine ⟨⟨ZFSet.sep (fun z => ∃ hz : P z, ∃ x : VClass P,
      (x : {x : ZFSet.{u} // P x}).1 ∈ a ∧ Φ x ⟨z, hz⟩) b₀, h.sep _ hb₀⟩, ?_⟩
  rintro ⟨y, hy⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨-, hz, x, hxa, hΦx⟩
    exact ⟨x, hxa, hΦx⟩
  · rintro ⟨x, hxa, hΦx⟩
    have hxP : P (x : {x : ZFSet.{u} // P x}).1 := (x : {x : ZFSet.{u} // P x}).2
    have hex : ∃ y' : VClass P, ∃ hw : P (x : {x : ZFSet.{u} // P x}).1,
        Φ ⟨(x : {x : ZFSet.{u} // P x}).1, hw⟩ y' := ⟨⟨y, hy⟩, hxP, hΦx⟩
    have hgx : g (x : {x : ZFSet.{u} // P x}).1 = y := by
      simp only [hg, dif_pos hex]
      obtain ⟨hw, hΦw⟩ := hex.choose_spec
      have : (⟨(x : {x : ZFSet.{u} // P x}).1, hw⟩ : {x : ZFSet.{u} // P x}) = x := Subtype.ext rfl
      rw [this] at hΦw
      have := hfun x hex.choose ⟨y, hy⟩ ⟨⟨hxa, hΦw⟩, hΦx⟩
      exact congrArg Subtype.val this
    refine ⟨(hb₀mem y).2 ⟨_, hxa, hgx⟩, hy, x, hxa, hΦx⟩

