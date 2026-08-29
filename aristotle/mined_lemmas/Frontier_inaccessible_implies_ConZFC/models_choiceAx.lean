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

theorem models_choiceAx : VClass P ⊨ choiceAx.{u + 1} := by
  rw [realize_choiceAx]
  rintro ⟨a, ha⟩ ⟨hne, hdisj⟩
  -- a choice function on the members of `a`
  classical
  set g : ZFSet.{u} → ZFSet.{u} := fun x => if hx : ∃ z, z ∈ x then hx.choose else ∅ with hg
  have hgmem : ∀ x : ZFSet.{u}, (∃ z, z ∈ x) → g x ∈ x := by
    intro x hx
    simp only [hg, dif_pos hx]
    exact hx.choose_spec
  have hgP : ∀ y ∈ a, P (g y) := by
    intro y hy
    by_cases hx : ∃ z, z ∈ y
    · exact h.mem_trans (h.mem_trans ha hy) (hgmem y hx)
    · simp only [hg, dif_neg hx]
      exact h.empty
  obtain ⟨c, hc, hcmem⟩ := h.replacement g ha hgP
  refine ⟨⟨c, hc⟩, ?_⟩
  rintro ⟨x, hx⟩ hxa
  have hxne : ∃ z, z ∈ x := by
    obtain ⟨⟨z, hz⟩, hzx⟩ := hne ⟨x, hx⟩ hxa
    exact ⟨z, hzx⟩
  have hgx : g x ∈ x := hgmem x hxne
  refine ⟨⟨g x, h.mem_trans hx hgx⟩, ⟨hgx, (hcmem _).2 ⟨x, hxa, rfl⟩⟩, ?_⟩
  rintro ⟨y', hy'⟩ ⟨hy'x, hy'c⟩
  obtain ⟨x', hx'a, hx'⟩ := (hcmem y').1 hy'c
  have hx'P : P x' := h.mem_trans ha hx'a
  have hxx' : (⟨x, hx⟩ : {x : ZFSet.{u} // P x}) = ⟨x', hx'P⟩ := by
    refine hdisj ⟨x, hx⟩ ⟨x', hx'P⟩ ⟨⟨hxa, hx'a⟩, ⟨y', hy'⟩, hy'x, ?_⟩
    have hx'ne : ∃ z, z ∈ x' := by
      obtain ⟨⟨z, hz⟩, hzx⟩ := hne ⟨x', hx'P⟩ hx'a
      exact ⟨z, hzx⟩
    show y' ∈ x'
    rw [← hx']
    exact hgmem x' hx'ne
  have : x = x' := congrArg Subtype.val hxx'
  subst this
  exact Subtype.ext hx'.symm

