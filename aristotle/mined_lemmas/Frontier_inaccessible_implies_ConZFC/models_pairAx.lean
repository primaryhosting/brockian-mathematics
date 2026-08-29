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

theorem models_pairAx : VClass P ⊨ pairAx.{u + 1} := by
  rw [realize_pairAx]
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨⟨{x, y}, h.pair hx hy⟩, ?_⟩
  rintro ⟨w, hw⟩
  show w ∈ ({x, y} : ZFSet.{u}) ↔ _
  rw [ZFSet.mem_pair]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (hh | hh) <;> [left; right] <;> exact congrArg Subtype.val hh

