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

theorem models_ZFC : VClass P ⊨ ZFC.{u + 1} := by
  refine ⟨?_⟩
  rintro σ hσ
  rcases hσ with ((hσ | ⟨k, φ, rfl⟩) | ⟨k, φ, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extAx h
    · exact models_foundAx h
    · exact models_pairAx h
    · exact models_unionAx h
    · exact models_powerAx h
    · exact models_infAx h
    · exact models_choiceAx h
  · exact models_sepAx h k φ
  · exact models_replAx h k φ

end VClass

/-! ### The class of all sets -/

/-- The class of all sets satisfies the closure conditions. -/
