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

theorem models_powerAx : VClass P ⊨ powerAx.{u + 1} := by
  rw [realize_powerAx]
  rintro ⟨a, ha⟩
  refine ⟨⟨a.powerset, h.powerset ha⟩, ?_⟩
  rintro ⟨z, hz⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_powerset]
  constructor
  · rintro hsub ⟨t, ht⟩ htz
    exact hsub htz
  · intro hall t htz
    exact hall ⟨t, h.mem_trans hz htz⟩ htz

