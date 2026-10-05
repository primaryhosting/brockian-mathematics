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

theorem models_foundAx : VClass P ⊨ foundAx.{u + 1} := by
  rw [realize_foundAx]
  rintro ⟨x, hx⟩ ⟨⟨y, hy⟩, hyx⟩
  have hne : x ≠ ∅ := by
    rintro rfl
    exact ZFSet.notMem_empty _ hyx
  obtain ⟨w, hw, hint⟩ := ZFSet.regularity x hne
  refine ⟨⟨w, h.mem_trans hx hw⟩, hw, ?_⟩
  rintro ⟨⟨z, hz⟩, h1, h2⟩
  have : z ∈ x ∩ w := ZFSet.mem_inter.2 ⟨h2, h1⟩
  rw [hint] at this
  exact ZFSet.notMem_empty _ this

