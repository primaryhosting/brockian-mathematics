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

theorem models_unionAx : VClass P ⊨ unionAx.{u + 1} := by
  rw [realize_unionAx]
  rintro ⟨a, ha⟩
  refine ⟨⟨⋃₀ a, h.sUnion ha⟩, ?_⟩
  rintro ⟨z, hz⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hya, hzy⟩
    exact ⟨⟨y, h.mem_trans ha hya⟩, hzy, hya⟩
  · rintro ⟨⟨y, hy⟩, hzy, hya⟩
    exact ⟨y, hya, hzy⟩

