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

theorem models_infAx : VClass P ⊨ infAx.{u + 1} := by
  rw [realize_infAx]
  refine ⟨⟨ZFSet.omega, h.omega⟩, ⟨⟨∅, h.empty⟩, ZFSet.omega_zero, ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    exact ZFSet.notMem_empty z
  · rintro ⟨y, hy⟩ hyw
    refine ⟨⟨insert y y, h.mem_trans h.omega (ZFSet.omega_succ hyw)⟩, ZFSet.omega_succ hyw, ?_⟩
    rintro ⟨z, hz⟩
    show z ∈ insert y y ↔ _
    rw [ZFSet.mem_insert_iff]
    constructor
    · rintro (rfl | hh)
      · exact Or.inr rfl
      · exact Or.inl hh
    · rintro (hh | hh)
      · exact Or.inr hh
      · exact Or.inl (congrArg Subtype.val hh)

