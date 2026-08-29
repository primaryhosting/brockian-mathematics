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

theorem models_sepAx (k : ℕ) (φ : setLang.{u + 1}.Formula (Fin k ⊕ Fin 1)) :
    VClass P ⊨ sepAx k φ := by
  classical
  rw [realize_sepAx]
  rintro p ⟨a, ha⟩
  refine ⟨⟨ZFSet.sep (fun w => ∃ hw : P w, φ.Realize (Sum.elim p (fun _ => ⟨w, hw⟩))) a,
    h.sep _ ha⟩, ?_⟩
  rintro ⟨z, hz⟩
  simp only [mem'_VClass]
  rw [ZFSet.mem_sep]
  refine and_congr_right fun hza => ⟨?_, ?_⟩
  · rintro ⟨hw, hφ⟩
    exact hφ
  · intro hφ
    exact ⟨hz, hφ⟩

