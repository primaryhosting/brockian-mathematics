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

noncomputable def ZFC : setLang.{u}.Theory :=
  {extAx, foundAx, pairAx, unionAx, powerAx, infAx, choiceAx} ∪
  {σ | ∃ (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 1)), σ = sepAx k φ} ∪
  {σ | ∃ (k : ℕ) (φ : setLang.{u}.Formula (Fin k ⊕ Fin 2)), σ = replAx k φ}

/-! ### Unfolding satisfaction of the axioms -/

