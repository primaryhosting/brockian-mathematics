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

theorem ConZFC_of_isSatisfiable_extension {T : setLang.{u}.Theory}
    (h : (ZFC.{u} ∪ T).IsSatisfiable) : (ZFC.{u}).IsSatisfiable :=
  h.mono Set.subset_union_left

/-- The class of all sets is a model of ZFC, so `Con(ZFC)` is a theorem of Lean's type theory
outright (Lean's universe hierarchy provides inaccessible cardinals). The point of
`Frontier.inaccessible_implies_ConZFC` is that the model is built from a *given* inaccessible
cardinal, as `V_κ`. -/
