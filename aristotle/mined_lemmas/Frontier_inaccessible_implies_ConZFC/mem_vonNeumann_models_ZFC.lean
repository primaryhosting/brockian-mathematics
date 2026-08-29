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

theorem mem_vonNeumann_models_ZFC {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    VClass (fun x : ZFSet.{u} => x ∈ ZFSet.vonNeumann κ.ord) ⊨ ZFC.{u + 1} :=
  VClass.models_ZFC (isZFCClass_mem_vonNeumann hκ)

/-- **An inaccessible cardinal yields a model of ZFC**, hence `Con(ZFC)`.

Here consistency is the semantic notion: `ZFC.IsSatisfiable` says that the first-order theory
`Frontier.ZFC` has a model. The model produced is `V_κ`, the class of sets of rank below
`κ.ord`, with the real membership relation. -/
