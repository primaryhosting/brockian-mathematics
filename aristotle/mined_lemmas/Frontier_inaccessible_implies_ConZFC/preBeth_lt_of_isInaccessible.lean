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

theorem preBeth_lt_of_isInaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → Cardinal.preBeth o < κ := by
  intro o
  induction o using Ordinal.induction with
  | _ o IH =>
    intro ho
    rw [Cardinal.preBeth, iSup_reindex (Ordinal.ToType.mk (o := o)).symm.toEquiv]
    refine Cardinal.iSup_lt_of_isRegular hκ.isRegular ?_ ?_
    · rw [mk_toType]
      exact Cardinal.lt_ord.1 ho
    · intro i
      exact hκ.isStrongLimit.two_power_lt
        (IH _ ((Ordinal.ToType.mk (o := o)).symm i).2
          (((Ordinal.ToType.mk (o := o)).symm i).2.trans ho))

/-- Every set of rank below an inaccessible `κ` has cardinality below `κ`. -/
