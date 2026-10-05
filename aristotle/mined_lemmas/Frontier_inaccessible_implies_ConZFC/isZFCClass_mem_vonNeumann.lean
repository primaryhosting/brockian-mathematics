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

theorem isZFCClass_mem_vonNeumann {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsZFCClass (fun x : ZFSet.{u} => x ∈ ZFSet.vonNeumann κ.ord) := by
  have hfun : (fun x : ZFSet.{u} => x ∈ ZFSet.vonNeumann κ.ord)
      = fun x : ZFSet.{u} => x.rank < κ.ord :=
    funext fun x => propext ZFSet.mem_vonNeumann
  rw [hfun]
  exact isZFCClass_rank_lt hκ

end Frontier

/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.SetLanguage
import RequestProject.ZFCModel
import RequestProject.Inaccessible

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Summary

`Frontier.ZFC` is the theory of Zermelo–Fraenkel set theory with choice, written out in the
first-order language `Frontier.setLang` with a single binary relation symbol `∈`
(extensionality, foundation, pairing, union, power set, infinity, choice, and the separation
and replacement schemes, with one axiom for each first-order formula and each finite list of
parameters).

Consistency is taken in its semantic form: a theory is consistent when it has a model, i.e.
`FirstOrder.Language.Theory.IsSatisfiable`. (Mathlib has no deduction calculus for first-order
logic, so the completeness theorem is not available to relate this to the syntactic notion.)

The main theorem `Frontier.inaccessible_implies_ConZFC` says that from a strongly inaccessible
cardinal `κ` one obtains a model of ZFC, namely `V_κ`, the class of sets of rank `< κ.ord`;
hence `Con(ZFC)` holds. Combined with the trivial monotonicity of satisfiability
(`Frontier.ConZFC_of_isSatisfiable_extension`) this gives the reduction
`Con(ZFC + "there is an inaccessible") → Con(ZFC)`.
-/

open FirstOrder Language ZFSet

universe u v

namespace Frontier

/-- For `κ` inaccessible, the sets of rank `< κ.ord` (i.e. `V_κ`) form a model of ZFC. -/
