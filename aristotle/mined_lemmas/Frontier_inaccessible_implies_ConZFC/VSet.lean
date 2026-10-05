import Mathlib

/-!
# The cumulative hierarchy and inaccessible cardinals

This file defines the von Neumann cumulative hierarchy `Frontier.cumul o` inside `ZFSet`,
characterizes its members by rank, and proves the two facts about an inaccessible cardinal `κ`
that are needed to see that `V_κ` is a model of ZFC:

* `Frontier.card_lt_of_rank_lt`: a set of rank `< κ.ord` has cardinality `< κ`;
* `Frontier.rank_range_lt`: `V_κ` is closed under images of small families (replacement).
-/

open Ordinal Cardinal

namespace Frontier

/-- The von Neumann cumulative hierarchy `V_o`, as a `ZFSet`. -/

theorem VSet.models_ZFC (hκ : κ.IsInaccessible) : (VSet κ) ⊨ ZFC := by
  haveI := nonempty_VSet hκ
  rw [models_ZFC_iff]
  exact ⟨⟨VSet.models_axExt, VSet.models_axPair hκ, VSet.models_axUnion,
    VSet.models_axPow hκ, VSet.models_axInf hκ, VSet.models_axFound, VSet.models_axChoice⟩,
    fun n φ => VSet.models_axSep n φ, fun n φ => VSet.models_axRep hκ n φ⟩

end Frontier

import Mathlib
import RequestProject.SetLanguage
import RequestProject.Cumulative
import RequestProject.Model

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized

`Frontier.ZFC` is the theory of ZFC, written in the first-order language
`Frontier.setLang` with a single binary relation symbol (see `RequestProject/SetLanguage.lean`):
extensionality, pairing, union, power set, infinity, foundation and choice, together with the
full separation and replacement schemes (one axiom for every formula with parameters).
Each axiom comes with a lemma computing its meaning in an arbitrary structure, so the
formalization can be checked against the usual informal statements.

For a cardinal `κ`, `Frontier.VSet κ` is the collection of all sets (`ZFSet`) of rank `< κ.ord`,
i.e. the level `V_κ` of the cumulative hierarchy, viewed as a structure for `setLang`.
The main result is that `V_κ` is a model of ZFC whenever `κ` is inaccessible, so that the
existence of an inaccessible cardinal implies the consistency of ZFC.

Since Mathlib's model theory provides semantics but no deductive calculus, consistency is
expressed as satisfiability, `FirstOrder.Language.Theory.IsSatisfiable` (the two are equivalent
by Gödel's completeness theorem). The reduction `Con(ZFC + inaccessible) → Con(ZFC)` in this
setting is the monotonicity statement `Frontier.ConZFC_of_extension`.

A remark on strength: the mathematical content of the development is the construction of the
model, `Frontier.VSet.models_ZFC`, which says that `V_κ ⊨ ZFC` for `κ` inaccessible. The
consequence `Frontier.ZFC.IsSatisfiable` is stated under the hypothesis that an inaccessible
cardinal exists, as in the informal statement; note that Lean's own type-theoretic foundation is
itself strong enough to prove Con(ZFC), so no formalization of Con(ZFC) inside Lean can be
independent of that ambient strength.

As a check that the axiomatization is not degenerate,
`Frontier.no_universal_set_of_models_ZFC` derives Russell's paradox from an instance of the
separation scheme in an arbitrary model.
-/

open FirstOrder Language Cardinal

namespace Frontier

/-- **An inaccessible cardinal yields a model of ZFC.**

If `κ` is an inaccessible cardinal, then the level `V_κ` of the cumulative hierarchy is a model
of ZFC; consequently ZFC is satisfiable (consistent). -/
