/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Arrow's impossibility theorem

A *ranking* of a type `A` of alternatives is a strict total order (transitive, total on
distinct elements, asymmetric).  A *social welfare function* is a map
`F : (V → Ranking A) → Ranking A` sending each profile of individual rankings (one for each
voter `i : V`) to a social ranking.

We prove: if `V` is a finite nonempty set of voters, `A` has at least three elements, and `F`
satisfies unanimity (Pareto) and independence of irrelevant alternatives (IIA), then `F` has a
dictator.  Equivalently, no `F` satisfies unanimity, IIA and non-dictatorship
(`Frontier.arrow_impossibility`).

Mathlib does not contain Arrow's theorem, so the development is from scratch.  The proof is the
classical one: a *field expansion* lemma (semi-decisiveness over one pair implies decisiveness
over all pairs) followed by a *group contraction* lemma (a decisive coalition splits into two
parts, one of which is decisive), and then induction on the size of the coalition starting from
the grand coalition, which is decisive by unanimity.
-/

namespace Frontier

/-- A strict total order ("ranking") on the type of alternatives `A`. -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_total : ∀ {x y}, x ≠ y → rel x y ∨ rel y x
  rel_asymm : ∀ {x y}, rel x y → ¬ rel y x

namespace Ranking

variable {A : Type*}


theorem arrow_impossibility [Fintype V] [Nonempty V]
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (F : (V → Ranking A) → Ranking A) :
    ¬ (Pareto F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hPar, hIIA, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator h3 F hPar hIIA
  exact hnd i hi

/-- Sanity check (non-vacuity): the projection onto a single voter is a social welfare
function satisfying unanimity and IIA; by Arrow's theorem it must be — and indeed is —
dictatorial. -/
example (i₀ : V) : Pareto (fun P : V → Ranking A => P i₀) ∧ IIA (fun P : V → Ranking A => P i₀) ∧
    IsDictator (fun P : V → Ranking A => P i₀) i₀ :=
  ⟨fun _ _ _ h => h i₀, fun _ _ _ _ h => h i₀, fun _ _ _ h => h⟩

end Proof

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

