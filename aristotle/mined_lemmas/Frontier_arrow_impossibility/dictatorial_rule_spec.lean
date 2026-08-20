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

import Mathlib

/-!
# Arrow's impossibility theorem

A *ranking* on a type of alternatives `A` is a total, transitive, antisymmetric relation
(a linear order presented as a relation).  A *profile* assigns a ranking to each voter, and a
*ranked voting rule* (social welfare function) aggregates profiles into a single relation.

The main result, `Frontier.arrow_impossibility`, states that whenever there are at least three
alternatives and finitely many voters, no ranked voting rule producing a ranking can
simultaneously satisfy unanimity (Pareto), independence of irrelevant alternatives, and
non-dictatorship.
-/

namespace Frontier

section Defs

variable {A : Type*}

/-- A *ranking* of the alternatives: a total, transitive, antisymmetric relation. -/

theorem dictatorial_rule_spec {V A : Type*} (d : V) :
    IsRankingRule (fun p : Profile V A => p d) ∧ Unanimity (fun p : Profile V A => p d) ∧
      IIA (fun p : Profile V A => p d) ∧ IsDictator (fun p : Profile V A => p d) d :=
  ⟨fun _ hp => hp d, fun _ _ _ _ h => h d, fun _ _ _ _ _ _ h1 _ => h1 d, fun _ _ _ _ h => h⟩

/-- **Arrow's impossibility theorem**: with at least three alternatives and finitely many
voters, no ranked voting rule satisfies unanimity, independence of irrelevant alternatives,
and non-dictatorship. -/
