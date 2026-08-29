import PCA.Isolation

/-
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

/-! ## The abstract isolation model

A *privilege policy* on a type of privileges `P` is a relation `grants`, where
`grants a b` means "a principal holding privilege `a` may directly acquire
privilege `b`".  Privilege *escalation* is the reflexive–transitive closure of
this relation, and the *escape set* of a set `S` of initially held privileges is
the set of privileges reachable by escalation from `S`. -/

/-- A privilege policy: `grants a b` means privilege `a` directly confers `b`. -/
structure Policy (P : Type*) where
  /-- The direct-grant relation of the policy. -/
  grants : P → P → Prop

variable {P : Type*}

/-- `Escalates pol a b` : privilege `b` is reachable from privilege `a` by a
finite chain of direct grants of the policy `pol`. -/

theorem subset_stepClosure (pol : FinPolicy P) (S : Finset P) :
    S ⊆ stepClosure pol S := Finset.subset_union_left

