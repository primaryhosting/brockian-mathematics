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

theorem engineEscape_mono [Fintype P] {pol₁ pol₂ : FinPolicy P} {S₁ S₂ : Finset P}
    (hpol : ∀ a, pol₁.grants a ⊆ pol₂.grants a) (hS : S₁ ⊆ S₂) :
    (engineEscape pol₁ S₁ : Set P) ⊆ (engineEscape pol₂ S₂ : Set P) := by
  rw [engineEscape_eq, engineEscape_eq]
  exact priv_escape_monotone (fun a b hab => hpol a hab) (by exact_mod_cast hS)

end Engine

/-! ## A worked example

A three-privilege policy in which `0` grants `1` and `1` grants `2`.  The engine
computes the full escape set of `{0}` and certifies that `{2}` is isolated from
`{0, 1}`. -/

namespace Example

/-- `0 ⟶ 1 ⟶ 2`, and `2` grants nothing. -/
