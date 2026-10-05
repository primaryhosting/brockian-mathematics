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

theorem isolated_mono {pol₁ pol₂ : Policy P} {S₁ S₂ T₁ T₂ : Set P}
    (hpol : Permits pol₁ pol₂) (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂)
    (h : Isolated pol₂ S₂ T₂) : Isolated pol₁ S₁ T₁ := by
  rw [isolated_iff] at h ⊢
  exact fun p hp q hq hpq => h p (hS hp) q (hT hq) (escalates_mono hpol hpq)

/-! ## The isolation engine

For a finite privilege type the escape set is computed by saturating the initial
set under the direct grants.  We show the engine is *sound* (it only reports
genuinely reachable privileges) and *complete* (it reports all of them). -/

section Engine

variable [DecidableEq P]

/-- A finitely presented policy: `grants p` lists the privileges directly
conferred by `p`. -/
structure FinPolicy (P : Type*) where
  /-- Direct grants of a privilege, as a finite set. -/
  grants : P → Finset P

/-- The abstract policy underlying a finitely presented one. -/
