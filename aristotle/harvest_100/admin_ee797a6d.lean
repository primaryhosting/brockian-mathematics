/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Model of the isolation engine of a proof-carrying app.

A *request* is an attempt by a principal to perform an action on a resource.
An isolation engine is configured with a finite list of *grant rules*; each rule
recognises the set of requests that it authorises.  The engine is *default
deny*: it returns `allow` exactly when some configured rule authorises the
request, and returns `deny` in every other case.  The *allowlist* of an engine
is the collection of requests authorised by at least one of its rules.

The main invariant, `PCA.Invariant.default_deny_excludes_only_allowlist`, states
that the collection of requests excluded (denied) by the engine is *exactly* the
complement of the allowlist:

* soundness of isolation — every request outside the allowlist is denied; and
* completeness / no over-blocking — no request on the allowlist is denied.

This file is deliberately self-contained (it needs nothing beyond Lean's core
prelude); `RequestProject/Main.lean` re-packages the same statement using
Mathlib's `Set` API.
-/

namespace PCA

/-- A request: a principal attempting an action on a resource. -/
structure Request (P R A : Type _) where
  /-- The principal issuing the request. -/
  principal : P
  /-- The resource being accessed. -/
  resource : R
  /-- The action attempted on the resource. -/
  action : A

/-- The verdict returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A grant rule, given by the predicate describing the requests it authorises. -/
structure Rule (P R A : Type _) where
  /-- The requests authorised by this rule. -/
  admits : Request P R A → Prop

/-- An isolation engine is a finite configuration of grant rules. -/
structure Engine (P R A : Type _) where
  /-- The configured grant rules, in order. -/
  rules : List (Rule P R A)

variable {P R A : Type _}

/-- Collections of requests are modelled as predicates on requests. -/
abbrev ReqSet (P R A : Type _) := Request P R A → Prop

/-- The complement of a collection of requests. -/
def Excluded (S : ReqSet P R A) : ReqSet P R A := fun req => ¬ S req

/-- The allowlist induced by an engine: the requests authorised by some
configured rule. -/
def Engine.Allowlist (eng : Engine P R A) : ReqSet P R A :=
  fun req => ∃ r ∈ eng.rules, r.admits req

/-- The default-deny evaluation function of the engine: `allow` when the request
is on the allowlist, `deny` in every other case. -/
noncomputable def Engine.evaluate (eng : Engine P R A) (req : Request P R A) : Decision :=
  haveI := Classical.propDecidable (eng.Allowlist req)
  if eng.Allowlist req then Decision.allow else Decision.deny

/-- The collection of requests excluded (denied) by the engine. -/
def Engine.Denied (eng : Engine P R A) : ReqSet P R A :=
  fun req => eng.evaluate req = Decision.deny

namespace Invariant

/-! ## Key intermediate lemmas -/

/-- **Key intermediate lemma.**  The engine returns `allow` for a request
precisely when some configured rule authorises it, i.e. precisely on the
allowlist. -/
theorem evaluate_eq_allow_iff_allowlist (eng : Engine P R A) (req : Request P R A) :
    eng.evaluate req = Decision.allow ↔ ∃ r ∈ eng.rules, r.admits req := by
  unfold Engine.evaluate Engine.Allowlist
  by_cases h : ∃ r ∈ eng.rules, r.admits req
  · simp [h]
  · simp [h]

/-- Complementary form of the key lemma: the engine returns `deny` for a request
precisely when no configured rule authorises it. -/
theorem evaluate_eq_deny_iff_not_allowlist (eng : Engine P R A) (req : Request P R A) :
    eng.evaluate req = Decision.deny ↔ ¬ eng.Allowlist req := by
  constructor
  · intro hdeny hmem
    have hallow : eng.evaluate req = Decision.allow :=
      (evaluate_eq_allow_iff_allowlist eng req).2 hmem
    rw [hdeny] at hallow
    exact Decision.noConfusion hallow
  · intro h
    unfold Engine.evaluate
    simp [h]

/-! ## Main invariant -/

/-- **Default deny excludes only the allowlist.**

The collection of requests denied by the default-deny isolation engine is
exactly the complement of its allowlist: every request off the allowlist is
denied (soundness of isolation), and no request on the allowlist is denied
(completeness, i.e. no over-blocking). -/
theorem default_deny_excludes_only_allowlist (eng : Engine P R A) :
    eng.Denied = Excluded eng.Allowlist := by
  funext req
  exact propext (evaluate_eq_deny_iff_not_allowlist eng req)

/-! ## Consequences -/

/-- Soundness of isolation: a request that no rule authorises is denied. -/
theorem denied_of_not_allowlist (eng : Engine P R A) {req : Request P R A}
    (h : ¬ eng.Allowlist req) : eng.evaluate req = Decision.deny :=
  (evaluate_eq_deny_iff_not_allowlist eng req).2 h

/-- No over-blocking: a request authorised by some rule is allowed. -/
theorem allow_of_allowlist (eng : Engine P R A) {req : Request P R A}
    (h : eng.Allowlist req) : eng.evaluate req = Decision.allow :=
  (evaluate_eq_allow_iff_allowlist eng req).2 h

/-- The engine is total: every request receives exactly one of the two
verdicts. -/
theorem allow_or_deny (eng : Engine P R A) (req : Request P R A) :
    (eng.evaluate req = Decision.allow ∧ ¬ eng.Denied req) ∨
      (eng.evaluate req = Decision.deny ∧ ¬ eng.Allowlist req) := by
  by_cases h : eng.Allowlist req
  · exact Or.inl ⟨allow_of_allowlist eng h, by
      unfold Engine.Denied
      rw [allow_of_allowlist eng h]
      exact fun hc => Decision.noConfusion hc⟩
  · exact Or.inr ⟨denied_of_not_allowlist eng h, h⟩

/-- An engine with no configured rules denies every request. -/
theorem denied_all_of_no_rules (eng : Engine P R A) (h : eng.rules = [])
    (req : Request P R A) : eng.Denied req := by
  refine denied_of_not_allowlist eng ?_
  unfold Engine.Allowlist
  rw [h]
  rintro ⟨r, hr, -⟩
  exact List.not_mem_nil hr

/-- Adding rules can only enlarge the allowlist, hence only shrink the denied
set: default deny never becomes more permissive than its rules allow. -/
theorem denied_antitone (eng eng' : Engine P R A)
    (hsub : ∀ r ∈ eng.rules, r ∈ eng'.rules) {req : Request P R A}
    (h : eng'.Denied req) : eng.Denied req := by
  refine denied_of_not_allowlist eng ?_
  rintro ⟨r, hr, hadm⟩
  have h' : ¬ eng'.Allowlist req :=
    (evaluate_eq_deny_iff_not_allowlist eng' req).1 h
  exact h' ⟨r, hsub r hr, hadm⟩

end Invariant

end PCA

import Mathlib
import RequestProject.DefaultDeny

/-!
# Default Deny Excludes Only Allowlist — Mathlib `Set` packaging

The target theorem `PCA.Invariant.default_deny_excludes_only_allowlist` lives in
`RequestProject/DefaultDeny.lean`, which is self-contained.  Here we restate it
using Mathlib's `Set` API: the set of requests denied by the default-deny
isolation engine is the set-theoretic complement of its allowlist.
-/

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

set_option grind.warning false

namespace PCA

variable {P R A : Type*}

/-- The allowlist of an engine, as a Mathlib `Set`. -/
def Engine.allowlistSet (eng : Engine P R A) : Set (Request P R A) :=
  {req | eng.Allowlist req}

/-- The set of requests denied by an engine, as a Mathlib `Set`. -/
def Engine.deniedSet (eng : Engine P R A) : Set (Request P R A) :=
  {req | eng.evaluate req = Decision.deny}

namespace Invariant

/-- `Set`-valued form of the main invariant: the denied set is exactly the
complement of the allowlist. -/
theorem deniedSet_eq_compl_allowlistSet (eng : Engine P R A) :
    eng.deniedSet = (eng.allowlistSet)ᶜ := by
  ext req
  simpa [Engine.deniedSet, Engine.allowlistSet, Set.mem_setOf_eq] using
    evaluate_eq_deny_iff_not_allowlist eng req

end Invariant

end PCA

