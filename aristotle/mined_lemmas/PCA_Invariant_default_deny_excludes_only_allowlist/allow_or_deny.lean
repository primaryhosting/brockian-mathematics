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
