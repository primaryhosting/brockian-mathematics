/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# A formal model of a default-deny isolation engine

This file develops a small, self-contained model of a *policy controlled access* (PCA)
isolation engine and proves its central security invariant: the engine is **default deny**,
so the set of requests it admits is *exactly* the set of requests captured by the
allowlist (minus anything the denylist covers).  Nothing else can slip through.

The two halves of the statement are:

* **soundness**  – every admitted request is matched by some allowlist rule
  (and by no denylist rule);
* **completeness** – every request matched by an allowlist rule and by no denylist rule
  is admitted.

Together these say the engine's behaviour is characterised by its policy, which is
`PCA.Invariant.default_deny_excludes_only_allowlist`.
-/

namespace PCA

/-- A *pattern* for one field of a request: `Pattern.any` is a wildcard, while
`Pattern.exact s` matches the single label `s`. -/
inductive Pattern (α : Type) where
  | any : Pattern α
  | exact : α → Pattern α
  deriving DecidableEq, Repr

/-- Does a field pattern match a concrete label? -/
def Pattern.Matches {α : Type} (p : Pattern α) (a : α) : Prop :=
  match p with
  | .any => True
  | .exact b => b = a

instance {α : Type} [DecidableEq α] (p : Pattern α) (a : α) : Decidable (p.Matches a) := by
  cases p <;> simp [Pattern.Matches] <;> infer_instance

/-- A request presented to the isolation engine: a principal in some domain asks to
perform an action on a resource. -/
structure Request (Principal Resource Action : Type) where
  principal : Principal
  resource : Resource
  action : Action
  deriving DecidableEq, Repr

/-- A policy rule: a triple of patterns, one for each field of a request. -/
structure Rule (Principal Resource Action : Type) where
  principal : Pattern Principal
  resource : Pattern Resource
  action : Pattern Action
  deriving DecidableEq, Repr

variable {Principal Resource Action : Type}

/-- A rule matches a request when all three of its field patterns match. -/
def Rule.Matches (r : Rule Principal Resource Action)
    (q : Request Principal Resource Action) : Prop :=
  r.principal.Matches q.principal ∧ r.resource.Matches q.resource ∧ r.action.Matches q.action

instance [DecidableEq Principal] [DecidableEq Resource] [DecidableEq Action]
    (r : Rule Principal Resource Action) (q : Request Principal Resource Action) :
    Decidable (r.Matches q) := by
  unfold Rule.Matches; infer_instance

/-- The verdict returned by the engine. -/
inductive Decision where
  | allow : Decision
  | deny : Decision
  deriving DecidableEq, Repr

/-- A policy consists of an allowlist and a denylist of rules.  Everything not on the
allowlist is denied by default, and the denylist overrides the allowlist. -/
structure Policy (Principal Resource Action : Type) where
  allowlist : List (Rule Principal Resource Action)
  denylist : List (Rule Principal Resource Action)

/-- The request is covered by some allowlist rule. -/
def Policy.Allowlisted (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) : Prop :=
  ∃ r ∈ p.allowlist, r.Matches q

/-- The request is covered by some denylist rule. -/
def Policy.Denylisted (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) : Prop :=
  ∃ r ∈ p.denylist, r.Matches q

section Engine

variable [DecidableEq Principal] [DecidableEq Resource] [DecidableEq Action]

/-- The isolation engine: deny if the denylist fires, otherwise allow only if the
allowlist fires, otherwise **deny by default**. -/
def Policy.eval (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) : Decision :=
  if p.denylist.any (fun r => decide (r.Matches q)) then Decision.deny
  else if p.allowlist.any (fun r => decide (r.Matches q)) then Decision.allow
  else Decision.deny

theorem Policy.any_denylist_iff (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) :
    (p.denylist.any (fun r => decide (r.Matches q)) = true) ↔ p.Denylisted q := by
  simp [Policy.Denylisted, List.any_eq_true]

theorem Policy.any_allowlist_iff (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) :
    (p.allowlist.any (fun r => decide (r.Matches q)) = true) ↔ p.Allowlisted q := by
  simp [Policy.Allowlisted, List.any_eq_true]

/-- **Soundness.** Anything the engine admits is on the allowlist and off the denylist. -/
theorem Invariant.eval_allow_sound (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) (h : p.eval q = Decision.allow) :
    p.Allowlisted q ∧ ¬ p.Denylisted q := by
  unfold Policy.eval at h
  by_cases hd : p.denylist.any (fun r => decide (r.Matches q)) = true
  · rw [if_pos hd] at h; exact absurd h (by simp)
  · rw [if_neg hd] at h
    by_cases ha : p.allowlist.any (fun r => decide (r.Matches q)) = true
    · exact ⟨(p.any_allowlist_iff q).mp ha, fun hcon =>
        hd ((p.any_denylist_iff q).mpr hcon)⟩
    · rw [if_neg ha] at h; exact absurd h (by simp)

/-- **Completeness.** Anything on the allowlist and off the denylist is admitted. -/
theorem Invariant.eval_allow_complete (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action)
    (ha : p.Allowlisted q) (hd : ¬ p.Denylisted q) :
    p.eval q = Decision.allow := by
  unfold Policy.eval
  rw [if_neg (fun h => hd ((p.any_denylist_iff q).mp h)),
    if_pos ((p.any_allowlist_iff q).mpr ha)]

/-- **The default-deny invariant (soundness + completeness).**

The isolation engine admits a request **iff** the request is captured by the allowlist
and is not captured by the denylist.  In particular the engine grants no access that the
allowlist does not explicitly describe: everything outside the allowlist is denied. -/
theorem Invariant.default_deny_excludes_only_allowlist
    (p : Policy Principal Resource Action) (q : Request Principal Resource Action) :
    p.eval q = Decision.allow ↔ (p.Allowlisted q ∧ ¬ p.Denylisted q) :=
  ⟨Invariant.eval_allow_sound p q, fun h => Invariant.eval_allow_complete p q h.1 h.2⟩

/-- Contrapositive form: everything off the allowlist is denied. -/
theorem Invariant.deny_of_not_allowlisted (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) (h : ¬ p.Allowlisted q) :
    p.eval q = Decision.deny := by
  rcases hdec : p.eval q with _ | _
  · exact absurd ((Invariant.default_deny_excludes_only_allowlist p q).mp hdec).1 h
  · rfl

/-- The denylist always overrides the allowlist. -/
theorem Invariant.deny_of_denylisted (p : Policy Principal Resource Action)
    (q : Request Principal Resource Action) (h : p.Denylisted q) :
    p.eval q = Decision.deny := by
  rcases hdec : p.eval q with _ | _
  · exact absurd h ((Invariant.default_deny_excludes_only_allowlist p q).mp hdec).2
  · rfl

/-- With an empty allowlist the engine is totally isolating. -/
theorem Invariant.empty_allowlist_denies_all
    (p : Policy Principal Resource Action) (hp : p.allowlist = [])
    (q : Request Principal Resource Action) : p.eval q = Decision.deny :=
  Invariant.deny_of_not_allowlisted p q (by simp [Policy.Allowlisted, hp])

/-- Shrinking the allowlist can only shrink the set of admitted requests: the engine is
monotone in its allowlist. -/
theorem Invariant.mono_allowlist (p p' : Policy Principal Resource Action)
    (hsub : p.allowlist ⊆ p'.allowlist) (hden : p'.denylist ⊆ p.denylist)
    (q : Request Principal Resource Action) (h : p.eval q = Decision.allow) :
    p'.eval q = Decision.allow := by
  obtain ⟨⟨r, hr, hrm⟩, hd⟩ := (Invariant.default_deny_excludes_only_allowlist p q).mp h
  refine (Invariant.default_deny_excludes_only_allowlist p' q).mpr
    ⟨⟨r, hsub hr, hrm⟩, ?_⟩
  rintro ⟨s, hs, hsm⟩
  exact hd ⟨s, hden hs, hsm⟩

end Engine

end PCA

