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

This file develops a small but complete model of the access-control ("isolation")
engine of a *policy-controlled agent* (`PCA`), together with the formal
soundness and completeness statement of its central security invariant:

> **Default deny.**  The engine denies every capability request, *except* exactly
> those that are explicitly matched by a rule of the policy's allowlist.

The model consists of

* `PCA.Capability`   — a concrete capability request (subject, action, resource);
* `PCA.Pattern`      — a matcher for one field, either a wildcard or an exact value;
* `PCA.Rule`         — an allowlist entry, i.e. a triple of patterns;
* `PCA.Policy`       — an allowlist of rules (and nothing else: there is no deny list,
                        denial is the default);
* `PCA.evaluate`     — the decision procedure of the engine.

The main theorem is `PCA.Invariant.default_deny_excludes_only_allowlist`.
-/

namespace PCA

/-- The decision returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A concrete capability request: a subject asking to perform an action on a resource. -/
structure Capability where
  subject : String
  action : String
  resource : String
  deriving DecidableEq, Repr

/-- A matcher for a single field of a capability: either a wildcard, or an exact value. -/
inductive Pattern
  | any
  | exact (value : String)
  deriving DecidableEq, Repr

/-- When does a pattern match a concrete field value? -/
def Pattern.Matches : Pattern → String → Prop
  | Pattern.any, _ => True
  | Pattern.exact v, s => v = s

instance (pt : Pattern) (s : String) : Decidable (pt.Matches s) := by
  cases pt <;> simp [Pattern.Matches] <;> infer_instance

/-- An allowlist entry: a rule matching a set of capabilities. -/
structure Rule where
  subject : Pattern
  action : Pattern
  resource : Pattern
  deriving DecidableEq, Repr

/-- A rule matches a capability when each of its three patterns matches
the corresponding field. -/
def Rule.Matches (rl : Rule) (c : Capability) : Prop :=
  rl.subject.Matches c.subject ∧ rl.action.Matches c.action ∧ rl.resource.Matches c.resource

instance (rl : Rule) (c : Capability) : Decidable (rl.Matches c) := by
  unfold Rule.Matches; infer_instance

/-- A policy is *only* an allowlist: there is no deny list, since denial is the default. -/
structure Policy where
  allowlist : List Rule
  deriving Repr

/-- The set of capabilities explicitly permitted by the policy's allowlist. -/
def Policy.Allows (p : Policy) (c : Capability) : Prop :=
  ∃ rl ∈ p.allowlist, rl.Matches c

instance (p : Policy) (c : Capability) : Decidable (p.Allows c) := by
  unfold Policy.Allows; infer_instance

/-- The set of capabilities that the allowlist of `p` grants. -/
def Policy.allowedSet (p : Policy) : Set Capability := {c | p.Allows c}

/-- The engine's decision procedure: allow when some allowlist rule matches,
otherwise fall through to the default, which is denial. -/
def evaluate (p : Policy) (c : Capability) : Decision :=
  if p.allowlist.any (fun rl => decide (rl.Matches c)) then Decision.allow else Decision.deny

/-- `List.any` over the allowlist is exactly the `Policy.Allows` predicate. -/
theorem any_allowlist_iff_allows (p : Policy) (c : Capability) :
    (p.allowlist.any fun rl => decide (rl.Matches c)) = true ↔ p.Allows c := by
  simp [Policy.Allows, List.any_eq_true]

/-- **Completeness.**  Every capability matched by the allowlist is allowed. -/
theorem Invariant.evaluate_allow_of_allows {p : Policy} {c : Capability}
    (h : p.Allows c) : evaluate p c = Decision.allow := by
  simp [evaluate, (any_allowlist_iff_allows p c).mpr h]

/-- **Soundness.**  Anything the engine allows is matched by the allowlist. -/
theorem Invariant.allows_of_evaluate_allow {p : Policy} {c : Capability}
    (h : evaluate p c = Decision.allow) : p.Allows c := by
  by_cases hb : (p.allowlist.any fun rl => decide (rl.Matches c)) = true
  · exact (any_allowlist_iff_allows p c).mp hb
  · simp [evaluate, hb] at h

/-- The engine allows exactly the capabilities in the allowlist. -/
theorem Invariant.evaluate_allow_iff (p : Policy) (c : Capability) :
    evaluate p c = Decision.allow ↔ p.Allows c :=
  ⟨Invariant.allows_of_evaluate_allow, Invariant.evaluate_allow_of_allows⟩

/-- The engine's decisions are exhaustive: allow or deny, never both. -/
theorem evaluate_deny_iff_not_allow (p : Policy) (c : Capability) :
    evaluate p c = Decision.deny ↔ evaluate p c ≠ Decision.allow := by
  unfold evaluate
  split <;> simp

/-!
## The main invariant
-/

/--
**Default deny excludes only the allowlist.**

The isolation engine's model is sound and complete with respect to the policy:

1. a capability is allowed iff it is matched by some rule of the allowlist
   (soundness: nothing else is ever allowed; completeness: everything listed is allowed);
2. consequently the set of *denied* capabilities is exactly the complement of the
   allowed set — denial is the default, and the allowlist is the only exception to it.
-/
theorem Invariant.default_deny_excludes_only_allowlist (p : Policy) :
    (∀ c : Capability, evaluate p c = Decision.allow ↔ p.Allows c) ∧
      {c : Capability | evaluate p c = Decision.deny} = (p.allowedSet)ᶜ := by
  refine ⟨Invariant.evaluate_allow_iff p, ?_⟩
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Policy.allowedSet]
  rw [evaluate_deny_iff_not_allow]
  simp only [ne_eq, Invariant.evaluate_allow_iff]

/-!
## Corollaries: the model really is "default deny"
-/

/-- With an empty allowlist the engine denies everything. -/
theorem Invariant.empty_policy_denies_all (c : Capability) :
    evaluate ⟨[]⟩ c = Decision.deny := by
  simp [evaluate]

/-- Nothing outside the allowlist is ever allowed. -/
theorem Invariant.denied_of_not_allows {p : Policy} {c : Capability}
    (h : ¬ p.Allows c) : evaluate p c = Decision.deny := by
  rw [evaluate_deny_iff_not_allow]
  simp only [ne_eq, Invariant.evaluate_allow_iff]
  exact h

/-- Extending the allowlist can only add permissions; it never revokes any
(monotonicity of the engine in the policy). -/
theorem Invariant.evaluate_mono {p q : Policy} (hsub : p.allowlist ⊆ q.allowlist)
    {c : Capability} (h : evaluate p c = Decision.allow) : evaluate q c = Decision.allow := by
  rw [Invariant.evaluate_allow_iff] at h ⊢
  obtain ⟨rl, hmem, hm⟩ := h
  exact ⟨rl, hsub hmem, hm⟩

/-- The allowed set is exactly the union of the sets matched by the individual rules:
no rule interaction can produce a permission that no single rule grants. -/
theorem Invariant.allowedSet_eq_iUnion (p : Policy) :
    p.allowedSet = ⋃ rl ∈ p.allowlist, {c : Capability | rl.Matches c} := by
  ext c
  simp [Policy.allowedSet, Policy.Allows]

/-!
## Sanity checks: the model is non-vacuous
-/

/-- A wildcard rule on the action field: `alice` may do anything to `file.txt`. -/
example :
    evaluate ⟨[⟨Pattern.exact "alice", Pattern.any, Pattern.exact "file.txt"⟩]⟩
      ⟨"alice", "read", "file.txt"⟩ = Decision.allow := by
  decide

/-- The very same policy denies a different subject: isolation is enforced. -/
example :
    evaluate ⟨[⟨Pattern.exact "alice", Pattern.any, Pattern.exact "file.txt"⟩]⟩
      ⟨"mallory", "read", "file.txt"⟩ = Decision.deny := by
  decide

/-- And it denies `alice` on a resource that is not listed. -/
example :
    evaluate ⟨[⟨Pattern.exact "alice", Pattern.any, Pattern.exact "file.txt"⟩]⟩
      ⟨"alice", "read", "secrets.txt"⟩ = Decision.deny := by
  decide

end PCA

