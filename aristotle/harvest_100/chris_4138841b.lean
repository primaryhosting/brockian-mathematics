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
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-! ## The capability model of the isolation engine -/

/-- A *pattern* used inside an allowlist rule: either the wildcard `any`, which
matches every value, or `exact v`, which matches only `v`. -/
inductive Pattern (α : Type _) where
  | any : Pattern α
  | exact : α → Pattern α
  deriving DecidableEq, Repr

/-- Does a pattern match a concrete value? -/
def Pattern.Matches {α : Type _} : Pattern α → α → Prop
  | .any, _ => True
  | .exact v, w => v = w

instance {α : Type _} [DecidableEq α] (p : Pattern α) (v : α) :
    Decidable (Pattern.Matches p v) := by
  cases p with
  | any => exact isTrue trivial
  | exact w => exact (inferInstance : Decidable (w = v))

/-- A concrete capability request presented to the isolation engine: a subject
(the running app / principal), a resource, and an action. -/
structure Capability (S R A : Type _) where
  subject : S
  resource : R
  action : A
  deriving DecidableEq, Repr

/-- An allowlist rule: a pattern for each of the three components of a request. -/
structure Rule (S R A : Type _) where
  subject : Pattern S
  resource : Pattern R
  action : Pattern A
  deriving DecidableEq, Repr

/-- A rule *covers* a capability when all three of its patterns match. -/
def Rule.Covers {S R A : Type _} (r : Rule S R A) (c : Capability S R A) : Prop :=
  r.subject.Matches c.subject ∧ r.resource.Matches c.resource ∧ r.action.Matches c.action

instance {S R A : Type _} [DecidableEq S] [DecidableEq R] [DecidableEq A]
    (r : Rule S R A) (c : Capability S R A) : Decidable (r.Covers c) := by
  unfold Rule.Covers; infer_instance

/-- A policy for the isolation engine is a finite list of allowlist rules.
There is no deny-list: everything not explicitly allowed is denied. -/
structure Policy (S R A : Type _) where
  rules : List (Rule S R A)
  deriving Repr

/-- The decision returned by the engine. -/
inductive Decision where
  | allow : Decision
  | deny : Decision
  deriving DecidableEq, Repr

/-- Predicates on capability requests, i.e. sets of requests. -/
abbrev CapSet (S R A : Type _) := Capability S R A → Prop

/-- Complement of a set of requests. -/
def CapSet.compl {S R A : Type _} (X : CapSet S R A) : CapSet S R A := fun c => ¬ X c

@[inherit_doc] postfix:max "ᶜᶜ" => CapSet.compl

/-- The *allowlist* determined by a policy: the set of capability requests
covered by at least one rule. -/
def Policy.Allowlist {S R A : Type _} (p : Policy S R A) : CapSet S R A :=
  fun c => ∃ r ∈ p.rules, r.Covers c

/-- The engine's evaluation function, implementing **default deny**: a request
is allowed exactly when some allowlist rule covers it, and denied otherwise. -/
def Policy.evaluate {S R A : Type _} [DecidableEq S] [DecidableEq R] [DecidableEq A]
    (p : Policy S R A) (c : Capability S R A) : Decision :=
  if p.rules.any (fun r => decide (r.Covers c)) then Decision.allow else Decision.deny

/-- The set of requests the engine *excludes* (denies). -/
def Policy.Excluded {S R A : Type _} [DecidableEq S] [DecidableEq R] [DecidableEq A]
    (p : Policy S R A) : CapSet S R A :=
  fun c => p.evaluate c = Decision.deny

namespace Invariant

variable {S R A : Type _} [DecidableEq S] [DecidableEq R] [DecidableEq A]

/-- The boolean rule search agrees with propositional allowlist membership. -/
theorem any_covers_iff (p : Policy S R A) (c : Capability S R A) :
    (p.rules.any (fun r => decide (r.Covers c)) = true) ↔ p.Allowlist c := by
  constructor
  · intro h
    obtain ⟨r, hr, hcov⟩ := List.any_eq_true.mp h
    exact ⟨r, hr, of_decide_eq_true hcov⟩
  · intro h
    obtain ⟨r, hr, hcov⟩ := h
    exact List.any_eq_true.mpr ⟨r, hr, decide_eq_true hcov⟩

/-- **Soundness**: every allowed request lies in the allowlist. -/
theorem allow_sound (p : Policy S R A) (c : Capability S R A)
    (h : p.evaluate c = Decision.allow) : p.Allowlist c := by
  refine (any_covers_iff p c).mp ?_
  by_cases hb : p.rules.any (fun r => decide (r.Covers c)) = true
  · exact hb
  · rw [Policy.evaluate, if_neg hb] at h
    exact absurd h (by intro hh; exact Decision.noConfusion hh)

/-- **Completeness**: every request in the allowlist is allowed. -/
theorem allow_complete (p : Policy S R A) (c : Capability S R A)
    (h : p.Allowlist c) : p.evaluate c = Decision.allow := by
  rw [Policy.evaluate, if_pos ((any_covers_iff p c).mpr h)]

/-- A request is denied iff it is not in the allowlist. -/
theorem deny_iff_not_mem_allowlist (p : Policy S R A) (c : Capability S R A) :
    p.evaluate c = Decision.deny ↔ ¬ p.Allowlist c := by
  constructor
  · intro h hmem
    rw [allow_complete p c hmem] at h
    exact Decision.noConfusion h
  · intro h
    rw [Policy.evaluate, if_neg (fun hb => h ((any_covers_iff p c).mp hb))]

/-- **Default deny excludes only the allowlist.**

The set of capability requests excluded (denied) by the isolation engine under
its default-deny policy is *exactly* the complement of the policy's allowlist:
nothing outside the allowlist is ever admitted (soundness) and nothing inside
the allowlist is ever excluded (completeness). -/
theorem default_deny_excludes_only_allowlist (p : Policy S R A) :
    p.Excluded = (p.Allowlist)ᶜᶜ := by
  funext c
  exact propext (deny_iff_not_mem_allowlist p c)

/-- Corollary: every request is either allowed or excluded. -/
theorem allowlist_union_excluded (p : Policy S R A) (c : Capability S R A) :
    p.Allowlist c ∨ p.Excluded c := by
  by_cases h : p.Allowlist c
  · exact Or.inl h
  · exact Or.inr ((deny_iff_not_mem_allowlist p c).mpr h)

/-- Corollary: no request is both allowed and excluded. -/
theorem allowlist_disjoint_excluded (p : Policy S R A) (c : Capability S R A) :
    ¬ (p.Allowlist c ∧ p.Excluded c) := by
  rintro ⟨h1, h2⟩
  exact (deny_iff_not_mem_allowlist p c).mp h2 h1

/-- Corollary: the empty policy denies everything. -/
theorem empty_policy_denies_all (c : Capability S R A) :
    (⟨[]⟩ : Policy S R A).evaluate c = Decision.deny := rfl

/-- Corollary: the fully-wildcard policy allows everything. -/
theorem wildcard_policy_allows_all (c : Capability S R A) :
    (⟨[⟨Pattern.any, Pattern.any, Pattern.any⟩]⟩ : Policy S R A).evaluate c
      = Decision.allow := rfl

end Invariant

/-! ## A concrete finite instantiation, checked by decision procedure -/

namespace Example

/-- Three principals. -/
inductive Subj where | app | plugin | kernel
  deriving DecidableEq, Repr

/-- Three resources. -/
inductive Res where | net | disk | cam
  deriving DecidableEq, Repr

/-- Two actions. -/
inductive Act where | read | write
  deriving DecidableEq, Repr

/-- A sample policy: the app may read anything; the plugin may read the network only. -/
def samplePolicy : Policy Subj Res Act :=
  ⟨[ ⟨Pattern.exact Subj.app, Pattern.any, Pattern.exact Act.read⟩,
     ⟨Pattern.exact Subj.plugin, Pattern.exact Res.net, Pattern.exact Act.read⟩ ]⟩

/-- Concrete finite check: for the sample policy, each of the 18 possible
capability requests is denied exactly when no rule covers it. -/
theorem sample_default_deny (c : Capability Subj Res Act) :
    (samplePolicy.evaluate c = Decision.deny) ↔
      ¬ (samplePolicy.rules.any (fun r => decide (r.Covers c)) = true) := by
  obtain ⟨s, r, a⟩ := c
  cases s <;> cases r <;> cases a <;> decide

/-- The kernel principal has no capabilities at all under the sample policy. -/
theorem kernel_fully_excluded (c : Capability Subj Res Act)
    (h : c.subject = Subj.kernel) : samplePolicy.evaluate c = Decision.deny := by
  obtain ⟨s, r, a⟩ := c
  cases s <;> cases r <;> cases a <;> simp_all <;> decide

/-- The app may read the camera, but may not write to it. -/
theorem app_read_cam_allowed :
    samplePolicy.evaluate ⟨Subj.app, Res.cam, Act.read⟩ = Decision.allow := rfl

theorem app_write_cam_denied :
    samplePolicy.evaluate ⟨Subj.app, Res.cam, Act.write⟩ = Decision.deny := rfl

end Example

end PCA

import Mathlib
import RequestProject.PCA.Invariant

/-!
# Default deny, restated with Mathlib `Set`s

`RequestProject/PCA/Invariant.lean` must begin with the required header comment,
which in Lean 4 forces that module to have no `import` line.  This companion
module therefore re-exposes the main invariant in Mathlib's set-theoretic
language: the excluded (denied) requests form exactly the complement of the
policy's allowlist, and the two sets partition the space of requests.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

variable {S R A : Type _} [DecidableEq S] [DecidableEq R] [DecidableEq A]

/-- The allowlist of a policy, as a Mathlib `Set`. -/
def Policy.allowSet (p : Policy S R A) : Set (Capability S R A) :=
  {c | p.Allowlist c}

/-- The excluded (denied) requests of a policy, as a Mathlib `Set`. -/
def Policy.excludedSet (p : Policy S R A) : Set (Capability S R A) :=
  {c | p.evaluate c = Decision.deny}

namespace Invariant

/-- Set-theoretic form of the main invariant: the denied set is precisely the
complement of the allowlist. -/
theorem excludedSet_eq_compl_allowSet (p : Policy S R A) :
    p.excludedSet = (p.allowSet)ᶜ := by
  ext c
  simpa [Policy.excludedSet, Policy.allowSet, Set.mem_compl_iff] using
    deny_iff_not_mem_allowlist p c

/-- The allowlist and the excluded set cover everything. -/
theorem allowSet_union_excludedSet (p : Policy S R A) :
    p.allowSet ∪ p.excludedSet = Set.univ := by
  rw [excludedSet_eq_compl_allowSet, Set.union_compl_self]

/-- The allowlist and the excluded set are disjoint. -/
theorem allowSet_disjoint_excludedSet (p : Policy S R A) :
    Disjoint p.allowSet p.excludedSet := by
  rw [excludedSet_eq_compl_allowSet]
  exact disjoint_compl_right

end Invariant

end PCA

