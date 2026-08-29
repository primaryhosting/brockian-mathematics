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

/-
Note on imports: a Lean module docstring must be the first command in the file and
`import` lines have to precede every command, so the header comment above rules out
any `import`.  The development below is therefore self-contained: it uses only the
Lean 4 core logic (`propext`, `funext`, `Classical`) and re-develops the handful of
set-theoretic notions (membership, complement, intersection, union, extensionality)
that the statement needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace PCA

/-! ## Sets of capabilities -/

/-- A set of capabilities, modelled as a predicate on the capability type. -/
def CapSet (Cap : Type u) : Type u := Cap → Prop

namespace CapSet

variable {Cap : Type u}

instance : Membership Cap (CapSet Cap) := ⟨fun s c => s c⟩

@[simp] theorem mem_def (s : CapSet Cap) (c : Cap) : (c ∈ s) = s c := rfl

/-- The set of capabilities satisfying a predicate. -/
def ofPred (p : Cap → Prop) : CapSet Cap := p

/-- The complement of a set of capabilities. -/
def compl (s : CapSet Cap) : CapSet Cap := fun c => ¬ (c ∈ s)

/-- The intersection of two sets of capabilities. -/
def inter (s t : CapSet Cap) : CapSet Cap := fun c => c ∈ s ∧ c ∈ t

/-- The union of two sets of capabilities. -/
def union (s t : CapSet Cap) : CapSet Cap := fun c => c ∈ s ∨ c ∈ t

/-- The empty set of capabilities. -/
def empty : CapSet Cap := fun _ => False

/-- The set of all capabilities. -/
def univ : CapSet Cap := fun _ => True

/-- Inclusion of sets of capabilities. -/
def Subset (s t : CapSet Cap) : Prop := ∀ ⦃c : Cap⦄, c ∈ s → c ∈ t

/-- Two sets of capabilities with the same members are equal. -/
theorem ext {s t : CapSet Cap} (h : ∀ c : Cap, c ∈ s ↔ c ∈ t) : s = t :=
  funext fun c => propext (h c)

theorem antisymm {s t : CapSet Cap} (h₁ : Subset s t) (h₂ : Subset t s) : s = t :=
  ext fun _ => ⟨fun hc => h₁ hc, fun hc => h₂ hc⟩

end CapSet

/-! ## The isolation engine -/

/-- The verdict returned by the isolation engine for a single capability request. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

theorem Decision.allow_ne_deny : Decision.allow ≠ Decision.deny := by
  intro h
  exact Decision.noConfusion h

/-- An isolation policy is given by its allowlist: the set of capabilities the
engine is explicitly permitted to grant.  Every other capability is denied by
default ("default deny"). -/
structure Policy (Cap : Type u) where
  /-- The set of explicitly permitted capabilities. -/
  allowlist : CapSet Cap

namespace Policy

variable {Cap : Type u}

open Classical in
/-- The default-deny evaluation function of the isolation engine: a capability is
allowed exactly when it appears on the allowlist, and denied otherwise. -/
noncomputable def evaluate (P : Policy Cap) (c : Cap) : Decision :=
  if c ∈ P.allowlist then Decision.allow else Decision.deny

/-- The set of capabilities the engine denies. -/
def denied (P : Policy Cap) : CapSet Cap := fun c => P.evaluate c = Decision.deny

/-- The set of capabilities the engine grants. -/
def granted (P : Policy Cap) : CapSet Cap := fun c => P.evaluate c = Decision.allow

theorem evaluate_of_mem {P : Policy Cap} {c : Cap} (h : c ∈ P.allowlist) :
    P.evaluate c = Decision.allow := by
  classical
  simp [evaluate, h]

theorem evaluate_of_not_mem {P : Policy Cap} {c : Cap} (h : c ∉ P.allowlist) :
    P.evaluate c = Decision.deny := by
  classical
  simp [evaluate, h]

/-- Every request receives exactly one of the two verdicts. -/
theorem evaluate_allow_or_deny (P : Policy Cap) (c : Cap) :
    P.evaluate c = Decision.allow ∨ P.evaluate c = Decision.deny :=
  Classical.byCases
    (fun h : c ∈ P.allowlist => Or.inl (evaluate_of_mem h))
    (fun h : c ∉ P.allowlist => Or.inr (evaluate_of_not_mem h))

end Policy

namespace Invariant

variable {Cap : Type u}

/-- Soundness of default deny: whatever the engine grants is on the allowlist. -/
theorem granted_subset_allowlist (P : Policy Cap) :
    CapSet.Subset P.granted P.allowlist := by
  intro c hc
  refine Classical.byCases (fun h : c ∈ P.allowlist => h) (fun h : c ∉ P.allowlist => ?_)
  have : Decision.allow = Decision.deny := by
    rw [← Policy.evaluate_of_not_mem h]
    exact hc.symm
  exact absurd this Decision.allow_ne_deny

/-- Completeness of default deny: everything on the allowlist is granted. -/
theorem allowlist_subset_granted (P : Policy Cap) :
    CapSet.Subset P.allowlist P.granted := fun _ hc => Policy.evaluate_of_mem hc

/-- The engine denies a capability exactly when it is off the allowlist. -/
theorem denied_iff_not_mem_allowlist (P : Policy Cap) (c : Cap) :
    P.evaluate c = Decision.deny ↔ c ∉ P.allowlist := by
  constructor
  · intro h hmem
    have : Decision.allow = Decision.deny := (Policy.evaluate_of_mem hmem).symm.trans h
    exact absurd this Decision.allow_ne_deny
  · intro h
    exact Policy.evaluate_of_not_mem h

/-- The engine allows a capability exactly when it is on the allowlist. -/
theorem allowed_iff_mem_allowlist (P : Policy Cap) (c : Cap) :
    P.evaluate c = Decision.allow ↔ c ∈ P.allowlist := by
  constructor
  · intro h
    exact granted_subset_allowlist P (show c ∈ P.granted from h)
  · intro h
    exact Policy.evaluate_of_mem h

/-- **Default deny excludes only the allowlist.**

In the isolation engine's model, the set of capabilities that are denied is
*exactly* the complement of the allowlist.  Stated in full: a capability is
denied iff it is not allowlisted; it is granted iff it is allowlisted; the
granted set coincides with the allowlist; and the granted and denied sets
partition the capability space.  This is simultaneously the soundness statement
(nothing outside the allowlist slips through) and the completeness statement
(nothing on the allowlist is spuriously blocked) for default deny. -/
theorem default_deny_excludes_only_allowlist (P : Policy Cap) :
    P.denied = CapSet.compl P.allowlist ∧
      P.granted = P.allowlist ∧
      (∀ c : Cap, P.evaluate c = Decision.deny ↔ c ∉ P.allowlist) ∧
      (∀ c : Cap, P.evaluate c = Decision.allow ↔ c ∈ P.allowlist) ∧
      CapSet.inter P.granted P.denied = CapSet.empty ∧
      CapSet.union P.granted P.denied = CapSet.univ := by
  have hden : ∀ c : Cap, P.evaluate c = Decision.deny ↔ c ∉ P.allowlist :=
    denied_iff_not_mem_allowlist P
  have hall : ∀ c : Cap, P.evaluate c = Decision.allow ↔ c ∈ P.allowlist :=
    allowed_iff_mem_allowlist P
  refine ⟨?_, ?_, hden, hall, ?_, ?_⟩
  · exact CapSet.ext fun c => hden c
  · exact CapSet.antisymm (granted_subset_allowlist P) (allowlist_subset_granted P)
  · refine CapSet.ext fun c => ⟨?_, ?_⟩
    · rintro ⟨hg, hd⟩
      have : Decision.allow = Decision.deny := (show P.evaluate c = Decision.allow from hg).symm.trans hd
      exact absurd this Decision.allow_ne_deny
    · intro h
      exact absurd h (fun h => h)
  · refine CapSet.ext fun c => ⟨fun _ => trivial, fun _ => ?_⟩
    exact P.evaluate_allow_or_deny c

end Invariant

end PCA

import Mathlib
import RequestProject.PCA.Invariant

/-!
# Default deny, restated with Mathlib's `Set`

The target theorem `PCA.Invariant.default_deny_excludes_only_allowlist` lives in the
module `RequestProject.PCA.Invariant`, whose mandated header docstring forbids any
`import` (a module docstring must be the first command of a file, and imports must
precede every command).  That development is therefore self-contained over Lean core.

This companion module imports Mathlib and transports the model and the invariant to
Mathlib's `Set`, so the statement can be used with the full Mathlib set API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA

universe u

variable {Cap : Type u}

/-- The Mathlib `Set` underlying a `CapSet`. -/
def CapSet.toSet (s : CapSet Cap) : Set Cap := {c | c ∈ s}

@[simp] theorem CapSet.mem_toSet (s : CapSet Cap) (c : Cap) : c ∈ s.toSet ↔ c ∈ s := Iff.rfl

@[simp] theorem CapSet.toSet_compl (s : CapSet Cap) : (CapSet.compl s).toSet = s.toSetᶜ := rfl

@[simp] theorem CapSet.toSet_inter (s t : CapSet Cap) :
    (CapSet.inter s t).toSet = s.toSet ∩ t.toSet := rfl

@[simp] theorem CapSet.toSet_union (s t : CapSet Cap) :
    (CapSet.union s t).toSet = s.toSet ∪ t.toSet := rfl

@[simp] theorem CapSet.toSet_empty : (CapSet.empty : CapSet Cap).toSet = (∅ : Set Cap) := rfl

@[simp] theorem CapSet.toSet_univ : (CapSet.univ : CapSet Cap).toSet = (Set.univ : Set Cap) := rfl

namespace Invariant

/-- **Default deny excludes only the allowlist**, phrased with Mathlib's `Set`:
the denied set is exactly the complement of the allowlist, the granted set is exactly
the allowlist, and granted/denied partition the space of capabilities. -/
theorem default_deny_excludes_only_allowlist_set (P : Policy Cap) :
    P.denied.toSet = (P.allowlist.toSet)ᶜ ∧
      P.granted.toSet = P.allowlist.toSet ∧
      (∀ c : Cap, P.evaluate c = Decision.deny ↔ c ∉ P.allowlist.toSet) ∧
      (∀ c : Cap, P.evaluate c = Decision.allow ↔ c ∈ P.allowlist.toSet) ∧
      P.granted.toSet ∩ P.denied.toSet = (∅ : Set Cap) ∧
      P.granted.toSet ∪ P.denied.toSet = (Set.univ : Set Cap) := by
  obtain ⟨hden, hgr, hdiff, hallow, hinter, hunion⟩ :=
    default_deny_excludes_only_allowlist P
  refine ⟨?_, ?_, hdiff, hallow, ?_, ?_⟩
  · rw [hden, CapSet.toSet_compl]
  · rw [hgr]
  · rw [← CapSet.toSet_inter, hinter, CapSet.toSet_empty]
  · rw [← CapSet.toSet_union, hunion, CapSet.toSet_univ]

end Invariant

end PCA

