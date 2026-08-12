import Mathlib

/-!
# A formal model of the isolation engine's scope check

This file gives a self-contained formal model of the *isolation engine* used to decide
whether a resource (identified by a hierarchical path) is inside a given isolation
scope, together with a proof that the executable (boolean) encoding of the check is
**sound and complete** with respect to the declarative specification.

## The model

* A resource path is a `List α` of path segments (e.g. `["tenant", "db", "table"]`).
* An isolation `Scope` consists of a list of *allow* prefixes and a list of *deny*
  prefixes.
* Declaratively (`InScope`), a path is in scope when some allow prefix is a prefix of
  the path and no deny prefix is a prefix of the path — i.e. deny always overrides
  allow.
* Operationally (`encodeInScope`), the engine evaluates a boolean expression built from
  `List.isPrefixOf` tests.

The main theorem `PCA.Isolation.in_scope_encoding_sound` states that the boolean
encoding returns `true` exactly on the paths that satisfy the declarative
specification; soundness and completeness are the two directions of this equivalence.
-/

namespace PCA.Isolation

universe u

variable {α : Type u}

/-- An isolation scope: a list of allowed path prefixes and a list of denied path
prefixes. -/
structure Scope (α : Type u) where
  /-- Path prefixes that grant access. -/
  allows : List (List α)
  /-- Path prefixes that revoke access; deny overrides allow. -/
  denies : List (List α)
  deriving Repr

/-- Declarative specification of the isolation check: the path `p` is in the scope `s`
when some allow prefix matches `p` and no deny prefix matches `p`. -/
def InScope (s : Scope α) (p : List α) : Prop :=
  (∃ a ∈ s.allows, a <+: p) ∧ ∀ d ∈ s.denies, ¬ d <+: p

/-- The executable encoding of the isolation check used by the engine. -/
def encodeInScope [BEq α] (s : Scope α) (p : List α) : Bool :=
  s.allows.any (fun a => a.isPrefixOf p) && !s.denies.any (fun d => d.isPrefixOf p)

section Lawful

variable [BEq α] [LawfulBEq α]

/-- The allow part of the encoding is equivalent to its specification. -/
theorem any_allows_iff (s : Scope α) (p : List α) :
    (s.allows.any fun a => a.isPrefixOf p) = true ↔ ∃ a ∈ s.allows, a <+: p := by
  simp [List.any_eq_true, List.isPrefixOf_iff_prefix]

/-- The deny part of the encoding is equivalent to its specification. -/
theorem not_any_denies_iff (s : Scope α) (p : List α) :
    (!s.denies.any fun d => d.isPrefixOf p) = true ↔ ∀ d ∈ s.denies, ¬ d <+: p := by
  simp [List.isPrefixOf_iff_prefix]

/-- **Soundness and completeness of the isolation engine's scope encoding.**

The boolean decision procedure `encodeInScope` returns `true` on exactly those paths
that the declarative specification `InScope` admits. Read left to right this is
soundness (every accepted path really is in scope), and right to left completeness
(every in-scope path is accepted). -/
theorem in_scope_encoding_sound (s : Scope α) (p : List α) :
    encodeInScope s p = true ↔ InScope s p := by
  rw [encodeInScope, Bool.and_eq_true, any_allows_iff, not_any_denies_iff, InScope]

/-- Completeness restated on the negative side: the engine rejects exactly the paths
that are out of scope. -/
theorem in_scope_encoding_complete (s : Scope α) (p : List α) :
    encodeInScope s p = false ↔ ¬ InScope s p := by
  rw [← in_scope_encoding_sound, Bool.not_eq_true]

/-- The declarative isolation check is decidable, via the engine's encoding. -/
instance instDecidableInScope (s : Scope α) (p : List α) : Decidable (InScope s p) :=
  decidable_of_iff _ (in_scope_encoding_sound s p)

end Lawful

/-- Deny overrides allow: a denied prefix puts the path out of scope. -/
theorem not_inScope_of_denied {s : Scope α} {p d : List α}
    (hd : d ∈ s.denies) (hpre : d <+: p) : ¬ InScope s p := by
  intro h
  exact h.2 d hd hpre

/-- Without a matching allow prefix, a path is out of scope. -/
theorem not_inScope_of_no_allow {s : Scope α} {p : List α}
    (h : ∀ a ∈ s.allows, ¬ a <+: p) : ¬ InScope s p := by
  rintro ⟨⟨a, ha, hpre⟩, -⟩
  exact h a ha hpre

/-- Scope membership is closed under extending the allow list. -/
theorem inScope_mono_allows {s t : Scope α} {p : List α}
    (hallow : s.allows ⊆ t.allows) (hdeny : t.denies ⊆ s.denies)
    (h : InScope s p) : InScope t p := by
  obtain ⟨⟨a, ha, hpre⟩, hden⟩ := h
  exact ⟨⟨a, hallow ha, hpre⟩, fun d hd => hden d (hdeny hd)⟩

/-- **Non-interference / isolation.** If every prefix allowed by `s` is itself denied by
`t`, then no path can be in both scopes: the two scopes are perfectly isolated. -/
theorem inScope_disjoint {s t : Scope α}
    (h : ∀ a ∈ s.allows, ∃ d ∈ t.denies, d <+: a) (p : List α) :
    InScope s p → ¬ InScope t p := by
  rintro ⟨⟨a, ha, hpre⟩, -⟩
  obtain ⟨d, hd, hda⟩ := h a ha
  exact not_inScope_of_denied hd (hda.trans hpre)

/-- The engine's batch operation: keep exactly the resources that pass the scope check. -/
def filterInScope [BEq α] (s : Scope α) (rs : List (List α)) : List (List α) :=
  rs.filter (encodeInScope s)

section Batch

variable [BEq α] [LawfulBEq α]

/-- Soundness and completeness of the batch filter: it retains exactly the resources of
the input that are in scope. -/
theorem mem_filterInScope_iff (s : Scope α) (rs : List (List α)) (p : List α) :
    p ∈ filterInScope s rs ↔ p ∈ rs ∧ InScope s p := by
  simp [filterInScope, List.mem_filter, in_scope_encoding_sound]

/-- The batch filter never invents resources. -/
theorem filterInScope_subset (s : Scope α) (rs : List (List α)) :
    filterInScope s rs ⊆ rs := fun _ h => ((mem_filterInScope_iff s rs _).1 h).1

omit [LawfulBEq α] in
/-- Filtering is idempotent: a second pass of the engine removes nothing. -/
theorem filterInScope_idem (s : Scope α) (rs : List (List α)) :
    filterInScope s (filterInScope s rs) = filterInScope s rs := by
  simp [filterInScope, List.filter_filter, Bool.and_self]

/-- Isolation of the batch operation: filtering through two mutually isolated scopes
yields no resources at all. -/
theorem filterInScope_disjoint {s t : Scope α}
    (h : ∀ a ∈ s.allows, ∃ d ∈ t.denies, d <+: a) (rs : List (List α)) :
    filterInScope t (filterInScope s rs) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  obtain ⟨hmem, ht⟩ := (mem_filterInScope_iff t _ p).1 hp
  obtain ⟨-, hs⟩ := (mem_filterInScope_iff s rs p).1 hmem
  exact inScope_disjoint h p hs ht

end Batch

/-- The empty scope (no allow prefixes) contains nothing. -/
theorem not_inScope_empty {p : List α} (denies : List (List α)) :
    ¬ InScope ⟨[], denies⟩ p := by
  apply not_inScope_of_no_allow
  simp

/-- A scope allowing the root prefix `[]` and denying nothing contains every path. -/
theorem inScope_root (p : List α) : InScope ⟨[[]], []⟩ p := by
  refine ⟨⟨[], by simp, by simp⟩, by simp⟩

/-! ## Worked example

A tenant scope that grants everything under `tenant1` except the `secret` subtree.
The facts below are checked by the kernel through `instDecidableInScope`, i.e. through
the verified encoding itself. -/

section Example

/-- Tenant 1 may see its own resources, except its `secret` subtree. -/
def tenant1 : Scope String :=
  ⟨[["tenant1"]], [["tenant1", "secret"]]⟩

/-- Tenant 2 may see only its own resources, and is explicitly denied tenant 1's. -/
def tenant2 : Scope String :=
  ⟨[["tenant2"]], [["tenant1"]]⟩

example : InScope tenant1 ["tenant1", "db", "users"] := by decide

example : ¬ InScope tenant1 ["tenant1", "secret", "key"] := by decide

example : ¬ InScope tenant1 ["tenant2", "db"] := by decide

example : ¬ InScope tenant1 ["tenant10", "db"] := by decide

example :
    filterInScope tenant1 [["tenant1", "db"], ["tenant1", "secret", "key"], ["tenant2"]]
      = [["tenant1", "db"]] := by decide

/-- The two tenant scopes are isolated from each other: no resource is visible to both. -/
example (p : List String) : InScope tenant1 p → ¬ InScope tenant2 p := by
  refine inScope_disjoint ?_ p
  intro a ha
  simp only [tenant1, List.mem_singleton] at ha
  subst ha
  exact ⟨["tenant1"], by simp [tenant2], List.prefix_refl _⟩

end Example

end PCA.Isolation

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

