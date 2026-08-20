/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- Actions a proof-carrying app may request on a resource. -/
inductive Action where
  | read | write | exec
  deriving DecidableEq, Repr

/-- A resource path: a list of interned path segments. -/
abbrev Path := List Nat

/-- A capability: an action on a resource path. -/
structure Cap where
  action : Action
  path : Path
  deriving DecidableEq, Repr

/-- A scope of the isolation engine: prefix grants, together with deny rules
that override grants. -/
structure Scope where
  grants : List Cap
  denies : List Cap

/-- `Covers g c` : the rule `g` applies to the capability `c`, i.e. it concerns the
same action and its path is a prefix of (an ancestor of) the requested path. -/
def Covers (g c : Cap) : Prop := g.action = c.action ∧ g.path <+: c.path

/-- The semantic (model-level) in-scope relation of the isolation engine:
some grant covers the capability and no deny rule does. -/
def InScope (s : Scope) (c : Cap) : Prop :=
  (∃ g ∈ s.grants, Covers g c) ∧ ∀ d ∈ s.denies, ¬ Covers d c

/-- Numeric tag of an action in the wire encoding. -/
def encAction : Action → Nat
  | .read => 0
  | .write => 1
  | .exec => 2

/-- Flat wire encoding of a capability: the action tag followed by the path. -/
def encodeCap (c : Cap) : Path := encAction c.action :: c.path

/-- The isolation engine's decision procedure, run entirely on encoded
capabilities: a request is allowed iff some encoded grant is a prefix of the
encoded request and no encoded deny rule is. -/
def inScopeEnc (s : Scope) (c : Cap) : Bool :=
  (s.grants.map encodeCap).any (fun g => g.isPrefixOf (encodeCap c)) &&
    !((s.denies.map encodeCap).any (fun d => d.isPrefixOf (encodeCap c)))

theorem encAction_injective : Function.Injective encAction := by
  intro a b h
  cases a <;> cases b <;> simp_all [encAction]

theorem encodeCap_injective : Function.Injective encodeCap := by
  intro a b h
  simp only [encodeCap, List.cons.injEq] at h
  obtain ⟨ha, hp⟩ := h
  cases a; cases b
  simp only [Cap.mk.injEq]
  exact ⟨encAction_injective ha, hp⟩

/-- The prefix test on encodings coincides exactly with the semantic
"rule applies" relation: the encoding introduces neither confusion between
actions nor spurious prefix relations across the action tag. -/
theorem isPrefixOf_encodeCap_iff (g c : Cap) :
    (encodeCap g).isPrefixOf (encodeCap c) = true ↔ Covers g c := by
  rw [List.isPrefixOf_iff_prefix]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    simp only [encodeCap, List.cons_append, List.cons.injEq] at ht
    exact ⟨encAction_injective ht.1, ⟨t, ht.2⟩⟩
  · rintro ⟨hact, t, ht⟩
    exact ⟨t, by simp [encodeCap, hact, ht]⟩

/-- **Main result.** The isolation engine's encoded decision procedure is sound
and complete with respect to the semantic in-scope relation of the model:
`inScopeEnc` returns `true` exactly on the capabilities that are genuinely in
scope. -/
theorem in_scope_encoding_sound (s : Scope) (c : Cap) :
    inScopeEnc s c = true ↔ InScope s c := by
  simp only [inScopeEnc, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.any_eq_false, List.mem_map, InScope]
  constructor
  · rintro ⟨⟨_, ⟨g, hg, rfl⟩, hpre⟩, hden⟩
    refine ⟨⟨g, hg, (isPrefixOf_encodeCap_iff g c).1 hpre⟩, ?_⟩
    intro d hd hcov
    exact hden (encodeCap d) ⟨d, hd, rfl⟩ ((isPrefixOf_encodeCap_iff d c).2 hcov)
  · rintro ⟨⟨g, hg, hcov⟩, hden⟩
    refine ⟨⟨encodeCap g, ⟨g, hg, rfl⟩, (isPrefixOf_encodeCap_iff g c).2 hcov⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩ hpre
    exact hden d hd ((isPrefixOf_encodeCap_iff d c).1 hpre)

/-- A capability that is in scope is covered by some grant. -/
theorem InScope.exists_grant {s : Scope} {c : Cap} (h : InScope s c) :
    ∃ g ∈ s.grants, Covers g c := h.1

/-- No denied capability is in scope. -/
theorem InScope.not_denied {s : Scope} {c : Cap} (h : InScope s c)
    {d : Cap} (hd : d ∈ s.denies) : ¬ Covers d c := h.2 d hd

/-- Decidability of the semantic in-scope relation, transported along the encoding. -/
instance decidableInScope (s : Scope) (c : Cap) : Decidable (InScope s c) :=
  decidable_of_iff _ (in_scope_encoding_sound s c)

end PCA.Isolation

section Sanity

open PCA.Isolation

/-- A granted read under `[1]` on the path `[1, 2]` is in scope. -/
example :
    InScope { grants := [⟨.read, [1]⟩], denies := [] } ⟨.read, [1, 2]⟩ := by decide

/-- Writing is not granted by a read grant: the action tag is respected. -/
example :
    ¬ InScope { grants := [⟨.read, [1]⟩], denies := [] } ⟨.write, [1, 2]⟩ := by decide

/-- A deny rule overrides a grant. -/
example :
    ¬ InScope { grants := [⟨.read, [1]⟩], denies := [⟨.read, [1, 2]⟩] } ⟨.read, [1, 2, 3]⟩ := by
  decide

/-- Paths outside the granted subtree are out of scope. -/
example : ¬ InScope { grants := [⟨.read, [1]⟩], denies := [] } ⟨.read, [2]⟩ := by decide

end Sanity

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

