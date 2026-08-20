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
