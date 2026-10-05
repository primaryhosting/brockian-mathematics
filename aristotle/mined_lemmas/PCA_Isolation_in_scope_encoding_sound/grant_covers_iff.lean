/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-! ## The isolation model

A proof-carrying app runs against an *isolation engine*: every resource access it
performs must be checked against the app's declared *scope*.  We model resources as
hierarchical paths (lists of name segments), and a scope as a list of positive
*grants* (a subtree root, together with a flag saying whether writing is permitted
inside that subtree) plus a list of *denied* subtrees which override every grant.

The declarative meaning of "this request is in scope" is the predicate `InScope`.
The engine, however, cannot evaluate an existential quantifier: it runs a concrete
boolean decision procedure, `encodeInScope`.  The target theorem states that this
boolean encoding is *sound and complete* for the declarative predicate. -/

/-- A path segment, i.e. one component of a resource name. -/
abbrev Seg : Type := String

/-- A resource is named by a hierarchical path. -/
abbrev Path : Type := List Seg

/-- The access mode of a request. -/
inductive Mode where
  | read : Mode
  | write : Mode
  deriving DecidableEq, Repr

/-- A positive capability: the subtree rooted at `root` may be read, and may also be
written when `mayWrite = true`. -/
structure Grant where
  root : Path
  mayWrite : Bool
  deriving Repr

/-- An app's isolation scope: positive grants, plus denied subtrees which take
priority over every grant. -/
structure Scope where
  grants : List Grant
  denies : List Path
  deriving Repr

/-- A resource access request. -/
structure Request where
  path : Path
  mode : Mode
  deriving Repr

/-- `g` covers the request `q`: the request's path lies in the subtree rooted at
`g.root`, and the grant is strong enough for the request's mode. -/

theorem grant_covers_iff (g : Grant) (q : Request) :
    g.covers q = true ↔ g.Covers q := by
  unfold Grant.covers Grant.Covers
  rw [Bool.and_eq_true, List.isPrefixOf_iff_prefix, Bool.or_eq_true]
  constructor
  · rintro ⟨hp, hm⟩
    refine ⟨hp, ?_⟩
    intro hw
    rcases hm with hm | hm
    · exact hm
    · simp only [decide_eq_true_eq] at hm
      exact absurd (hm ▸ hw) (by simp)
  · rintro ⟨hp, hm⟩
    refine ⟨hp, ?_⟩
    cases hq : q.mode with
    | read => exact Or.inr (by simp)
    | write => exact Or.inl (hm hq)

/-- The boolean block test agrees with its declarative meaning. -/
