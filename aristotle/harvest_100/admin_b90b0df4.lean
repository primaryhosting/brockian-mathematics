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
def Grant.Covers (g : Grant) (q : Request) : Prop :=
  g.root <+: q.path ∧ (q.mode = Mode.write → g.mayWrite = true)

/-- The request `q` is blocked by scope `s`: some denied subtree contains it. -/
def Scope.Blocks (s : Scope) (q : Request) : Prop :=
  ∃ d ∈ s.denies, d <+: q.path

/-- **Declarative semantics of isolation.**  A request is in scope when some grant
covers it and no deny rule blocks it. -/
def InScope (s : Scope) (q : Request) : Prop :=
  (∃ g ∈ s.grants, g.Covers q) ∧ ¬ s.Blocks q

/-- Boolean check that a single grant covers a request. -/
def Grant.covers (g : Grant) (q : Request) : Bool :=
  g.root.isPrefixOf q.path && (g.mayWrite || decide (q.mode = Mode.read))

/-- Boolean check that a scope blocks a request. -/
def Scope.blocks (s : Scope) (q : Request) : Bool :=
  s.denies.any (fun d => d.isPrefixOf q.path)

/-- **The isolation engine's executable encoding** of the in-scope test. -/
def encodeInScope (s : Scope) (q : Request) : Bool :=
  s.grants.any (fun g => g.covers q) && !s.blocks q

/-! ## Pointwise correctness of the two components -/

/-- A grant's boolean cover test agrees with its declarative meaning. -/
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
theorem scope_blocks_iff (s : Scope) (q : Request) :
    s.blocks q = true ↔ s.Blocks q := by
  unfold Scope.blocks Scope.Blocks
  simp [List.any_eq_true, List.isPrefixOf_iff_prefix]

/-! ## Main theorem -/

/-- **In-scope encoding soundness (and completeness).**

The isolation engine's executable check `encodeInScope` returns `true` on a request
exactly when that request is in scope according to the declarative model `InScope`.

Read in the `→` direction this is *soundness* of the engine's accept decision; the
`←` direction is *completeness*.  Equivalently, in contrapositive form: the engine
rejects a request precisely when no grant covers it or some deny rule blocks it. -/
theorem in_scope_encoding_sound (s : Scope) (q : Request) :
    encodeInScope s q = true ↔ InScope s q := by
  unfold encodeInScope InScope
  rw [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true]
  constructor
  · rintro ⟨⟨g, hg, hcov⟩, hb⟩
    refine ⟨⟨g, hg, (grant_covers_iff g q).mp hcov⟩, ?_⟩
    intro hblk
    rw [← scope_blocks_iff] at hblk
    exact absurd hblk (by simp [hb])
  · rintro ⟨⟨g, hg, hcov⟩, hb⟩
    refine ⟨⟨g, hg, (grant_covers_iff g q).mpr hcov⟩, ?_⟩
    cases hbq : s.blocks q with
    | false => rfl
    | true => exact absurd ((scope_blocks_iff s q).mp hbq) hb

/-- Contrapositive form: the engine denies a request exactly when the declarative
model puts it out of scope. -/
theorem not_in_scope_encoding_sound (s : Scope) (q : Request) :
    encodeInScope s q = false ↔ ¬ InScope s q := by
  rw [← in_scope_encoding_sound]
  simp

/-- Consequently `InScope` is decidable, with the engine's check as decision
procedure. -/
instance instDecidableInScope (s : Scope) (q : Request) : Decidable (InScope s q) :=
  decidable_of_iff _ (in_scope_encoding_sound s q)

/-! ## Sanity checks: the model is not vacuous -/

private def demoScope : Scope :=
  { grants := [{ root := ["app", "data"], mayWrite := true },
               { root := ["app", "cfg"], mayWrite := false }]
    denies := [["app", "data", "secret"]] }

example : encodeInScope demoScope { path := ["app", "data", "x"], mode := Mode.write } = true := by
  decide

example : encodeInScope demoScope { path := ["app", "cfg", "y"], mode := Mode.write } = false := by
  decide

example : encodeInScope demoScope { path := ["app", "cfg", "y"], mode := Mode.read } = true := by
  decide

example :
    encodeInScope demoScope { path := ["app", "data", "secret", "k"], mode := Mode.read }
      = false := by
  decide

example : encodeInScope demoScope { path := ["other"], mode := Mode.read } = false := by
  decide

end PCA.Isolation

