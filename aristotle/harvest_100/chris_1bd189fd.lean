/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Self-contained development: no external imports are needed, and Lean does not
-- permit `import` after the required module header comment above.

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

namespace PCA.Isolation

/-- An access mode requested by (or granted to) a component of a proof-carrying app. -/
inductive Mode
  | read
  | write
  deriving DecidableEq, Repr

/-- A resource of the isolation engine, identified by a hierarchical path
(e.g. `["home", "user", "data.txt"]`). -/
structure Resource where
  path : List String
  deriving DecidableEq, Repr

/-- A capability grant: every resource sitting under `prefixPath` may be accessed
with mode `mode` (a `write` grant subsumes `read`). -/
structure Grant where
  prefixPath : List String
  mode : Mode
  deriving DecidableEq, Repr

/-- The declarative (specification-level) meaning of a grant: it covers the request
`(m, r)` when its path prefix is a prefix of the resource path and the granted mode
is strong enough for the requested mode. -/
def Grant.Covers (g : Grant) (m : Mode) (r : Resource) : Prop :=
  g.prefixPath <+: r.path ∧ (m = Mode.read ∨ g.mode = Mode.write)

/-- An isolation policy is a list of capability grants. -/
abbrev Policy := List Grant

/-- Specification-level scope check: the request `(m, r)` is in scope for the policy `P`
when some grant of `P` covers it. -/
def InScope (P : Policy) (m : Mode) (r : Resource) : Prop :=
  ∃ g ∈ P, g.Covers m r

/-- Executable encoding of a single grant check used by the isolation engine. -/
def encodeGrant (m : Mode) (r : Resource) (g : Grant) : Bool :=
  g.prefixPath.isPrefixOf r.path &&
    (match m, g.mode with
     | Mode.read, _ => true
     | Mode.write, Mode.write => true
     | Mode.write, Mode.read => false)

/-- Executable encoding of the scope check: scan the policy for a covering grant. -/
def encodeInScope (P : Policy) (m : Mode) (r : Resource) : Bool :=
  P.any (encodeGrant m r)

/-- The per-grant encoding is faithful to the declarative `Grant.Covers` relation. -/
theorem encodeGrant_eq_true_iff (m : Mode) (r : Resource) (g : Grant) :
    encodeGrant m r g = true ↔ g.Covers m r := by
  obtain ⟨gp, gm⟩ := g
  unfold encodeGrant Grant.Covers
  cases m <;> cases gm <;> simp [List.isPrefixOf_iff_prefix]

/-- **Completeness of the in-scope encoding.**
If a request is in scope according to the declarative isolation policy semantics,
then the executable encoding used by the isolation engine accepts it. -/
theorem in_scope_encoding_complete (P : Policy) (m : Mode) (r : Resource)
    (h : InScope P m r) : encodeInScope P m r = true := by
  obtain ⟨g, hgP, hg⟩ := h
  refine List.any_eq_true.2 ⟨g, hgP, ?_⟩
  exact (encodeGrant_eq_true_iff m r g).2 hg

/-- **Soundness of the in-scope encoding.**
If the executable encoding accepts a request, it really is in scope. -/
theorem in_scope_encoding_sound (P : Policy) (m : Mode) (r : Resource)
    (h : encodeInScope P m r = true) : InScope P m r := by
  obtain ⟨g, hgP, hg⟩ := List.any_eq_true.1 h
  exact ⟨g, hgP, (encodeGrant_eq_true_iff m r g).1 hg⟩

/-- Soundness and completeness combined: the encoding decides the scope predicate. -/
theorem in_scope_encoding_iff (P : Policy) (m : Mode) (r : Resource) :
    encodeInScope P m r = true ↔ InScope P m r :=
  ⟨in_scope_encoding_sound P m r, in_scope_encoding_complete P m r⟩

/-- The scope predicate is therefore decidable, with the engine's encoding as decision
procedure. -/
instance instDecidableInScope (P : Policy) (m : Mode) (r : Resource) :
    Decidable (InScope P m r) :=
  decidable_of_iff (encodeInScope P m r = true) (in_scope_encoding_iff P m r)

/-- Nothing is in scope for the empty policy: full isolation by default. -/
theorem not_inScope_nil (m : Mode) (r : Resource) : ¬ InScope [] m r := by
  simp [InScope]

/-- Adding grants to a policy can only enlarge the set of in-scope requests. -/
theorem inScope_mono {P Q : Policy} (hPQ : ∀ g, g ∈ P → g ∈ Q) (m : Mode) (r : Resource)
    (h : InScope P m r) : InScope Q m r := by
  obtain ⟨g, hgP, hg⟩ := h
  exact ⟨g, hPQ g hgP, hg⟩

/-- A write permission always entails the corresponding read permission. -/
theorem inScope_read_of_write (P : Policy) (r : Resource)
    (h : InScope P Mode.write r) : InScope P Mode.read r := by
  obtain ⟨g, hgP, hg⟩ := h
  exact ⟨g, hgP, ⟨hg.1, Or.inl rfl⟩⟩

section Sanity

/-- A `write` grant on `home` puts a write request on `home/a.txt` in scope. -/
example : InScope [⟨["home"], Mode.write⟩] Mode.write ⟨["home", "a.txt"]⟩ :=
  in_scope_encoding_sound _ _ _ (by decide)

/-- A `read`-only grant does not put a write request in scope: the model is not vacuous. -/
example : ¬ InScope [⟨["home"], Mode.read⟩] Mode.write ⟨["home", "a.txt"]⟩ := by
  intro h
  have := in_scope_encoding_complete _ _ _ h
  revert this
  decide

/-- A grant on a different subtree does not put the request in scope. -/
example : ¬ InScope [⟨["tmp"], Mode.write⟩] Mode.read ⟨["home", "a.txt"]⟩ := by
  intro h
  have := in_scope_encoding_complete _ _ _ h
  revert this
  decide

end Sanity

end PCA.Isolation

