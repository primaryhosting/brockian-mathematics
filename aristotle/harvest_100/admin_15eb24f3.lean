/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-! ## The model of the isolation engine

A *proof-carrying app* runs inside an isolation engine.  Resources are named by
hierarchical paths (a list of path segments), and each access is tagged with a
capability (read / write / execute).  A *policy* is a finite list of grants; a
grant authorises a capability on every resource lying under a given path prefix.

`InScope` is the declarative (specification-level) notion of an access being
permitted.  `inScopeCheck` is the executable Boolean decision procedure that the
engine actually runs.  The target theorem states that the executable encoding is
both *sound* (it never accepts an access that the specification forbids) and
*complete* (it never rejects an access that the specification permits). -/

/-- A resource name: a hierarchical path, given as its list of segments. -/
abbrev Path := List String

/-- The capabilities an access can require. -/
inductive Cap
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A single grant in a policy: all capabilities in `caps` are authorised on
every resource whose path extends `root`. -/
structure Grant where
  root : Path
  caps : List Cap
  deriving DecidableEq, Repr

/-- A policy is a finite list of grants. -/
abbrev Policy := List Grant

/-- Specification: the access of capability `c` to resource `p` is in scope for
policy `P` when some grant of `P` both covers `p` (its root is a prefix of `p`)
and confers `c`. -/
def InScope (P : Policy) (c : Cap) (p : Path) : Prop :=
  ∃ g ∈ P, g.root <+: p ∧ c ∈ g.caps

/-- Executable encoding of a single grant's coverage check. -/
def grantCovers (g : Grant) (c : Cap) (p : Path) : Bool :=
  g.root.isPrefixOf p && g.caps.contains c

/-- Executable encoding of the in-scope check run by the isolation engine. -/
def inScopeCheck (P : Policy) (c : Cap) (p : Path) : Bool :=
  P.any (fun g => grantCovers g c p)

/-- Pointwise correctness of the per-grant coverage encoding. -/
theorem grantCovers_eq_true_iff (g : Grant) (c : Cap) (p : Path) :
    grantCovers g c p = true ↔ (g.root <+: p ∧ c ∈ g.caps) := by
  simp [grantCovers, List.isPrefixOf_iff_prefix]

/-- **Target.**  The executable in-scope encoding is sound and complete with
respect to the declarative isolation specification: the engine's Boolean check
accepts exactly the accesses that the policy authorises. -/
theorem in_scope_encoding_sound (P : Policy) (c : Cap) (p : Path) :
    inScopeCheck P c p = true ↔ InScope P c p := by
  simp [inScopeCheck, InScope, List.any_eq_true, grantCovers_eq_true_iff]

/-- Soundness direction, stated separately: an accepted access is authorised. -/
theorem in_scope_encoding_sound_of_check (P : Policy) (c : Cap) (p : Path)
    (h : inScopeCheck P c p = true) : InScope P c p :=
  (in_scope_encoding_sound P c p).mp h

/-- Completeness direction: an authorised access is accepted. -/
theorem in_scope_encoding_complete (P : Policy) (c : Cap) (p : Path)
    (h : InScope P c p) : inScopeCheck P c p = true :=
  (in_scope_encoding_sound P c p).mpr h

/-- Negative form: the engine rejects exactly the unauthorised accesses. -/
theorem in_scope_encoding_reject (P : Policy) (c : Cap) (p : Path) :
    inScopeCheck P c p = false ↔ ¬ InScope P c p := by
  rw [← in_scope_encoding_sound P c p, Bool.not_eq_true]

/-- `InScope` is decidable, witnessed by the engine's executable check. -/
instance instDecidableInScope (P : Policy) (c : Cap) (p : Path) :
    Decidable (InScope P c p) :=
  decidable_of_iff _ (in_scope_encoding_sound P c p)

/-- The empty policy isolates completely: no access is in scope. -/
theorem not_inScope_nil (c : Cap) (p : Path) : ¬ InScope [] c p := by
  simp [InScope]

/-- Enlarging the policy can only enlarge the set of permitted accesses. -/
theorem inScope_mono {P Q : Policy} (hPQ : P ⊆ Q) {c : Cap} {p : Path}
    (h : InScope P c p) : InScope Q c p := by
  obtain ⟨g, hg, hcov, hc⟩ := h
  exact ⟨g, hPQ hg, hcov, hc⟩

/-- Scope is closed downwards along the resource hierarchy: if an access is in
scope for a directory, it is in scope for everything beneath it. -/
theorem inScope_of_prefix {P : Policy} {c : Cap} {p q : Path} (hpq : p <+: q)
    (h : InScope P c p) : InScope P c q := by
  obtain ⟨g, hg, hcov, hc⟩ := h
  exact ⟨g, hg, hcov.trans hpq, hc⟩

end PCA.Isolation

