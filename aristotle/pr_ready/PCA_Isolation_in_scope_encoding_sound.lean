/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/



-- This development needs no Mathlib import: every lemma used
-- (`List.isPrefixOf_iff_prefix`, `List.any_eq_true`, `decidable_of_iff`)
-- is available in the Lean 4 core library, and the required header comment
-- must be the first thing in the file (Lean forbids `import` after a `/-! -/`
-- module docstring).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-! ## The isolation model

A *resource* is identified by a hierarchical path (a list of path components).
A *scope* granted to an application is a path prefix: holding the scope `s`
authorises access to every resource whose path extends `s.root`.

The isolation engine of a proof-carrying app does not reason with the
propositional predicate directly; it evaluates a decidable *encoding*
(a `Bool`-valued function) built from `List.isPrefixOf` / `List.any`.
The theorems below state that this encoding is sound and complete with
respect to the intended semantics. -/

/-- A resource path: a list of hierarchical components. -/
abbrev Path := List String

/-- A capability scope: everything below `root` is authorised. -/
structure Scope where
  root : Path
  deriving DecidableEq

/-- Semantics of a single scope: `s` covers `p` when `s.root` is a prefix of `p`. -/
def Scope.Covers (s : Scope) (p : Path) : Prop := s.root <+: p

/-- Boolean encoding of `Scope.Covers`, as evaluated by the isolation engine. -/
def Scope.coversB (s : Scope) (p : Path) : Bool := s.root.isPrefixOf p

/-- A policy is the list of scopes granted to an application. -/
abbrev Policy := List Scope

/-- Semantics: a path is in scope for a policy when some granted scope covers it. -/
def InScope (pol : Policy) (p : Path) : Prop := ∃ s ∈ pol, s.Covers p

/-- The engine's decision procedure: the boolean encoding of `InScope`. -/
def inScopeB (pol : Policy) (p : Path) : Bool := pol.any (fun s => s.coversB p)

/-- Soundness and completeness of the single-scope encoding.
The Mathlib/core lemma `List.isPrefixOf_iff_prefix` closes this immediately. -/
theorem covers_encoding_sound (s : Scope) (p : Path) :
    s.coversB p = true ↔ s.Covers p :=
  List.isPrefixOf_iff_prefix

/-- **Main theorem.** The isolation engine's boolean encoding of "the requested
resource is in scope" is sound and complete with respect to the intended
semantics: `inScopeB pol p` returns `true` exactly when some granted scope of
the policy covers the requested path.

The proof reduces to `List.any_eq_true` together with the core lemma
`List.isPrefixOf_iff_prefix`. -/
theorem in_scope_encoding_sound (pol : Policy) (p : Path) :
    inScopeB pol p = true ↔ InScope pol p := by
  simp only [inScopeB, InScope, List.any_eq_true, covers_encoding_sound]

/-! ## Consequences for isolation -/

/-- Soundness direction: a `true` verdict is justified by an actual grant. -/
theorem in_scope_of_encoding (pol : Policy) (p : Path) (h : inScopeB pol p = true) :
    InScope pol p := (in_scope_encoding_sound pol p).1 h

/-- Isolation: if the engine denies access, no granted scope covers the path. -/
theorem not_in_scope_of_encoding_false (pol : Policy) (p : Path)
    (h : inScopeB pol p = false) : ¬ InScope pol p := by
  intro hp
  have := (in_scope_encoding_sound pol p).2 hp
  simp [h] at this

/-- The semantic predicate is decidable, with the engine's encoding as decision
procedure. -/
instance (pol : Policy) (p : Path) : Decidable (InScope pol p) :=
  decidable_of_iff _ (in_scope_encoding_sound pol p)

/-- The empty policy grants nothing: total isolation. -/
theorem not_in_scope_nil (p : Path) : ¬ InScope [] p := by
  simp [InScope]

/-- Monotonicity: enlarging a policy can only enlarge the set of in-scope paths. -/
theorem in_scope_mono {pol pol' : Policy} (h : pol ⊆ pol') {p : Path}
    (hp : InScope pol p) : InScope pol' p := by
  obtain ⟨s, hs, hcov⟩ := hp
  exact ⟨s, h hs, hcov⟩

end PCA.Isolation

#print axioms PCA.Isolation.in_scope_encoding_sound

