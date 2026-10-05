/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-! ## The abstract model

An *isolation engine* mediates every access an application makes to a resource.
Resources are addressed by hierarchical paths (`List String`), and every access
is performed in one of two modes.  A *policy* is a list of capabilities, each of
which grants one mode on a whole subtree of the resource hierarchy.

The engine does not scan the policy list at access time; instead the policy is
*encoded* once into a prefix tree (`Trie`) which the engine then walks.  The
results below relate the declarative notion `InScope` with the operational
notion `engineAccepts` computed on the encoded policy. -/

/-- Access modes mediated by the isolation engine. -/
inductive Mode where
  | read : Mode
  | write : Mode
  deriving DecidableEq, Repr

/-- A capability grants `mode` on every resource at or below the path `root`. -/
structure Capability where
  root : List String
  mode : Mode
  deriving DecidableEq, Repr

/-- An access request: a resource path together with the mode of access. -/
structure Request where
  path : List String
  mode : Mode
  deriving DecidableEq, Repr

/-- A policy is a list of capabilities. -/
abbrev Policy := List Capability

/-- The declarative (model-level) notion of being in scope: some capability of
the policy grants the requested mode on a prefix of the requested path. -/

theorem permits_encodeFrom_elim (p : Policy) (path : List String) (m : Mode) (t : Trie)
    (h : Trie.permits path m (encodeFrom t p) = true) :
    Trie.permits path m t = true ∨ ∃ c ∈ p, c.mode = m ∧ c.root <+: path := by
  induction p generalizing t with
  | nil => exact Or.inl (by simpa [encodeFrom] using h)
  | cons c p ih =>
      rcases ih _ (by simpa [encodeFrom] using h) with h1 | ⟨c', hc', hmode, hpre⟩
      · rcases Trie.permits_grant_elim c.root c.mode path m t h1 with h2 | ⟨hm, hp⟩
        · exact Or.inl h2
        · exact Or.inr ⟨c, List.mem_cons_self, hm.symm, hp⟩
      · exact Or.inr ⟨c', List.mem_cons_of_mem c hc', hmode, hpre⟩

/-! ## Main results -/

/-- **Completeness of the in-scope encoding.**  Every request that is in scope
of the policy, according to the declarative model, is accepted by the isolation
engine running on the encoded policy. -/
