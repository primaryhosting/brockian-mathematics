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

theorem permits_encodeFrom_of_mem (p : Policy) (t : Trie) (c : Capability) (hc : c ∈ p)
    (path : List String) (m : Mode) (hm : c.mode = m) (hp : c.root <+: path) :
    Trie.permits path m (encodeFrom t p) = true := by
  induction p generalizing t with
  | nil => exact absurd hc List.not_mem_nil
  | cons c' p ih =>
      rcases List.mem_cons.1 hc with rfl | hmem
      · obtain ⟨ext, hext⟩ := hp
        refine permits_encodeFrom_mono p path m _ ?_
        subst hm
        rw [← hext]
        exact Trie.permits_grant_append c.root ext c.mode t
      · exact ih _ hmem

/-- Every permission granted by an encoded policy comes either from the initial
trie or from one of the capabilities of the policy. -/
