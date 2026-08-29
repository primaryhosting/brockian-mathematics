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

theorem Trie.permits_grant_elim (root : List String) (m' : Mode) (path : List String)
    (m : Mode) (t : Trie) (h : Trie.permits path m (Trie.grant root m' t) = true) :
    Trie.permits path m t = true ∨ (m = m' ∧ root <+: path) := by
  induction root generalizing t path with
  | nil =>
      cases t with
      | node g ch =>
          by_cases hm : m = m'
          · exact Or.inr ⟨hm, List.nil_prefix⟩
          · cases path with
            | nil =>
                simp only [Trie.grant_nil, Trie.permits_nil, if_neg hm] at h
                exact Or.inl (by simpa using h)
            | cons s rest =>
                simp only [Trie.grant_nil, Trie.permits_cons, if_neg hm] at h
                exact Or.inl (by simpa using h)
  | cons s0 root ih =>
      cases t with
      | node g ch =>
          cases path with
          | nil =>
              simp only [Trie.grant_cons, Trie.permits_nil] at h
              exact Or.inl (by simpa using h)
          | cons s rest =>
              simp only [Trie.grant_cons, Trie.permits_cons] at h
              rcases Bool.or_eq_true_iff.1 h with hg | hc
              · exact Or.inl (by simp [hg])
              · by_cases hs : s = s0
                · subst hs
                  simp only [Trie.permitsOpt] at hc
                  rcases ih rest ((ch s).getD Trie.empty) hc with h1 | ⟨hm, hp⟩
                  · left
                    have : Trie.permitsOpt rest m (ch s) = true := by simpa using h1
                    simp [this]
                  · obtain ⟨ext, hext⟩ := hp
                    exact Or.inr ⟨hm, ⟨ext, by simp [hext]⟩⟩
                · simp only [if_neg hs] at hc
                  exact Or.inl (by simp [hc])

/-! ## Lemmas about the encoding of a whole policy -/

/-- Encoding further capabilities never revokes an existing permission. -/
