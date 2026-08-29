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
def InScope (p : Policy) (r : Request) : Prop :=
  ∃ c ∈ p, c.mode = r.mode ∧ c.root <+: r.path

/-! ## The operational encoding -/

/-- A prefix tree over path components.  Each node records which modes are
granted at (and hence below) that node, together with its children. -/
inductive Trie : Type where
  | node (grants : Mode → Bool) (child : String → Option Trie) : Trie

namespace Trie

/-- The trie granting nothing. -/
def empty : Trie := .node (fun _ => false) (fun _ => none)

/-- `grant root m t` adds a grant of mode `m` on the whole subtree `root` to
the trie `t`. -/
def grant : List String → Mode → Trie → Trie
  | [], m, .node g ch => .node (fun m' => if m' = m then true else g m') ch
  | s :: rest, m, .node g ch =>
      .node g (fun s' => if s' = s then some (grant rest m ((ch s).getD empty)) else ch s')

/-- `permits path m t` is the engine's access check: walk `path` from the root
of `t`, accepting as soon as a visited node grants the mode `m`. -/
def permits : List String → Mode → Trie → Bool
  | [], m, .node g _ => g m
  | s :: rest, m, .node g ch =>
      g m || (match ch s with
              | some t => permits rest m t
              | none => false)

/-- `permits` lifted to an optional subtree; a missing subtree permits nothing. -/
def permitsOpt (path : List String) (m : Mode) : Option Trie → Bool
  | none => false
  | some t => permits path m t

@[simp] theorem permits_nil (g : Mode → Bool) (ch : String → Option Trie) (m : Mode) :
    permits [] m (.node g ch) = g m := rfl

@[simp] theorem permits_cons (s : String) (rest : List String) (m : Mode)
    (g : Mode → Bool) (ch : String → Option Trie) :
    permits (s :: rest) m (.node g ch) = (g m || permitsOpt rest m (ch s)) := by
  cases h : ch s <;> simp [permits, permitsOpt, h]

@[simp] theorem grant_nil (m : Mode) (g : Mode → Bool) (ch : String → Option Trie) :
    grant [] m (.node g ch) = .node (fun m' => if m' = m then true else g m') ch := rfl

@[simp] theorem grant_cons (s : String) (rest : List String) (m : Mode)
    (g : Mode → Bool) (ch : String → Option Trie) :
    grant (s :: rest) m (.node g ch) =
      .node g (fun s' => if s' = s then some (grant rest m ((ch s).getD empty)) else ch s') :=
  rfl

@[simp] theorem permits_empty (path : List String) (m : Mode) :
    permits path m empty = false := by
  cases path with
  | nil => rfl
  | cons s rest => simp [empty, permitsOpt]

@[simp] theorem permits_getD (path : List String) (m : Mode) (o : Option Trie) :
    permits path m (o.getD empty) = permitsOpt path m o := by
  cases o <;> simp [permitsOpt]

end Trie

/-- Encoding of a policy into a prefix tree, starting from a given trie. -/
def encodeFrom (t : Trie) : Policy → Trie
  | [] => t
  | c :: p => encodeFrom (Trie.grant c.root c.mode t) p

/-- The encoding of a policy: insert every capability into the empty trie. -/
def encode (p : Policy) : Trie := encodeFrom Trie.empty p

/-- The engine's decision on the encoded policy. -/
def engineAccepts (p : Policy) (r : Request) : Bool :=
  Trie.permits r.path r.mode (encode p)

/-! ## Lemmas about a single grant -/

/-- A freshly granted subtree permits every extension of its root. -/
theorem Trie.permits_grant_append (root ext : List String) (m : Mode) (t : Trie) :
    Trie.permits (root ++ ext) m (Trie.grant root m t) = true := by
  induction root generalizing t with
  | nil =>
      cases t with
      | node g ch => cases ext <;> simp [Trie.permitsOpt]
  | cons s root ih =>
      cases t with
      | node g ch => simp [Trie.permitsOpt, ih]

/-- Granting further capabilities never revokes an existing permission. -/
theorem Trie.permits_grant_mono (path : List String) (m : Mode) (root : List String)
    (m' : Mode) (t : Trie) (h : Trie.permits path m t = true) :
    Trie.permits path m (Trie.grant root m' t) = true := by
  induction path generalizing t root with
  | nil =>
      cases t with
      | node g ch =>
          cases root with
          | nil => simp only [Trie.permits_nil] at h ⊢; simp [h]
          | cons s root => simpa using h
  | cons s rest ih =>
      cases t with
      | node g ch =>
          cases root with
          | nil =>
              simp only [Trie.permits_cons, Trie.grant_nil] at h ⊢
              rcases Bool.or_eq_true_iff.1 h with hg | hc
              · simp [hg]
              · simp [hc]
          | cons s0 root =>
              simp only [Trie.permits_cons, Trie.grant_cons] at h ⊢
              rcases Bool.or_eq_true_iff.1 h with hg | hc
              · simp [hg]
              · by_cases hs : s = s0
                · subst hs
                  have : Trie.permitsOpt rest m (ch s) = true := hc
                  simp only [Trie.permitsOpt]
                  refine Bool.or_eq_true_iff.2 (Or.inr ?_)
                  have h2 : Trie.permits rest m ((ch s).getD Trie.empty) = true := by
                    simpa using this
                  exact ih _ _ h2
                · simp only [if_neg hs]
                  exact Bool.or_eq_true_iff.2 (Or.inr hc)

/-- Every permission granted by `grant root m' t` comes either from `t` itself
or from the newly added capability. -/
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
theorem permits_encodeFrom_mono (p : Policy) (path : List String) (m : Mode) (t : Trie)
    (h : Trie.permits path m t = true) :
    Trie.permits path m (encodeFrom t p) = true := by
  induction p generalizing t with
  | nil => simpa [encodeFrom] using h
  | cons c p ih => exact ih _ (Trie.permits_grant_mono path m c.root c.mode t h)

/-- Every capability of the policy is honoured by the encoded policy. -/
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
theorem in_scope_encoding_complete (p : Policy) (r : Request) (h : InScope p r) :
    engineAccepts p r = true := by
  obtain ⟨c, hc, hmode, hpre⟩ := h
  exact permits_encodeFrom_of_mem p Trie.empty c hc r.path r.mode hmode hpre

/-- **Soundness of the in-scope encoding.**  The isolation engine accepts only
requests that are in scope of the policy. -/
theorem in_scope_encoding_sound (p : Policy) (r : Request) (h : engineAccepts p r = true) :
    InScope p r := by
  rcases permits_encodeFrom_elim p r.path r.mode Trie.empty h with h1 | ⟨c, hc, hm, hpre⟩
  · exact absurd h1 (by simp)
  · exact ⟨c, hc, hm, hpre⟩

/-- The encoded isolation engine decides exactly the declarative scope relation. -/
theorem in_scope_encoding_correct (p : Policy) (r : Request) :
    engineAccepts p r = true ↔ InScope p r :=
  ⟨in_scope_encoding_sound p r, in_scope_encoding_complete p r⟩

/-! ## Sanity checks (non-vacuity of the model) -/

/-- A sample policy: read access below `home/app`, write access below `tmp`. -/
def samplePolicy : Policy :=
  [⟨["home", "app"], Mode.read⟩, ⟨["tmp"], Mode.write⟩]

example : engineAccepts samplePolicy ⟨["home", "app", "data"], Mode.read⟩ = true := rfl

example : engineAccepts samplePolicy ⟨["home", "app", "data"], Mode.write⟩ = false := rfl

/-- The engine refuses an access outside the granted subtrees, and hence, by
soundness, such an access is genuinely out of scope. -/
example : ¬ InScope samplePolicy ⟨["home", "other"], Mode.read⟩ := by
  intro h
  have h2 := in_scope_encoding_complete _ _ h
  have hfalse : engineAccepts samplePolicy ⟨["home", "other"], Mode.read⟩ = false := rfl
  rw [hfalse] at h2
  exact Bool.noConfusion h2

end PCA.Isolation

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

