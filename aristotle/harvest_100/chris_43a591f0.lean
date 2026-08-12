import Mathlib
import RequestProject.Main

/-!
# In-scope encoding soundness, Mathlib (`Finset`) formulation

`RequestProject/Main.lean` states and proves the target theorem
`PCA.Isolation.in_scope_encoding_sound` for policies given as lists.  (That file must
begin with the prescribed header docstring, which Lean does not allow to precede an
`import`, so it is written against Lean's core `List`/`String` API only.)

This companion file works in full Mathlib and restates the same soundness /
completeness result for policies given as `Finset`s of paths, deriving it from the
encoding lemmas of `RequestProject.Main`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-- The isolation policy with policy sets given as `Finset`s of paths. -/
structure FinScope where
  /-- Roots of the sub-trees the app may access. -/
  allowed : Finset Path
  /-- Roots of the sub-trees explicitly denied to the app. -/
  denied : Finset Path

/-- Abstract scope membership for a `Finset`-valued policy. -/
def FinInScope (s : FinScope) (p : Path) : Prop :=
  (∃ r ∈ s.allowed, r <+: p) ∧ ∀ d ∈ s.denied, ¬ d <+: p

/-- The encoding of a finite set of paths. -/
def encFinset (S : Finset Path) : Finset EncPath := S.image encPath

/-- The in-scope test performed by the engine on encoded data, `Finset` version. -/
def FinInScopeEnc (A D : Finset EncPath) (q : EncPath) : Prop :=
  (∃ r ∈ A, r <+: q) ∧ ∀ d ∈ D, ¬ d <+: q

theorem mem_encFinset_iff {S : Finset Path} {q : EncPath} :
    q ∈ encFinset S ↔ ∃ p ∈ S, encPath p = q := by
  simp [encFinset]

/-- **In-scope encoding is sound (and complete)**, for `Finset`-valued policies. -/
theorem fin_in_scope_encoding_sound (s : FinScope) (p : Path) :
    FinInScopeEnc (encFinset s.allowed) (encFinset s.denied) (encPath p) ↔ FinInScope s p := by
  constructor
  · rintro ⟨⟨q, hq, hqp⟩, hd⟩
    obtain ⟨r, hr, rfl⟩ := mem_encFinset_iff.mp hq
    refine ⟨⟨r, hr, (encPath_prefix_iff r p).mp hqp⟩, ?_⟩
    intro d hdmem hdp
    exact hd (encPath d) (Finset.mem_image_of_mem encPath hdmem)
      ((encPath_prefix_iff d p).mpr hdp)
  · rintro ⟨⟨r, hr, hrp⟩, hd⟩
    refine ⟨⟨encPath r, Finset.mem_image_of_mem encPath hr,
      (encPath_prefix_iff r p).mpr hrp⟩, ?_⟩
    intro q hq hqp
    obtain ⟨d, hdmem, rfl⟩ := mem_encFinset_iff.mp hq
    exact hd d hdmem ((encPath_prefix_iff d p).mp hqp)

/-- The `Finset` formulation agrees with the list formulation of the target theorem:
turning the policy `Finset`s into (deduplicated) lists changes nothing. -/
theorem fin_in_scope_iff_inScope (s : FinScope) (p : Path) :
    FinInScope s p ↔ InScope ⟨s.allowed.toList, s.denied.toList⟩ p := by
  simp [FinInScope, InScope]

/-! ### Sanity checks: the model is not vacuous -/

example : InScope ⟨[["home", "app"]], [["home", "app", "secrets"]]⟩ ["home", "app", "data"] := by
  refine ⟨⟨["home", "app"], List.mem_singleton.mpr rfl, ⟨["data"], rfl⟩⟩, ?_⟩
  intro d hd
  rw [List.mem_singleton] at hd
  subst hd
  rintro ⟨t, ht⟩
  simp at ht

example :
    ¬ InScope ⟨[["home", "app"]], [["home", "app", "secrets"]]⟩ ["home", "app", "secrets", "k"] := by
  rintro ⟨-, hd⟩
  exact hd ["home", "app", "secrets"] (List.mem_singleton.mpr rfl) ⟨["k"], rfl⟩

example : ¬ InScope ⟨[["home", "app"]], [["home", "app", "secrets"]]⟩ ["etc"] := by
  rintro ⟨⟨r, hr, t, ht⟩, -⟩
  rw [List.mem_singleton] at hr
  subst hr
  simp at ht

end PCA.Isolation

/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-! ## The isolation model

A *resource* handled by the isolation engine is identified by a hierarchical path,
modelled as a list of path segments (`List String`).

A *scope* is the policy carried by a proof-carrying app: a list of allowed roots
together with a list of denied sub-trees. A resource is *in scope* when some
allowed root is a prefix of it and no denied path is a prefix of it.

The engine does not manipulate `String` segments directly: it works on an
*encoded* form, where every segment is expanded into its list of characters.
The statement `in_scope_encoding_sound` says that running the in-scope test on the
encoded representation gives exactly the same verdict as the abstract scope
membership: the encoding neither rejects resources that are in scope
(completeness) nor admits resources that are out of scope (soundness).
-/

/-- A resource path: a list of path segments. -/
abbrev Path : Type := List String

/-- The encoded form of a path: each segment expanded to its characters. -/
abbrev EncPath : Type := List (List Char)

/-- The isolation policy: allowed roots and denied sub-trees. -/
structure Scope where
  /-- Roots of the sub-trees the app may access. -/
  allowed : List Path
  /-- Roots of the sub-trees explicitly denied to the app. -/
  denied : List Path

/-- A path is in scope when it lies under an allowed root and under no denied root. -/
def InScope (s : Scope) (p : Path) : Prop :=
  (∃ r ∈ s.allowed, r <+: p) ∧ ∀ d ∈ s.denied, ¬ d <+: p

/-- The encoding of a path used by the isolation engine. -/
def encPath (p : Path) : EncPath := p.map String.toList

/-- The encoding of a list of paths. -/
def encPaths (S : List Path) : List EncPath := S.map encPath

/-- The in-scope test performed by the engine on encoded data. -/
def InScopeEnc (A D : List EncPath) (q : EncPath) : Prop :=
  (∃ r ∈ A, r <+: q) ∧ ∀ d ∈ D, ¬ d <+: q

/-! ## Basic properties of the encoding -/

/-- Segment encoding is injective. -/
theorem toList_injective : Function.Injective String.toList :=
  fun _ _ h => String.ext h

/-- Mapping an injective function over lists both preserves and reflects the prefix
relation.  The easy direction is `List.IsPrefix.map`; the reflecting direction is
proved here by induction on the prefix candidate. -/
theorem map_prefix_map_iff {α β : Type} {f : α → β} (hf : Function.Injective f)
    (l m : List α) : l.map f <+: m.map f ↔ l <+: m := by
  constructor
  · intro h
    induction l generalizing m with
    | nil => simp
    | cons a l ih =>
      cases m with
      | nil => simp at h
      | cons b m =>
        simp only [List.map_cons, List.cons_prefix_cons] at h ⊢
        exact ⟨hf h.1, ih _ h.2⟩
  · intro h
    exact h.map f

/-- Path encoding is injective: distinct resources have distinct encodings, so the
encoding cannot be spoofed. -/
theorem encPath_injective : Function.Injective encPath := by
  intro p q h
  induction p generalizing q with
  | nil => cases q with
    | nil => rfl
    | cons b q => simp [encPath] at h
  | cons a p ih =>
    cases q with
    | nil => simp [encPath] at h
    | cons b q =>
      simp only [encPath, List.map_cons, List.cons.injEq] at h
      rw [toList_injective h.1, ih h.2]

/-- The encoding preserves and reflects the "lies under" (prefix) relation. -/
theorem encPath_prefix_iff (r p : Path) : encPath r <+: encPath p ↔ r <+: p :=
  map_prefix_map_iff toList_injective r p

/-- Membership in an encoded list of paths comes exactly from membership in the
original list. -/
theorem mem_encPaths_iff {S : List Path} {q : EncPath} :
    q ∈ encPaths S ↔ ∃ p ∈ S, encPath p = q := by
  simp [encPaths]

/-- If a path belongs to a list of paths, its encoding belongs to the encoded list. -/
theorem encPath_mem_encPaths {S : List Path} {p : Path} (hp : p ∈ S) :
    encPath p ∈ encPaths S :=
  mem_encPaths_iff.mpr ⟨p, hp, rfl⟩

/-! ## Soundness and completeness of the encoding -/

/-- **In-scope encoding is sound (and complete).**
Running the isolation engine's in-scope test on the encoded policy and the encoded
resource path yields exactly the same verdict as abstract scope membership. -/
theorem in_scope_encoding_sound (s : Scope) (p : Path) :
    InScopeEnc (encPaths s.allowed) (encPaths s.denied) (encPath p) ↔ InScope s p := by
  constructor
  · rintro ⟨⟨q, hq, hqp⟩, hd⟩
    obtain ⟨r, hr, rfl⟩ := mem_encPaths_iff.mp hq
    refine ⟨⟨r, hr, (encPath_prefix_iff r p).mp hqp⟩, ?_⟩
    intro d hdmem hdp
    exact hd (encPath d) (encPath_mem_encPaths hdmem) ((encPath_prefix_iff d p).mpr hdp)
  · rintro ⟨⟨r, hr, hrp⟩, hd⟩
    refine ⟨⟨encPath r, encPath_mem_encPaths hr, (encPath_prefix_iff r p).mpr hrp⟩, ?_⟩
    intro q hq hqp
    obtain ⟨d, hdmem, rfl⟩ := mem_encPaths_iff.mp hq
    exact hd d hdmem ((encPath_prefix_iff d p).mp hqp)

end PCA.Isolation

