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
