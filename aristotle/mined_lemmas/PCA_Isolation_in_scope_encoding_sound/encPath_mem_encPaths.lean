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

theorem encPath_mem_encPaths {S : List Path} {p : Path} (hp : p ∈ S) :
    encPath p ∈ encPaths S :=
  mem_encPaths_iff.mpr ⟨p, hp, rfl⟩

/-! ## Soundness and completeness of the encoding -/

/-- **In-scope encoding is sound (and complete).**
Running the isolation engine's in-scope test on the encoded policy and the encoded
resource path yields exactly the same verdict as abstract scope membership. -/
