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
