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
