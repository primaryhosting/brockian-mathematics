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

