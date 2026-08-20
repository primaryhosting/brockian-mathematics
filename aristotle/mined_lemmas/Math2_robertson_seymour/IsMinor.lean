import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` to be the first command of a file, so the
module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the import is a parse error).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

universe u v w

open SimpleGraph

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`: there is a family of pairwise disjoint,
nonempty, connected *branch sets* `B w ⊆ V(G)`, indexed by the vertices `w` of `H`, such
that adjacent vertices of `H` have an edge of `G` between their branch sets. -/

theorem IsMinor.congr {V : Type u} {W : Type v} {V' : Type w} {W' : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {H' : SimpleGraph W'} {G' : SimpleGraph V'}
    (eH : H ≃g H') (eG : G' ≃g G) (h : IsMinor H' G') : IsMinor H G :=
  (Iso.embeds eH).isMinor.trans (h.trans (Iso.embeds eG).isMinor)

/-! ## Components: paths and cycles -/

/-- A connected graph of maximum degree at most two: either a path with `n` vertices or a
cycle with `n + 3` vertices. -/
inductive Comp where
  | path (n : ℕ) : Comp
  | cycle (n : ℕ) : Comp
  deriving DecidableEq

/-- The number of vertices of a component. -/
