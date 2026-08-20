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

theorem brHi_lt_brLo {c d : Comp} (hcd : c.le d) {x x' : ℕ} (h : x < x') :
    brHi c d x < brLo c d x' := by
  cases c with
  | path m => cases d <;> simp only [brHi, brLo] <;> omega
  | cycle m =>
    cases d with
    | path n => exact absurd hcd (by simp [Comp.le])
    | cycle n =>
      simp only [brHi, brLo]
      split <;> split <;> omega

/-- If two positions of `c` are adjacent, then their branch sets in `d` are joined by an
edge of `d`. -/
