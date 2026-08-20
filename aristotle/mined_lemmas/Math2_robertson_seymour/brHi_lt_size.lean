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

theorem brHi_lt_size {c d : Comp} (hcd : c.le d) {x : ℕ} (hx : x < c.size) :
    brHi c d x < d.size := by
  cases c with
  | path m =>
    cases d with
    | path n => simp only [brHi]; simp only [Comp.le] at hcd; simp only [Comp.size] at *; omega
    | cycle n => simp only [brHi]; simp only [Comp.le] at hcd; simp only [Comp.size] at *; omega
  | cycle m =>
    cases d with
    | path n => exact absurd hcd (by simp [Comp.le])
    | cycle n =>
      simp only [Comp.le] at hcd
      simp only [Comp.size] at *
      simp only [brHi]
      split <;> omega

