/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 5

A comparison sort on `5` elements is modelled as a binary comparison decision tree:
each internal node asks a comparison `x i < x j` between two of the five input
positions, and each leaf outputs the permutation describing the sorted order.

The input is encoded by a permutation `σ : Equiv.Perm (Fin 5)` giving the rank
`σ i` of the element in position `i`; the comparison at a node `(i, j)` is
answered by `σ i < σ j`.  Correctness means the tree outputs `σ` on input `σ`.

The main result `CS.sorting_lb_5` says that the depth (worst-case number of
comparisons) of any correct tree is at least `⌈log₂ (5!)⌉ = 7`.
-/

namespace CS

/-- Rankings of the five inputs. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A binary comparison decision tree on five elements:
`node i j lo hi` compares the elements at positions `i` and `j`, continuing in
`lo` if the `i`-th is smaller and in `hi` otherwise; `leaf o` outputs `o`. -/
inductive CompTree where
  | leaf : Perm5 → CompTree
  | node : Fin 5 → Fin 5 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The depth of a comparison tree: the worst-case number of comparisons. -/

noncomputable def build : List (Fin 5 × Fin 5) → Finset Perm5 → CompTree
  | [], S => .leaf S.toList.headI
  | (i, j) :: ps, S =>
      .node i j (build ps (S.filter (fun τ => τ i < τ j)))
                (build ps (S.filter (fun τ => τ j ≤ τ i)))

/-- Running `build ps S` on an input from `S` returns an element of `S` that answers
all the comparisons in `ps` exactly as the input does. -/
