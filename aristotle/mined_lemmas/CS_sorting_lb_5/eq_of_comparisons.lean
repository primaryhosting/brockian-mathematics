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

theorem eq_of_comparisons {σ τ : Perm5} (h : ∀ i j, (τ i < τ j ↔ σ i < σ j)) : τ = σ := by
  have hg : StrictMono (fun a => τ (σ.symm a)) := by
    intro a b hab
    simp only
    rw [h]
    simpa using hab
  have hgs : StrictMono (fun a => σ (τ.symm a)) := by
    intro a b hab
    by_contra hc
    push_neg at hc
    rcases lt_or_eq_of_le hc with hlt | heq
    · have := (h (τ.symm b) (τ.symm a)).mpr hlt
      simp at this
      omega
    · have h1 : τ.symm b = τ.symm a := by simpa using congrArg σ.symm heq
      have : b = a := by simpa using congrArg τ h1
      omega
  ext i
  have h1 : σ i ≤ τ i := by simpa using hg.le_apply (x := σ i)
  have h2 : τ i ≤ σ i := by simpa using hgs.le_apply (x := τ i)
  omega

/-- There **is** a correct comparison tree for five elements, so the hypothesis of the
lower bound below is satisfiable and the statement is not vacuous. -/
