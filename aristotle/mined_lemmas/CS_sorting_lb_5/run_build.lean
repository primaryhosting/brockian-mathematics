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

theorem run_build (ps : List (Fin 5 × Fin 5)) (S : Finset Perm5) (σ : Perm5) (hσ : σ ∈ S) :
    (build ps S).run σ ∈ S ∧
      ∀ p ∈ ps, (((build ps S).run σ) p.1 < ((build ps S).run σ) p.2 ↔ σ p.1 < σ p.2) := by
  induction ps generalizing S with
  | nil =>
      refine ⟨?_, by simp⟩
      have hne : S.toList ≠ [] := by
        intro hnil
        have : σ ∈ S.toList := by simpa using hσ
        simp [hnil] at this
      have hmem : S.toList.headI ∈ S.toList := by
        cases hl : S.toList with
        | nil => exact absurd hl hne
        | cons a t => simp
      simpa [build, run] using hmem
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      by_cases h : σ i < σ j
      · have hmem : σ ∈ S.filter (fun τ => τ i < τ j) := Finset.mem_filter.mpr ⟨hσ, h⟩
        obtain ⟨h1, h2⟩ := ih _ hmem
        simp only [build, run, if_pos h]
        rw [Finset.mem_filter] at h1
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨fun _ => h, fun _ => h1.2⟩
        · exact h2 q hq
      · have h' : σ j ≤ σ i := not_lt.mp h
        have hmem : σ ∈ S.filter (fun τ => τ j ≤ τ i) := Finset.mem_filter.mpr ⟨hσ, h'⟩
        obtain ⟨h1, h2⟩ := ih _ hmem
        simp only [build, run, if_neg h]
        rw [Finset.mem_filter] at h1
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨fun hh => absurd hh (not_lt.mpr h1.2), fun hh => absurd hh h⟩
        · exact h2 q hq

/-- All ordered pairs of positions. -/
