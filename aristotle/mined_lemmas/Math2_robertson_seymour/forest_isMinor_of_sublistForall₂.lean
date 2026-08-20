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

theorem forest_isMinor_of_sublistForall₂ {l₁ l₂ : List Comp}
    (h : List.SublistForall₂ Comp.le l₁ l₂) : IsMinor (Forest l₁) (Forest l₂) := by
  obtain ⟨σ, hmono, hσ⟩ :=
    exists_strictMono_of_sublistForall₂ (d := Comp.path 0) h
  have hlen : ∀ u : ForestVerts l₁, σ u.1.1 < l₂.length := fun u => (hσ u.1.1 u.2.1).1
  have hle : ∀ u : ForestVerts l₁, (compAt l₁ u.1.1).le (compAt l₂ (σ u.1.1)) :=
    fun u => (hσ u.1.1 u.2.1).2
  refine ⟨fun u => {q : ForestVerts l₂ | q.1.1 = σ u.1.1 ∧
      brLo (compAt l₁ u.1.1) (compAt l₂ (σ u.1.1)) u.1.2 ≤ q.1.2 ∧
      q.1.2 ≤ brHi (compAt l₁ u.1.1) (compAt l₂ (σ u.1.1)) u.1.2}, ?_, ?_, ?_, ?_⟩
  · intro u
    refine ⟨⟨(σ u.1.1, brLo (compAt l₁ u.1.1) (compAt l₂ (σ u.1.1)) u.1.2), hlen u, ?_⟩,
      rfl, le_rfl, brLo_le_brHi _ _ _⟩
    exact lt_of_le_of_lt (brLo_le_brHi _ _ _) (brHi_lt_size (hle u) u.2.2)
  · intro u
    exact connected_interval (hlen u) (brLo_le_brHi _ _ _) (brHi_lt_size (hle u) u.2.2)
  · rintro u u' hne
    rw [Set.disjoint_left]
    rintro q ⟨hq1, hq2, hq3⟩ ⟨hq1', hq2', hq3'⟩
    have hii : u.1.1 = u'.1.1 := hmono.injective (hq1 ▸ hq1')
    have hxx : u.1.2 ≠ u'.1.2 := by
      intro hcon
      exact hne (Subtype.ext (Prod.ext hii hcon))
    rcases Nat.lt_or_ge u.1.2 u'.1.2 with hlt | hge
    · have := brHi_lt_brLo (c := compAt l₁ u.1.1) (d := compAt l₂ (σ u.1.1)) (hle u) hlt
      rw [← hii] at hq2'
      omega
    · have hlt' : u'.1.2 < u.1.2 := by omega
      have := brHi_lt_brLo (c := compAt l₁ u'.1.1) (d := compAt l₂ (σ u'.1.1)) (hle u') hlt'
      rw [← hii] at this hq3'
      omega
  · rintro ⟨⟨i, x⟩, hu1, hu2⟩ ⟨⟨i', x'⟩, hu1', hu2'⟩ ⟨hidx, hadj⟩
    obtain rfl : i = i' := hidx
    obtain ⟨y, y', hy1, hy2, hy3, hy4, hyadj⟩ :=
      exists_adj_branch (c := compAt l₁ i) (hσ i hu1).2 hu2 hu2' hadj
    exact ⟨⟨(σ i, y), (hσ i hu1).1, lt_of_le_of_lt hy2 (brHi_lt_size (hσ i hu1).2 hu2)⟩,
      ⟨rfl, hy1, hy2⟩,
      ⟨(σ i, y'), (hσ i hu1).1, lt_of_le_of_lt hy4 (brHi_lt_size (hσ i hu1).2 hu2')⟩,
      ⟨rfl, hy3, hy4⟩, ⟨rfl, hyadj⟩⟩

/-! Sanity checks: a small cycle is a minor of a larger one (obtained by contracting a
segment), and a path is a minor of a long enough cycle. -/

example : IsMinor (Forest [Comp.cycle 0]) (Forest [Comp.cycle 5]) :=
  forest_isMinor_of_sublistForall₂
    (List.SublistForall₂.cons (by simp [Comp.le]) List.SublistForall₂.nil)

example : IsMinor (Forest [Comp.path 2]) (Forest [Comp.cycle 0]) :=
  forest_isMinor_of_sublistForall₂
    (List.SublistForall₂.cons (by simp [Comp.le]) List.SublistForall₂.nil)

/-! ## Well-quasi-ordering -/

/-- **Robertson–Seymour, well-quasi-ordering by minors, for graphs of maximum degree at
most two.**

For any sequence `G` of graphs, each of which is a disjoint union of finite paths and
cycles, there are indices `i < j` such that `G i` is a minor of `G j`.  Together with
`Math2.isMinor_refl` and `Math2.IsMinor.trans` this says exactly that the minor relation is
a well-quasi-order on this class of graphs: it is a quasi-order with no infinite antichain
and no infinite strictly descending sequence.

The proof follows the Robertson–Seymour scheme in the case where the graph minor theorem
reduces to Higman's lemma: such a graph is encoded by the list of its components, a
component `c` is a minor of a component `d` exactly when `Comp.le c d`, which is a
well-quasi-order on components, an entrywise domination of one list of components by a
sublist of another produces a minor (using contractions inside cycles), and Higman's lemma
supplies such a domination between two terms of any infinite sequence of lists. -/
