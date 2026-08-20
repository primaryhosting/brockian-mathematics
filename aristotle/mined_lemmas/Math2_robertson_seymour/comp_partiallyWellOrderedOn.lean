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

theorem comp_partiallyWellOrderedOn :
    (Set.univ : Set Comp).PartiallyWellOrderedOn Comp.le := by
  classical
  intro f
  set g : ℕ → Comp := fun n => (f n).1 with hg
  set T : Set ℕ := {n | ∃ k, g n = Comp.cycle k} with hT
  have hsplit : T.Infinite ∨ (Tᶜ).Infinite := by
    rcases Set.finite_or_infinite T with hfin | hinf
    · refine Or.inr ?_
      rcases Set.finite_or_infinite (Tᶜ) with hfin' | hinf'
      · exact absurd (by simpa [Set.union_compl_self] using hfin.union hfin')
          (Set.infinite_univ (α := ℕ))
      · exact hinf'
    · exact Or.inl hinf
  have key : ∃ m n, m < n ∧ Comp.le (g m) (g n) := by
    rcases hsplit with hinf | hinf
    · obtain ⟨i, hi, j, hj, hij, hle⟩ := exists_le_on_infinite (fun n => (g n).param) hinf
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := hj
      refine ⟨i, j, hij, ?_⟩
      rw [ha, hb]
      rw [ha, hb] at hle
      simpa [Comp.le, Comp.param] using hle
    · obtain ⟨i, hi, j, hj, hij, hle⟩ := exists_le_on_infinite (fun n => (g n).param) hinf
      have ha : ∃ a, g i = Comp.path a := by
        cases hgi : g i with
        | path a => exact ⟨a, rfl⟩
        | cycle a => exact absurd ⟨a, hgi⟩ hi
      have hb : ∃ b, g j = Comp.path b := by
        cases hgj : g j with
        | path b => exact ⟨b, rfl⟩
        | cycle b => exact absurd ⟨b, hgj⟩ hj
      obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      refine ⟨i, j, hij, ?_⟩
      rw [ha, hb]
      rw [ha, hb] at hle
      simpa [Comp.le, Comp.param] using hle
  exact key

/-! ## Forests of paths and cycles -/

/-- The component of index `i` of the list `l` (with a junk value out of range). -/
