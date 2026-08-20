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

theorem exists_le_on_infinite (g : ℕ → ℕ) {T : Set ℕ} (hT : T.Infinite) :
    ∃ i ∈ T, ∃ j ∈ T, i < j ∧ g i ≤ g j := by
  classical
  obtain ⟨i, hiT⟩ := hT.nonempty
  set A : Set ℕ := g '' T with hA
  have hAne : (g i) ∈ A := ⟨i, hiT, rfl⟩
  obtain ⟨i₀, hi₀T, hi₀⟩ : ∃ i₀ ∈ T, g i₀ = sInf A := by
    have : sInf A ∈ A := Nat.sInf_mem ⟨g i, hAne⟩
    obtain ⟨i₀, hi₀T, hi₀⟩ := this
    exact ⟨i₀, hi₀T, hi₀⟩
  obtain ⟨j, hjT, hj⟩ := hT.exists_gt i₀
  refine ⟨i₀, hi₀T, j, hjT, hj, ?_⟩
  rw [hi₀]
  exact Nat.sInf_le ⟨j, hjT, rfl⟩

/-- Components are well-quasi-ordered by `Comp.le`. -/
