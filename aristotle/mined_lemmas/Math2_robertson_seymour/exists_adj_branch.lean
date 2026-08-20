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

theorem exists_adj_branch {c d : Comp} (hcd : c.le d) {x x' : ℕ}
    (hx : x < c.size) (hx' : x' < c.size) (hadj : c.Adj x x') :
    ∃ y y', brLo c d x ≤ y ∧ y ≤ brHi c d x ∧ brLo c d x' ≤ y' ∧ y' ≤ brHi c d x' ∧
      d.Adj y y' := by
  cases c with
  | path m =>
    simp only [Comp.Adj] at hadj
    simp only [Comp.size] at hx hx'
    cases d with
    | path n =>
      exact ⟨x, x', le_rfl, le_rfl, le_rfl, le_rfl, by simpa [Comp.Adj, brLo, brHi] using hadj⟩
    | cycle n =>
      simp only [Comp.le] at hcd
      refine ⟨x, x', le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
      simp only [Comp.Adj]
      rcases hadj with h | h
      · left; rw [← h]; exact Nat.mod_eq_of_lt (by omega)
      · right; rw [← h]; exact Nat.mod_eq_of_lt (by omega)
  | cycle m =>
    cases d with
    | path n => exact absurd hcd (by simp [Comp.le])
    | cycle n =>
      simp only [Comp.le] at hcd
      simp only [Comp.size] at hx hx'
      simp only [Comp.Adj] at hadj
      have main : ∀ z z' : ℕ, z < m + 3 → z' < m + 3 → (z + 1) % (m + 3) = z' →
          ∃ y y', brLo (.cycle m) (.cycle n) z ≤ y ∧ y ≤ brHi (.cycle m) (.cycle n) z ∧
            brLo (.cycle m) (.cycle n) z' ≤ y' ∧ y' ≤ brHi (.cycle m) (.cycle n) z' ∧
            Comp.Adj (.cycle n) y y' := by
        intro z z' hz hz' hmod
        rcases Comp.cycle_succ_mod hz hmod with hcase | ⟨hz2, hz'2⟩
        · refine ⟨(n - m) + z, (n - m) + z', ?_, ?_, ?_, ?_, ?_⟩
          · simp only [brLo]; split <;> omega
          · simp only [brHi]; split <;> omega
          · simp only [brLo]; split <;> omega
          · simp only [brHi]; split <;> omega
          · simp only [Comp.Adj]
            left
            have : (n - m) + z + 1 = (n - m) + z' := by omega
            rw [this]
            exact Nat.mod_eq_of_lt (by omega)
        · subst hz2; subst hz'2
          refine ⟨n + 2, 0, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [brLo]; split <;> omega
          · simp only [brHi]; split <;> omega
          · simp [brLo]
          · simp [brHi]
          · simp only [Comp.Adj]
            left
            have : n + 2 + 1 = n + 3 := by omega
            rw [this, Nat.mod_self]
      rcases hadj with h | h
      · exact main x x' hx hx' h
      · obtain ⟨y', y, h1, h2, h3, h4, h5⟩ := main x' x hx' hx h
        exact ⟨y, y', h3, h4, h1, h2, Comp.adj_symm _ h5⟩

/-! ## Domination of component lists gives a minor -/

