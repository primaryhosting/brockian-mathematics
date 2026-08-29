import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Finset

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances `d(u,v)` over all
unordered pairs `{u, v}` of vertices (the diagonal pairs contribute `0`). -/

theorem pathGraph_exists_walk {n : ℕ} : ∀ (d : ℕ) (i j : Fin n), ((i : ℤ) - (j : ℤ)).natAbs = d →
    ∃ p : (pathGraph n).Walk i j, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have hij : i = j := Fin.ext (by omega)
    subst hij
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
    intro i j h
    rcases (by omega : (j : ℕ) = (i : ℕ) + (d + 1) ∨ (i : ℕ) = (j : ℕ) + (d + 1)) with hc | hc
    · have hlt : (i : ℕ) + 1 < n := by omega
      set k : Fin n := ⟨(i : ℕ) + 1, hlt⟩ with hk
      have hadj : (pathGraph n).Adj i k := by
        rw [SimpleGraph.pathGraph_adj]; left; simp [hk]
      obtain ⟨p, hp⟩ := ih k j (by simp [hk]; omega)
      exact ⟨SimpleGraph.Walk.cons hadj p, by simp [hp]⟩
    · have hlt : (i : ℕ) - 1 < n := by omega
      set k : Fin n := ⟨(i : ℕ) - 1, hlt⟩ with hk
      have hadj : (pathGraph n).Adj i k := by
        rw [SimpleGraph.pathGraph_adj]; right; simp [hk]; omega
      obtain ⟨p, hp⟩ := ih k j (by simp [hk]; omega)
      exact ⟨SimpleGraph.Walk.cons hadj p, by simp [hp]⟩

/-- Every walk in the path graph is at least as long as the difference of its endpoints. -/
