import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
In Hückel molecular orbital theory the π-energies of an annulene `C_n H_n` are `α + β λ`,
where `λ` runs over the eigenvalues of the adjacency matrix of the cycle graph `C n`.
This file proves that this spectrum is exactly `{2 cos (2 π k / n) : k = 0, …, n-1}`.

The proof diagonalizes the (circulant) adjacency matrix by the Vandermonde/Fourier matrix
built from the `n`-th roots of unity.
-/

open scoped BigOperators Real

namespace Chem

open SimpleGraph Matrix Complex

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with entries in `ℂ`:
the `(i, j)` entry is `1` when `i` and `j` are adjacent in `C n`, and `0` otherwise. -/

lemma sum_adj_eq (hn : 3 ≤ n) (i : Fin n) (f : Fin n → ℂ) :
    ∑ j, (if (SimpleGraph.cycleGraph n).Adj i j then (1 : ℂ) else 0) * f j
      = f (i - 1) + f (i + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : ∀ j : Fin (m + 3), (if (cycleGraph (m + 3)).Adj i j then (1 : ℂ) else 0) * f j
      = if (cycleGraph (m + 3)).Adj i j then f j else 0 := by
    intro j; split <;> simp
  simp only [h1]
  rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair]
  intro h
  rw [sub_eq_add_neg] at h
  have h2 : (-1 : Fin (m + 3)) = 1 := add_left_cancel h
  have h3 := congrArg Fin.val h2
  simp [Fin.neg_def] at h3

/-- The vector `j ↦ ω ^ (k j)` is an eigenvector of the Hückel matrix of `C n`
with eigenvalue `2 cos (2 π k / n)`. -/
