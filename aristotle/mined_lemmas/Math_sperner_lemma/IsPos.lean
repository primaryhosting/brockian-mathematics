import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-!
## Setting

We work with the standard `m`-fold dilated `n`-dimensional simplex

  `Δ = { v : ℕ^{n+1} | v 0 + ... + v n = m }`

described in *partial sum coordinates*: a vertex is encoded by the function
`s : ℕ → ℕ` with `s j = v 0 + ... + v (j-1)`, so that `s 0 = 0`, `s` is monotone,
and `s j = m` for `j > n`.  The barycentric coordinate `v i` is `s (i+1) - s i`.

The triangulation is the classical Freudenthal–Kuhn triangulation: a maximal cell
is given by a base vertex `s` together with an ordering of the `n` coordinates
`1, …, n`; the ordering is encoded by the function `p : ℕ → ℕ` sending a coordinate
`j ∈ [1,n]` to the step `p j ∈ [0,n-1]` at which it is incremented.  The `k`-th
vertex of the cell is then `wv n s p k`.
-/

/-- `Reg n m s` says that `s` encodes a vertex of the `m`-fold dilated standard
`n`-simplex, in partial sum coordinates. -/

lemma IsPos.surj {n : ℕ} {p : ℕ → ℕ} (h : IsPos n p) {i : ℕ} (hi : i < n) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ p j = i := by
  classical
  have hsub : (Finset.Icc 1 n).image p ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hx
    exact Finset.mem_range.2 (h.1 j hj1 hj2)
  have hcard : ((Finset.Icc 1 n).image p).card = n := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      exact h.2.1 a b ha.1 ha.2 hb.1 hb.2 hab
  have heq : (Finset.Icc 1 n).image p = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have : i ∈ (Finset.Icc 1 n).image p := by rw [heq]; exact Finset.mem_range.2 hi
  simp only [Finset.mem_image, Finset.mem_Icc] at this
  obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := this
  exact ⟨j, hj1, hj2, hj⟩

/-!
## Basic facts about the vertices of a cell
-/

