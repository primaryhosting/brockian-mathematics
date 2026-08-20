/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

theorem exists_saddle_point [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ x ∈ stdSimplex ℝ m, ∃ y ∈ stdSimplex ℝ n,
      (∀ x' ∈ stdSimplex ℝ m, bilin A x' y ≤ bilin A x y) ∧
      (∀ y' ∈ stdSimplex ℝ n, bilin A x y ≤ bilin A x y') := by
  obtain ⟨x, hx, hxmax⟩ := exists_max_rowValue A
  set v : ℝ := rowValue A x with hv
  set B : m → n → ℝ := fun i j => A i j - v with hB
  have halt := exists_alternative B
  -- the second alternative is impossible, by maximality of `x`
  have hnot : ¬ ∃ x' ∈ stdSimplex ℝ m, ∀ j, 0 < colPayoff B x' j := by
    rintro ⟨x', hx', hpos⟩
    have hcol : ∀ j, colPayoff B x' j = colPayoff A x' j - v := by
      intro j
      have : colPayoff B x' j = ∑ i, (x' i * A i j - x' i * v) := by
        refine Finset.sum_congr rfl fun i _ => by simp [hB]; ring
      rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hx'.2, one_mul]
      rfl
    obtain ⟨j0, hj0⟩ := exists_rowValue_eq A x'
    have h1 : v < colPayoff A x' j0 := by
      have := hpos j0
      rw [hcol j0] at this
      linarith
    have h2 := hxmax x' hx'
    rw [← hj0] at h1
    linarith
  obtain ⟨y, hy, hyle⟩ := halt.resolve_right hnot
  have hyA : ∀ i, payoffVec A y i ≤ v := by
    intro i
    have h := hyle i
    have : payoffVec B y i = payoffVec A y i - v := by
      have hexp : payoffVec B y i = ∑ j, (y j * A i j - y j * v) := by
        refine Finset.sum_congr rfl fun j _ => by simp [hB]; ring
      rw [hexp, Finset.sum_sub_distrib, ← Finset.sum_mul, hy.2, one_mul]
      rfl
    rw [this] at h
    linarith
  -- the row player cannot get more than `v` against `y`
  have hrow : ∀ x' ∈ stdSimplex ℝ m, bilin A x' y ≤ v := by
    intro x' hx'
    rw [bilin_eq_row]
    calc ∑ i, x' i * payoffVec A y i ≤ ∑ i, x' i * v :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyA i) (hx'.1 i)
      _ = v := by rw [← Finset.sum_mul, hx'.2, one_mul]
  -- the column player cannot get more than `-v` against `x`
  have hcol : ∀ y' ∈ stdSimplex ℝ n, v ≤ bilin A x y' := by
    intro y' hy'
    rw [bilin_eq_col]
    calc v = ∑ j, y' j * v := by rw [← Finset.sum_mul, hy'.2, one_mul]
      _ ≤ ∑ j, y' j * colPayoff A x j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (rowValue_le A x j) (hy'.1 j)
  have hval : bilin A x y = v := le_antisymm (hrow x hx) (hcol y hy)
  refine ⟨x, hx, y, hy, ?_, ?_⟩
  · intro x' hx'
    rw [hval]
    exact hrow x' hx'
  · intro y' hy'
    rw [hval]
    exact hcol y' hy'

end Frontier

/-
Bridging the minimax theorem into the general finite game framework: a two player
zero sum finite game, viewed as a `FiniteGame` with player set `Bool`, has a mixed
strategy Nash equilibrium.  This is unconditional (no Brouwer hypothesis).
-/

import RequestProject.Minimax

/-!
# Two player zero sum games as finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The strategy sets of a two player game: the row player is `true`. -/
