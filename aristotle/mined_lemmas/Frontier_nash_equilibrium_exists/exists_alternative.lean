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

theorem exists_alternative [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    (∃ y ∈ stdSimplex ℝ n, ∀ i, payoffVec A y i ≤ 0) ∨
      (∃ x ∈ stdSimplex ℝ m, ∀ j, 0 < colPayoff A x j) := by
  by_cases hK : ∃ y ∈ stdSimplex ℝ n, ∀ i, payoffVec A y i ≤ 0
  · exact Or.inl hK
  right
  push_neg at hK
  have hdisj : Disjoint (payoffVec A '' stdSimplex ℝ n) {z : m → ℝ | ∀ i, z i ≤ 0} := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hz
    obtain ⟨i, hi⟩ := hK y hy
    exact absurd (hz i) (not_le.2 hi)
  obtain ⟨f, u, v, hKu, huv, hNv⟩ := geometric_hahn_banach_compact_closed
    (convex_payoffVec_image A) (isCompact_payoffVec_image A) convex_nonpos isClosed_nonpos hdisj
  obtain ⟨c, hcdef⟩ : ∃ c : m → ℝ, ∀ i, c i = f (Pi.single i 1) := ⟨_, fun _ => rfl⟩
  have hrep : ∀ z : m → ℝ, f z = ∑ i, z i * c i := by
    intro z
    rw [strongDual_repr f]
    exact Finset.sum_congr rfl fun i _ => by rw [hcdef i]
  -- `v < 0`, since `0` lies in the nonpositive orthant
  have hv : v < 0 := by
    have : v < f 0 := hNv 0 (by intro i; simp)
    simpa using this
  -- all coefficients of `f` are nonpositive
  have hcnonpos : ∀ i, c i ≤ 0 := by
    intro i
    by_contra hci
    push_neg at hci
    have hcne : c i ≠ 0 := ne_of_gt hci
    set t : ℝ := (1 - v) / c i with ht
    have htpos : 0 < t := div_pos (by linarith) hci
    have hval : t * c i = 1 - v := by
      rw [ht]; field_simp
    have hmem : (fun k => if k = i then -t else 0) ∈ {z : m → ℝ | ∀ k, z k ≤ 0} := by
      intro k
      by_cases h : k = i <;> simp [h]
      linarith
    have hlt := hNv _ hmem
    rw [hrep] at hlt
    have hsum : ∑ k, (if k = i then -t else 0) * c k = -t * c i := by
      simp [ite_mul]
    rw [hsum] at hlt
    nlinarith
  -- `f` is strictly negative on the (nonempty) image of the simplex
  have hKneg : ∀ w ∈ payoffVec A '' stdSimplex ℝ n, f w < 0 := fun w hw =>
    lt_trans (hKu w hw) (by linarith)
  obtain ⟨y0, hy0⟩ := stdSimplex_nonempty n
  have hw0 : f (payoffVec A y0) < 0 := hKneg _ ⟨y0, hy0, rfl⟩
  -- hence some coefficient is strictly negative
  have hexists : ∃ i, c i < 0 := by
    by_contra hall
    push_neg at hall
    have hzero : ∀ i, c i = 0 := fun i => le_antisymm (hcnonpos i) (hall i)
    have : f (payoffVec A y0) = 0 := by
      rw [hrep]
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]
    linarith
  obtain ⟨i0, hi0⟩ := hexists
  set D : ℝ := ∑ i, -c i with hD
  have hDpos : 0 < D := by
    refine Finset.sum_pos' (fun i _ => by linarith [hcnonpos i]) ⟨i0, Finset.mem_univ _, ?_⟩
    linarith
  refine ⟨fun i => (-c i) / D, ⟨fun i => div_nonneg (by linarith [hcnonpos i]) hDpos.le, ?_⟩,
    ?_⟩
  · rw [← Finset.sum_div, ← hD]
    exact div_self (ne_of_gt hDpos)
  · intro j
    have hfj : f (payoffVec A (pureVec j)) < 0 := hKneg _ ⟨pureVec j, pureVec_mem_stdSimplex j, rfl⟩
    have hrepr : f (payoffVec A (pureVec j)) = ∑ i, A i j * c i := by
      rw [hrep]
      exact Finset.sum_congr rfl fun i _ => by rw [payoffVec_pureVec]
    have hsum : colPayoff A (fun i => (-c i) / D) j = (∑ i, -(A i j * c i)) / D := by
      rw [colPayoff, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [hsum]
    apply div_pos _ hDpos
    have : ∑ i, -(A i j * c i) = -(∑ i, A i j * c i) := by
      rw [← Finset.sum_neg_distrib]
    rw [this, ← hrepr]
    linarith

/-! ### The value of the game -/

/-- The security level of the row player's mixed strategy `x`: the worst payoff over all
columns. -/
