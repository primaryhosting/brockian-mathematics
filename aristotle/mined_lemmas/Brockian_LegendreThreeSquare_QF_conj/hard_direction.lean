import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

theorem hard_direction (n : ℕ) (h : ¬ ∃ k m : ℕ, n = 4 ^ k * (8 * m + 7)) :
    ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  -- Handle n = 0
  by_cases hn0 : n = 0
  · exact ⟨0, 0, 0, by simp [hn0]⟩
  -- Induction on n: if n % 4 = 0, reduce to n/4; otherwise apply core
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : n % 4 = 0
    · -- n % 4 = 0: write n = 4 * (n/4), apply IH
      let m := n / 4
      have hm_lt : m < n := by simp [m]; omega
      have hm_pos : 0 < m := by simp [m]; omega
      have hm_nh0 : m ≠ 0 := ne_of_gt hm_pos
      have hm_h : ¬∃ k m_1, m = 4 ^ k * (8 * m_1 + 7) := by
        intro ⟨k, m_1, hm_eq⟩
        have hn_eq : n = 4 ^ (k + 1) * (8 * m_1 + 7) := by
          have : 4 ^ (k + 1) * (8 * m_1 + 7) = 4 * (4 ^ k * (8 * m_1 + 7)) := by ring
          rw [this]
          rw [← hm_eq]
          have : n = 4 * (n / 4) := by omega
          exact this
        exact h ⟨k + 1, m_1, hn_eq⟩
      obtain ⟨a', b', c', hm_eq⟩ := ih m hm_lt hm_h hm_nh0 hm_pos
      use 2 * a', 2 * b', 2 * c'
      have hn_eq : n = 4 * m := by simp [m]; omega
      rw [hn_eq, hm_eq]
      ring
    · -- n % 4 ≠ 0: need to show n % 8 ≠ 7 and apply core
      have h8 : n % 8 ≠ 7 := by
        intro h7
        exact h ⟨0, n / 8, by omega⟩
      exact core n h4 h8

/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/
