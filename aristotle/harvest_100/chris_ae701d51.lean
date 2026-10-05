import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Setting

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`; the only known ones are
`n = 4, 5, 7`, and it is an open problem whether there are others.

The *Brocard gap* statement formalised here is the quantitative "sparseness of squares just
above `n !`" phenomenon underlying the conjecture:

* consecutive squares just above `n !` are more than `Nat.sqrt (n !)` apart, so the window
  `(n !, n ! + Nat.sqrt (n !)]` contains **at most one** perfect square;
* for `n ≥ 8` this window has length at least `n ^ 2`, because `n ^ 4 ≤ n !` (proved by
  induction on `n`);
* consequently any Brocard solution `n ! + 1 = m ^ 2` with `n ≥ 8` has `m > n ^ 2` and yields
  the factorisation `n ! = (m - 1) * (m + 1)` of `n !` into two factors differing by `2`.
-/

open scoped Nat

namespace Brockian
namespace BrocardGap

/-- The Brocard gap window at `n`: the integers strictly above `n !` and at most
`n ! + Nat.sqrt (n !)`. -/
def window (n : ℕ) : Set ℕ := {k | n ! < k ∧ k ≤ n ! + Nat.sqrt (n !)}

/-- Growth lemma, proved by induction on `n`: `n ^ 5 ≤ n !` for `n ≥ 8`. -/
theorem pow_five_le_factorial : ∀ n : ℕ, 8 ≤ n → n ^ 5 ≤ n ! := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 8 with hk | hk
    · have hk8 : k + 1 = 8 := by omega
      rw [hk8]
      decide
    · have hk' : k ^ 5 ≤ k ! := ih hk
      have hstep : (k + 1) ^ 4 ≤ k ^ 5 := by
        have h1 : (8 * (k + 1)) ^ 4 ≤ (9 * k) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        have e1 : (8 * (k + 1)) ^ 4 = 4096 * (k + 1) ^ 4 := by ring
        have e2 : (9 * k) ^ 4 = 6561 * k ^ 4 := by ring
        rw [e1, e2] at h1
        have h2 : 6561 * k ^ 4 ≤ 4096 * k ^ 5 := by
          have hc : 6561 ≤ 4096 * k := by omega
          calc 6561 * k ^ 4 ≤ (4096 * k) * k ^ 4 := Nat.mul_le_mul_right _ hc
            _ = 4096 * k ^ 5 := by ring
        exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by norm_num)
      calc (k + 1) ^ 5 = (k + 1) * (k + 1) ^ 4 := by ring
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul_left _ (hstep.trans hk')
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- `n ^ 4 ≤ n !` for `n ≥ 8`. -/
theorem pow_four_le_factorial (n : ℕ) (hn : 8 ≤ n) : n ^ 4 ≤ n ! :=
  le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (pow_five_le_factorial n hn)

/-- For `n ≥ 8` the Brocard gap window has length at least `n ^ 2`. -/
theorem sq_le_sqrt_factorial (n : ℕ) (hn : 8 ≤ n) : n ^ 2 ≤ Nat.sqrt (n !) := by
  refine Nat.le_sqrt.2 ?_
  calc n ^ 2 * n ^ 2 = n ^ 4 := by ring
    _ ≤ n ! := pow_four_le_factorial n hn

/-- If `a ^ 2` exceeds `N`, then `a` exceeds `Nat.sqrt N`. -/
theorem sqrt_lt_of_lt_sq {N a : ℕ} (ha : N < a ^ 2) : Nat.sqrt N < a := by
  by_contra h
  push_neg at h
  have : a * a ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul h h
  have hN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have ha2 : a ^ 2 = a * a := by ring
  omega

/-- **Gap bound.** The distance from a square lying just above `n !` to the next square is
more than `Nat.sqrt (n !)`. -/
theorem sqrt_factorial_lt_gap {n a : ℕ} (ha : n ! < a ^ 2) :
    Nat.sqrt (n !) < (a + 1) ^ 2 - a ^ 2 := by
  have h : Nat.sqrt (n !) < a := sqrt_lt_of_lt_sq ha
  have hexp : (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
  omega

/-- For `n ≥ 8`, the gap between consecutive squares just above `n !` exceeds `n ^ 2`. -/
theorem sq_lt_gap {n a : ℕ} (hn : 8 ≤ n) (ha : n ! < a ^ 2) :
    n ^ 2 < (a + 1) ^ 2 - a ^ 2 :=
  lt_of_le_of_lt (sq_le_sqrt_factorial n hn) (sqrt_factorial_lt_gap ha)

/-- **At most one square lies in the Brocard gap window.** -/
theorem unique_square_in_window {n a b : ℕ}
    (ha : a ^ 2 ∈ window n) (hb : b ^ 2 ∈ window n) : a = b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have key : ∀ x y : ℕ, n ! < x ^ 2 → y ^ 2 ≤ n ! + Nat.sqrt (n !) → x < y → False := by
    intro x y hx1 hy2 hxy
    have hx : Nat.sqrt (n !) < x := sqrt_lt_of_lt_sq hx1
    have h1 : (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hxy 2
    have h2 : (x + 1) ^ 2 = x ^ 2 + (2 * x + 1) := by ring
    omega
  rcases lt_trichotomy a b with h | h | h
  · exact absurd h (fun hlt => key a b ha1 hb2 hlt)
  · exact h
  · exact absurd h (fun hlt => key b a hb1 ha2 hlt)

/-- **Reduction of Brocard solutions.** A solution `n ! + 1 = m ^ 2` with `n ≥ 8` forces
`m > n ^ 2` and exhibits `n !` as a product of two integers differing by `2`. -/
theorem brocard_solution_reduction {n m : ℕ} (hn : 8 ≤ n) (h : n ! + 1 = m ^ 2) :
    n ^ 2 < m ∧ n ! = (m - 1) * (m + 1) := by
  have hgt : n ! < m ^ 2 := by omega
  have hm : n ^ 2 < m :=
    lt_of_le_of_lt (sq_le_sqrt_factorial n hn) (sqrt_lt_of_lt_sq hgt)
  refine ⟨hm, ?_⟩
  have hfac : (m - 1) * (m + 1) + 1 = m ^ 2 := by
    cases m with
    | zero => omega
    | succ k =>
      have hk : (k + 1 - 1) * (k + 1 + 1) + 1 = (k + 1) ^ 2 := by
        simp only [Nat.add_sub_cancel]
        ring
      exact hk
  omega

/-- The three known Brocard solutions. -/
theorem brocard_known_solutions :
    4 ! + 1 = 5 ^ 2 ∧ 5 ! + 1 = 11 ^ 2 ∧ 7 ! + 1 = 71 ^ 2 :=
  ⟨by decide, by decide, by decide⟩

/-- **Brocard Gap Conjecture.**

For every `n ≥ 8`:

* the window `(n !, n ! + Nat.sqrt (n !)]` contains at most one perfect square, and this
  window has length at least `n ^ 2`;
* consecutive squares just above `n !` are more than `n ^ 2` apart;
* every Brocard solution `n ! + 1 = m ^ 2` satisfies `m > n ^ 2` and yields the factorisation
  `n ! = (m - 1) * (m + 1)` into two factors differing by `2`.
-/
theorem BrocardGapConjecture (n : ℕ) (hn : 8 ≤ n) :
    n ^ 2 ≤ Nat.sqrt (n !) ∧
    (∀ a b : ℕ, a ^ 2 ∈ window n → b ^ 2 ∈ window n → a = b) ∧
    (∀ a : ℕ, n ! < a ^ 2 → n ^ 2 < (a + 1) ^ 2 - a ^ 2) ∧
    (∀ m : ℕ, n ! + 1 = m ^ 2 → n ^ 2 < m ∧ n ! = (m - 1) * (m + 1)) :=
  ⟨sq_le_sqrt_factorial n hn,
    fun _ _ ha hb => unique_square_in_window ha hb,
    fun _ ha => sq_lt_gap hn ha,
    fun _ hm => brocard_solution_reduction hn hm⟩

end BrocardGap
end Brockian

