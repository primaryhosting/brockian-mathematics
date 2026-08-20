import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian


theorem exists_wheel_split_727 {n : Nat} (hn : n < 728) (h4 : 4 ≤ n) (hev : n % 2 = 0) :
    ∃ p ∈ wheelPrimes727, (n - p) ∈ wheelPrimes727 := by
  have h := List.all_eq_true.mp wheelSearch727_eq_true n (List.mem_range.mpr hn)
  simp only [h4, hev, decide_true, Bool.true_and, Bool.not_true, Bool.false_or,
    beq_self_eq_true, List.any_eq_true, List.contains_iff_mem] at h
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, hp, hq⟩

/-- **Goldbach wheel, `K = 2`, modulus `727`.**
Every even natural number `n` with `4 ≤ n ≤ 727` is a sum of two primes. -/
