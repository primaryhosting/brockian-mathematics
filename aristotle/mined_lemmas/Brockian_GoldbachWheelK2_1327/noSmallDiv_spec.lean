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

namespace Brockian

/-! ## A kernel-friendly primality test

Mathlib's `Decidable` instance for `Nat.Prime` performs a linear scan, which makes
`by decide` unusable for numbers of the size we need.  We therefore set up a trial
division test by divisors `≤ 63`, which is sound for all `n < 64 ^ 2 = 4096`.
-/

/-- `noSmallDiv n k = true` asserts that no `d` with `2 ≤ d ≤ k` and `d ≠ n` divides `n`. -/

lemma noSmallDiv_spec : ∀ {n k : ℕ}, noSmallDiv n k = true →
    ∀ {d : ℕ}, 2 ≤ d → d ≤ k → d ≠ n → ¬ (d ∣ n) := by
  intro n k
  induction k with
  | zero => intro _ d hd2 hdk; omega
  | succ k ih =>
      intro h d hd2 hdk hdn
      rw [noSmallDiv, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge d (k + 1) with hlt | hge
      · exact ih h2 hd2 (by omega) hdn
      · have hde : d = k + 1 := by omega
        subst hde
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with (h1 | h1) | h1
        · omega
        · omega
        · exact fun hdvd => h1 (Nat.dvd_iff_mod_eq_zero.mp hdvd)

