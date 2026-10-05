/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α]

/-- `Sorted a` says that the array `a` is weakly increasing: no later entry is
strictly smaller than an earlier one. -/

theorem bsearch_isSome_iff_aux (a : Array α) (k : α)
    (hlin : IsLinear α) (hsort : Sorted a) :
    ∀ n lo hi : Nat, hi - lo ≤ n → hi ≤ a.size →
      ((bsearch a k lo hi).isSome ↔ ∃ i : Nat, lo ≤ i ∧ i < hi ∧ a[i]! = k) := by
  intro n
  induction n with
  | zero =>
    intro lo hi hn hhi
    have hle : ¬ (lo < hi) := by omega
    rw [bsearch]
    simp only [hle, if_false, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨i, h1, h2, -⟩
    omega
  | succ n ih =>
    intro lo hi hn hhi
    rw [bsearch]
    by_cases hlt : lo < hi
    · have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 < hi := by omega
      simp only [hlt, if_true]
      by_cases h1 : a[(lo + hi) / 2]! < k
      · simp only [h1, if_true]
        rw [ih ((lo + hi) / 2 + 1) hi (by omega) hhi]
        constructor
        · rintro ⟨i, hi1, hi2, hi3⟩
          exact ⟨i, by omega, hi2, hi3⟩
        · rintro ⟨i, hi1, hi2, hi3⟩
          refine ⟨i, ?_, hi2, hi3⟩
          rcases Nat.lt_or_ge ((lo + hi) / 2) i with h | h
          · omega
          · have hcon := hsort i ((lo + hi) / 2) h (by omega)
            rw [hi3] at hcon
            exact absurd h1 hcon
      · simp only [h1, if_false]
        by_cases h2 : k < a[(lo + hi) / 2]!
        · simp only [h2, if_true]
          rw [ih lo ((lo + hi) / 2) (by omega) (by omega)]
          constructor
          · rintro ⟨i, hi1, hi2, hi3⟩
            exact ⟨i, hi1, by omega, hi3⟩
          · rintro ⟨i, hi1, hi2, hi3⟩
            refine ⟨i, hi1, ?_, hi3⟩
            rcases Nat.lt_or_ge i ((lo + hi) / 2) with h | h
            · exact h
            · have hcon := hsort ((lo + hi) / 2) i h (by omega)
              rw [hi3] at hcon
              exact absurd h2 hcon
        · simp only [h2, if_false]
          have heq : a[(lo + hi) / 2]! = k := hlin _ _ h1 h2
          simp only [Option.isSome_some, true_iff]
          exact ⟨(lo + hi) / 2, hm1, hm2, heq⟩
    · simp only [hlt, if_false, Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨i, ha, hb, -⟩
      omega

/-- Correctness on a slice: on a sorted array, binary search on `[lo, hi)`
succeeds iff the key occurs in that slice. -/
