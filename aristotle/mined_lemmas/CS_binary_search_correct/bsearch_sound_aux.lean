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

theorem bsearch_sound_aux (a : Array α) (k : α) (hlin : IsLinear α) :
    ∀ n lo hi i : Nat, hi - lo ≤ n → bsearch a k lo hi = some i →
      lo ≤ i ∧ i < hi ∧ a[i]! = k := by
  intro n
  induction n with
  | zero =>
    intro lo hi i hn hres
    rw [bsearch] at hres
    have hle : ¬ (lo < hi) := by omega
    simp only [hle, if_false] at hres
    exact absurd hres (by simp)
  | succ n ih =>
    intro lo hi i hn hres
    rw [bsearch] at hres
    by_cases hlt : lo < hi
    · have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 < hi := by omega
      simp only [hlt, if_true] at hres
      by_cases h1 : a[(lo + hi) / 2]! < k
      · simp only [h1, if_true] at hres
        have := ih ((lo + hi) / 2 + 1) hi i (by omega) hres
        exact ⟨by omega, this.2.1, this.2.2⟩
      · simp only [h1, if_false] at hres
        by_cases h2 : k < a[(lo + hi) / 2]!
        · simp only [h2, if_true] at hres
          have := ih lo ((lo + hi) / 2) i (by omega) hres
          exact ⟨this.1, by omega, this.2.2⟩
        · simp only [h2, if_false, Option.some.injEq] at hres
          subst hres
          exact ⟨hm1, hm2, hlin _ _ h1 h2⟩
    · simp only [hlt, if_false] at hres
      exact absurd hres (by simp)

/-- Soundness: any index returned by binary search lies in the searched slice
and really holds the key.  (No sortedness assumption is needed here.) -/
