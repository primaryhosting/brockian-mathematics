import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


theorem isPrimeB_sound (n : Nat) (h : isPrimeB n = true) : IsPrime n := by
  unfold isPrimeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, ht⟩ := h
  refine ⟨h2, ?_⟩
  intro m hmn hdvd
  by_cases hm1 : m = 1
  · exact hm1
  · exfalso
    have hm0 : m ≠ 0 := by rintro rfl; have := Nat.eq_zero_of_zero_dvd hdvd; omega
    have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · match k, hlt with
        | 0, _ => simp at hk; omega
        | 1, _ => simp at hk; omega
      · exact hge
    rcases Nat.le_total m k with hmk | hmk
    · exact trialDiv_sound n n 2 m ht hm2
        (by calc m * m ≤ m * k := Nat.mul_le_mul_left m hmk
              _ = n := hk.symm) (by omega) ⟨k, hk⟩
    · exact trialDiv_sound n n 2 k ht hk2
        (by calc k * k ≤ m * k := Nat.mul_le_mul_right k hmk
              _ = n := hk.symm) (by omega) ⟨m, by rw [hk, Nat.mul_comm]⟩

/-- The `K = 2` Goldbach wheel: the list of prime spokes used to split every even
number `n` with `4 ≤ n ≤ 2 * 947` as `p + (n - p)` with both parts prime. -/
