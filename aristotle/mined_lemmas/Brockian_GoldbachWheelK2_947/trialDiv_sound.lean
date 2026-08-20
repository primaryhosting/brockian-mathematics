import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


theorem trialDiv_sound : ∀ (fuel n d e : Nat), trialDiv n fuel d = true → d ≤ e →
    e * e ≤ n → e < d + fuel → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n d e _ h1 _ h3; omega
  | succ f ih =>
    intro n d e ht hde hen hlt
    rw [trialDiv] at ht
    by_cases hd : n < d * d
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [hd, if_false] at ht
      by_cases hm : n % d == 0
      · simp [hm] at ht
      · simp only [hm] at ht
        rcases Nat.eq_or_lt_of_le hde with rfl | hlt2
        · intro hdvd
          have := Nat.dvd_iff_mod_eq_zero.mp hdvd
          simp at hm
          omega
        · exact ih n (d + 1) e ht hlt2 hen (by omega)

/-- Soundness of the Boolean primality test. -/
