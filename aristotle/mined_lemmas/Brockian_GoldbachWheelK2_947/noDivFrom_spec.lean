/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian

/-- Elementary primality predicate: `p` is at least `2` and its only divisors are `1` and `p`. -/

theorem noDivFrom_spec (n : Nat) :
    ∀ fuel d e, noDivFrom n fuel d = true → d ≤ e → e < d + fuel → e * e ≤ n → n % e ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro d e _ h1 h2 _; omega
  | succ f ih =>
    intro d e h hde helt hee
    rw [noDivFrom] at h
    split at h
    · rename_i hlt
      have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · rename_i hge
      split at h
      · exact absurd h (by simp)
      · rename_i hmod
        rw [beq_iff_eq] at hmod
        rcases Nat.eq_or_lt_of_le hde with rfl | hlt
        · exact hmod
        · exact ih (d + 1) e h hlt (by omega) hee

