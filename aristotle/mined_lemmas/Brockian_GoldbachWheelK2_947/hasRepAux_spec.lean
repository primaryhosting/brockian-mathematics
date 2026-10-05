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

theorem hasRepAux_spec (n : Nat) :
    ∀ fuel p, hasRepAux n fuel p = true →
      ∃ a b, isPrimeB a = true ∧ isPrimeB b = true ∧ a + b = n := by
  intro fuel
  induction fuel with
  | zero => intro p h; exact absurd h (by simp [hasRepAux])
  | succ f ih =>
    intro p h
    rw [hasRepAux] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hpn
      split at h
      · rename_i hpr
        rw [Bool.and_eq_true] at hpr
        exact ⟨p, n - p, hpr.1, hpr.2, by omega⟩
      · exact ih (p + 1) h

