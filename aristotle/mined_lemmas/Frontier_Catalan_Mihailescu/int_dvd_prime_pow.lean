import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma int_dvd_prime_pow {A : ℤ} (hA : 0 < A) {r m : ℕ} (hr : r.Prime) (h : A ∣ (r:ℤ) ^ m) :
    ∃ u, u ≤ m ∧ A = (r:ℤ) ^ u := by
  have h1 : A.natAbs ∣ r ^ m := by
    have h2 := Int.natAbs_dvd_natAbs.mpr h
    simpa [Int.natAbs_pow] using h2
  obtain ⟨u, hu, h'⟩ := (Nat.dvd_prime_pow hr).1 h1
  refine ⟨u, hu, ?_⟩
  have habs : (A.natAbs : ℤ) = A := Int.natAbs_of_nonneg hA.le
  rw [← habs, h']
  push_cast
  ring

