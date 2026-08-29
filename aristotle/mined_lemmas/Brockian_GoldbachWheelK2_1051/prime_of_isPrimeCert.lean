import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxRecDepth 100000

namespace Brockian

/-- The "spokes" of the wheel: the small primes that are used as the smaller summand
in the Goldbach decompositions below.  (For every even `n ≤ 1051` one of these works.) -/

theorem prime_of_isPrimeCert {p : ℕ} (hb : p < 1600) (h : isPrimeCert p = true) : Nat.Prime p := by
  rw [isPrimeCert, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  have h2' : 2 ≤ p := by simpa using h2
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2', ?_⟩
  intro m hm2 hms hdvd
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  have hm40 : m < 40 := by nlinarith
  have hcontra := hall m (List.mem_range.mpr hm40)
  simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hcontra
  have : p % m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd |> fun _ => (Nat.mod_eq_zero_of_dvd hdvd)
  simp [hm2, hmm, this] at hcontra

/-- The finite Goldbach verification for the wheel of modulus `1051`: every even `n` with
`4 ≤ n < 1052` is the sum of a spoke prime and another prime. -/
