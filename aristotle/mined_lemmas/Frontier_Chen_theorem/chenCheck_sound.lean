import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

theorem chenCheck_sound {n : ℕ} (h : chenCheck n = true) : IsChenNumber n := by
  rw [chenCheck, List.any_eq_true] at h
  obtain ⟨p, -, hp⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hp
  obtain ⟨⟨hpp, hple⟩, hq⟩ := hp
  rcases Bool.or_eq_true _ _ |>.mp hq with h1 | h2
  · refine ⟨p, n - p, hpp, isP2_of_prime (of_decide_eq_true h1), by omega⟩
  · rw [List.any_eq_true] at h2
    obtain ⟨a, -, ha⟩ := h2
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      beq_iff_eq] at ha
    obtain ⟨⟨hap, hdvd⟩, hdiv⟩ := ha
    have hd : a ∣ (n - p) := Nat.dvd_of_mod_eq_zero hdvd
    refine ⟨p, a * ((n - p) / a), hpp, isP2_mul_of_prime hap hdiv, ?_⟩
    rw [Nat.mul_div_cancel' hd]
    omega

/-! ### The verified base case -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
