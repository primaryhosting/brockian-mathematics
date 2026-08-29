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

theorem isPrimeB_spec {n : Nat} (h : isPrimeB n = true) : IsPrimeNat n := by
  rw [isPrimeB, Bool.and_eq_true] at h
  obtain ⟨h2, hnd⟩ := h
  have hn2 : 2 ≤ n := by simpa using h2
  have key : ∀ e, 2 ≤ e → e * e ≤ n → n % e ≠ 0 := by
    intro e he2 hee
    have hle : e ≤ e * e := Nat.le_mul_of_pos_right e (by omega)
    exact noDivFrom_spec n n 2 e hnd he2 (by omega) hee
  refine ⟨hn2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmn : m = n
  · exact Or.inr hmn
  exfalso
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by
    intro h0; subst h0; simp at hk; omega
  have hk0 : k ≠ 0 := by
    intro h0; subst h0; simp at hk; omega
  have hk1 : k ≠ 1 := by
    intro h1; subst h1; simp at hk; exact hmn hk.symm
  have hm2 : 2 ≤ m := by omega
  have hk2 : 2 ≤ k := by omega
  rcases Nat.le_total m k with hmk | hkm
  · have hmm : m * m ≤ n := by
      calc m * m ≤ m * k := Nat.mul_le_mul_left m hmk
        _ = n := hk.symm
    exact key m hm2 hmm (by rw [hk]; exact Nat.mul_mod_right m k)
  · have hkk : k * k ≤ n := by
      calc k * k ≤ m * k := Nat.mul_le_mul_right k hkm
        _ = n := hk.symm
    exact key k hk2 hkk (by rw [hk]; exact Nat.mul_mod_left m k)

