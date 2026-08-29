/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality, stated in the usual way: `p` is at least `2` and its only divisors are
`1` and `p`. (This file is self-contained, so the predicate is spelled out here.) -/

theorem gwIsPrime_sound {p : Nat} (hp : p ≤ 1051) (h : gwIsPrime p = true) : GwPrime p := by
  rw [gwIsPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hdiv⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  obtain ⟨k, hk⟩ := hm
  -- both factors are at least 2
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, Nat.zero_mul] at hk; omega
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0, Nat.mul_zero] at hk; omega
  have hk1 : k ≠ 1 := by
    intro h1; rw [h1, Nat.mul_one] at hk; omega
  have hm2 : 2 ≤ m := by omega
  have hk2 : 2 ≤ k := by omega
  -- the smaller factor `d` satisfies `d * d ≤ p`
  obtain ⟨d, hd⟩ : ∃ d, min m k = d := ⟨_, rfl⟩
  have hdor : d = m ∨ d = k := by
    rw [← hd]
    rcases Nat.le_total m k with h | h
    · exact Or.inl (Nat.min_eq_left h)
    · exact Or.inr (Nat.min_eq_right h)
  have hdm : d ≤ m := hd ▸ Nat.min_le_left m k
  have hdk : d ≤ k := hd ▸ Nat.min_le_right m k
  have hd2 : 2 ≤ d := by omega
  have hdd : d * d ≤ p := by
    calc d * d ≤ m * k := Nat.mul_le_mul hdm hdk
    _ = p := hk.symm
  have hd32 : d < 33 := by
    rcases Nat.lt_or_ge d 33 with h | h
    · exact h
    · exfalso
      have : 33 * 33 ≤ d * d := Nat.mul_le_mul h h
      omega
  -- `d` divides `p`, contradicting the trial division check
  have hmod : p % d = 0 := by
    rcases hdor with hde | hde
    · rw [hde, hk]
      exact Nat.mul_mod_right m k
    · rw [hde, hk]
      exact Nat.mul_mod_left m k
  have hmem : d ∈ List.range 33 := List.mem_range.mpr hd32
  have := List.all_eq_true.mp hdiv d hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at this
  omega

/-- The "wheel" of small prime shifts: for every even `n` with `4 ≤ n ≤ 1051`
one of these primes `p` satisfies `n - p` prime. -/
