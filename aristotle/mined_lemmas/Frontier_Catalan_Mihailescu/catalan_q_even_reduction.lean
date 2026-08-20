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

lemma catalan_q_even_reduction {x y p q : ℕ} (hy : 1 < y) (hp : 1 < p) (hq : 1 < q)
    (h : x ^ p = y ^ q + 1) (hqe : Even q) : Odd x ∧ Even y ∧ Odd p := by
  obtain ⟨k, rfl⟩ := hqe
  have hk : k ≠ 0 := by omega
  have hsplit : y ^ (k + k) = (y ^ k) * (y ^ k) := by rw [← pow_add]
  have hZeven : Even (y ^ k) := by
    rcases Nat.even_or_odd (y ^ k) with he | ho
    · exact he
    · exfalso
      rcases ho with ⟨t, ht⟩
      have hxe : Even x := by
        rcases Nat.even_or_odd x with he' | ho'
        · exact he'
        · exfalso
          have : Odd (x ^ p) := ho'.pow
          rcases this with ⟨s, hs⟩
          rw [hsplit, ht] at h
          have hexp : (2 * t + 1) * (2 * t + 1) + 1 = 2 * (2 * t * t + 2 * t + 1) := by ring
          omega
      have h4 : (4:ℕ) ∣ x ^ p := by
        obtain ⟨u, hu⟩ := hxe
        have : (2:ℕ) ^ 2 ∣ x ^ p := by
          have h2 : (2:ℕ) ∣ x := ⟨u, by omega⟩
          calc (2:ℕ) ^ 2 ∣ x ^ 2 := pow_dvd_pow_of_dvd h2 2
          _ ∣ x ^ p := pow_dvd_pow x (by omega)
        simpa using this
      rw [hsplit, ht] at h
      rcases h4 with ⟨s, hs⟩
      have hexp : (2 * t + 1) * (2 * t + 1) + 1 = 4 * (t * t + t) + 2 := by ring
      omega
  have hyeven : Even y := by
    rcases Nat.even_or_odd y with he | ho
    · exact he
    · exact absurd hZeven (by simpa using ho.pow (n := k))
  have hxodd : Odd x := by
    rcases Nat.even_or_odd x with he | ho
    · exfalso
      have hxp : Even (x ^ p) := (Nat.even_pow (n := p)).2 ⟨he, by omega⟩
      have hyq : Even (y ^ (k + k)) := by
        rw [hsplit]
        exact hZeven.mul_right _
      rcases hxp with ⟨s, hs⟩; rcases hyq with ⟨t, ht⟩; omega
    · exact ho
  refine ⟨hxodd, hyeven, ?_⟩
  rcases Nat.even_or_odd p with he | ho
  · exact absurd h (catalan_even_even (by omega) he ⟨k, rfl⟩)
  · exact ho

/-! ### A finite verification -/

set_option maxRecDepth 1000000 in
/-- Exhaustive kernel check of Catalan's equation in the box `x, y ≤ 100`, `p, q ≤ 13`,
for powers of size at most `10000`. -/
