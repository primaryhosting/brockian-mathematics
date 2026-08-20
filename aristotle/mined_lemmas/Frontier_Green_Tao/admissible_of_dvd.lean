import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header block above
-- appears immediately after the single `import Mathlib` line.)

set_option maxRecDepth 10000

namespace Frontier

/-- `IsPrimeAP k a d` says that `a, a + d, …, a + (k-1) d` is an arithmetic progression of
length `k` consisting of prime numbers, with positive common difference `d`. -/

theorem admissible_of_dvd (k d : ℕ) (hd : ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d)
    (p : ℕ) (hp : p.Prime) : ∃ n : ℕ, ∀ i < k, ¬ (p ∣ (i * d + n)) := by
  by_cases hpk : p ≤ k
  · -- `p ∣ d`, so all the forms are `≡ 1 (mod p)` at `n = 1`.
    refine ⟨1, fun i _ hdvd => ?_⟩
    have h2 : p ∣ i * d := Dvd.dvd.mul_left (hd p hp hpk) i
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub hdvd h2
      simpa using this
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h3)
  · -- `p > k`: the `k` forbidden residues cannot cover all `p` residue classes.
    push_neg at hpk
    set S : Finset ℕ := (Finset.range k).image (fun i => (p - i * d % p) % p) with hS
    have hcard : S.card ≤ k := le_trans (Finset.card_image_le) (by simp)
    have hns : ¬ (Finset.range p ⊆ S) := by
      intro h
      have := Finset.card_le_card h
      simp only [Finset.card_range] at this
      omega
    obtain ⟨n, hn, hnS⟩ := Finset.not_subset.mp hns
    have hnp : n < p := Finset.mem_range.mp hn
    refine ⟨n, fun i hi hdvd => hnS ?_⟩
    have hppos : 0 < p := hp.pos
    set r := i * d % p with hr
    have hrp : r < p := Nat.mod_lt _ hppos
    have hdv : p ∣ r + n := by
      have : (i * d + n) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      have h4 : (r + n % p) % p = 0 := by
        rwa [Nat.add_mod] at this
      rw [Nat.mod_eq_of_lt hnp] at h4
      exact Nat.dvd_iff_mod_eq_zero.mpr h4
    obtain ⟨c, hc⟩ := hdv
    have hc2 : c < 2 := by
      by_contra hcon
      push_neg at hcon
      have : p * 2 ≤ p * c := Nat.mul_le_mul_left p hcon
      omega
    have hkey : n = (p - r) % p := by
      interval_cases c
      · simp only [Nat.mul_zero] at hc
        have hr0 : r = 0 := by omega
        have hn0 : n = 0 := by omega
        simp [hr0, hn0]
      · have hcp : r + n = p := by omega
        have hrpos : 0 < r := by omega
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    rw [hS]
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, by rw [hkey, hr]⟩

/-- **Green–Tao, conditional on Dickson's conjecture.**  Dickson's conjecture implies that
the primes contain arbitrarily long arithmetic progressions.  For each `k` the progression
can be taken with common difference `(k+1)!`. -/
