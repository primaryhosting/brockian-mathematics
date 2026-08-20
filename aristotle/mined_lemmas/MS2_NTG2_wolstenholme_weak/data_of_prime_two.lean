import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma data_of_prime_two (n p : ℕ) [Fact p.Prime] (hp2 : p % 2 = 1)
    (hdvd : n ∣ 2 * p + 1)
    (hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1) :
    ∃ u M s : ℤ, 0 < M ∧ (n : ℤ) * (u * M - s ^ 2) - M = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hD⟩ : ((n : ℤ)) ∣ (2 * (p : ℤ) + 1) := by
    have := Int.natCast_dvd_natCast.mpr hdvd
    push_cast at this
    exact this
  have hmod : ((n : ℤ) * D) % p = 1 % p := by
    rw [← hD]
    have : (2 * (p : ℤ) + 1) ≡ 1 [ZMOD (p : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-2, by ring⟩
    exact this
  obtain ⟨s₀, hs₀⟩ := sq_mod_prime p D (D_nonzero p n D hmod) (legendre_neg_D p n D hmod hsign)
  -- `D` is odd
  have hDodd : ¬ (2 : ℤ) ∣ D := by
    intro ⟨c, hc⟩
    rw [hc] at hD
    have : (2 : ℤ) ∣ 2 * (p : ℤ) + 1 := ⟨(n : ℤ) * c, by linarith [hD]⟩
    omega
  -- adjust the parity of the square root
  set s : ℤ := if (2 : ℤ) ∣ s₀ then s₀ + p else s₀ with hsdef
  have hps : (p : ℤ) ∣ s ^ 2 + D := by
    rw [hsdef]
    split
    · obtain ⟨c, hc⟩ := hs₀
      exact ⟨c + 2 * s₀ + p, by linear_combination hc⟩
    · exact hs₀
  have hsodd : ¬ (2 : ℤ) ∣ s := by
    rw [hsdef]
    have hpodd : ¬ (2 : ℤ) ∣ (p : ℤ) := by
      intro ⟨c, hc⟩
      have : (2 : ℕ) ∣ p := by
        have : ((2 : ℕ) : ℤ) ∣ (p : ℤ) := ⟨c, by exact_mod_cast hc⟩
        exact_mod_cast this
      omega
    split
    · rename_i h
      intro hcon
      exact hpodd (by omega)
    · rename_i h
      exact h
  have h2s : (2 : ℤ) ∣ s ^ 2 + D := by
    have hso : Odd s := Int.odd_iff.mpr (by omega)
    have hDo : Odd D := Int.odd_iff.mpr (by omega)
    exact (hso.pow.add_odd hDo).two_dvd
  have hcop : IsCoprime (2 : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 2 p := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
    simpa [Int.gcd] using this
  have hdvd2p : (2 * (p : ℤ)) ∣ s ^ 2 + D := hcop.mul_dvd h2s hps
  refine data_of_dvd n (2 * (p : ℤ)) D s ?_ hD.symm hdvd2p
  have := hp.pos
  positivity

/-! ### Jacobi symbol computations -/

