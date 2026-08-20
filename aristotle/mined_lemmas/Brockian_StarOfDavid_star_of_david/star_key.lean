import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/

private lemma star_key {a b c a' b' c' : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (hprod : a * b * c = a' * b' * c')
    (h1 : c' = a + a' + b) (h2 : c = b' + a + a') :
    Nat.gcd (Nat.gcd a b) c ∣ Nat.gcd (Nat.gcd a' b') c' := by
  have hda : Nat.gcd (Nat.gcd a b) c ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b)
  have hdb : Nat.gcd (Nat.gcd a b) c ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a b)
  have hdc : Nat.gcd (Nat.gcd a b) c ∣ c := Nat.gcd_dvd_right _ _
  have hda' : Nat.gcd (Nat.gcd a b) c ∣ a' := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p e hp hpe
    by_contra hcon
    have hpa : p ^ e ∣ a := hpe.trans hda
    have hpb : p ^ e ∣ b := hpe.trans hdb
    have hpc : p ^ e ∣ c := hpe.trans hdc
    have hnb' : ¬ p ^ e ∣ b' := by
      intro h
      refine hcon ?_
      have hsub : c - (b' + a) = a' := by omega
      exact hsub ▸ Nat.dvd_sub hpc (dvd_add h hpa)
    have hnc' : ¬ p ^ e ∣ c' := by
      intro h
      refine hcon ?_
      have hsub : c' - (a + b) = a' := by omega
      exact hsub ▸ Nat.dvd_sub h (dvd_add hpa hpb)
    have hA : e ≤ a.factorization p := (hp.pow_dvd_iff_le_factorization ha).1 hpa
    have hB : e ≤ b.factorization p := (hp.pow_dvd_iff_le_factorization hb).1 hpb
    have hC : e ≤ c.factorization p := (hp.pow_dvd_iff_le_factorization hc).1 hpc
    have hA' : a'.factorization p < e := by
      by_contra hle
      exact hcon ((hp.pow_dvd_iff_le_factorization ha').2 (not_lt.1 hle))
    have hB' : b'.factorization p < e := by
      by_contra hle
      exact hnb' ((hp.pow_dvd_iff_le_factorization hb').2 (not_lt.1 hle))
    have hC' : c'.factorization p < e := by
      by_contra hle
      exact hnc' ((hp.pow_dvd_iff_le_factorization hc').2 (not_lt.1 hle))
    have hfl : (a * b * c).factorization p
        = a.factorization p + b.factorization p + c.factorization p := by
      rw [Nat.factorization_mul (mul_ne_zero ha hb) hc, Nat.factorization_mul ha hb]
      simp
    have hfr : (a' * b' * c').factorization p
        = a'.factorization p + b'.factorization p + c'.factorization p := by
      rw [Nat.factorization_mul (mul_ne_zero ha' hb') hc', Nat.factorization_mul ha' hb']
      simp
    rw [hprod, hfr] at hfl
    omega
  have hdb' : Nat.gcd (Nat.gcd a b) c ∣ b' := by
    have hsub : c - (a + a') = b' := by omega
    exact hsub ▸ Nat.dvd_sub hdc (dvd_add hda hda')
  have hdc' : Nat.gcd (Nat.gcd a b) c ∣ c' := by
    rw [h1]; exact dvd_add (dvd_add hda hda') hdb
  exact Nat.dvd_gcd (Nat.dvd_gcd hda' hdb') hdc'

/-- Abstract form of the Star of David theorem. -/
