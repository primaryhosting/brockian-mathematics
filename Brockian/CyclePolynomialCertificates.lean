import Mathlib

/-!
# Exact scalar polynomial certificates for the five- and thirteen-cycle spectra

These identities explain the polynomial factors of the Fourier eigenvalues.
The matrix rank and minimal-polynomial irreducibility statements are distinct
obligations; neither is claimed by the scalar identities alone.
-/

namespace Brockian.CyclePolynomialCertificates

variable {K : Type*} [Field K]

def psi13 (t : K) : K := t ^ 6 + t ^ 5 - 5 * t ^ 4 - 4 * t ^ 3 +
  6 * t ^ 2 + 3 * t - 1

theorem five_factor_identity (x : K) (hx : x ≠ 0) :
    (x + x⁻¹ - 2) * ((x + x⁻¹) ^ 2 + (x + x⁻¹) - 1) =
      (x - 1) * (x ^ 5 - 1) / x ^ 3 := by
  field_simp
  <;> ring

theorem thirteen_factor_identity (x : K) (hx : x ≠ 0) :
    (x + x⁻¹ - 2) * psi13 (x + x⁻¹) =
      (x - 1) * (x ^ 13 - 1) / x ^ 7 := by
  dsimp [psi13]
  field_simp
  <;> ring

theorem five_root_annihilator (x : K) (hx : x ^ 5 = 1) :
    (x + x⁻¹ - 2) * ((x + x⁻¹) ^ 2 + (x + x⁻¹) - 1) = 0 := by
  have h0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  rw [five_factor_identity x h0, hx]
  simp

theorem thirteen_root_annihilator (x : K) (hx : x ^ 13 = 1) :
    (x + x⁻¹ - 2) * psi13 (x + x⁻¹) = 0 := by
  have h0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  rw [thirteen_factor_identity x h0, hx]
  simp

theorem character_power (N : ℕ) [NeZero N] (k : ZMod N) :
    (ZMod.stdAddChar k) ^ N = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul, ZMod.natCast_self, AddChar.map_zero_eq_one]

theorem five_fourier_eigenvalue (k : ZMod 5) :
    let t := ZMod.stdAddChar k + ZMod.stdAddChar (-k)
    (t - 2) * (t ^ 2 + t - 1) = 0 := by
  dsimp
  rw [AddChar.map_neg_eq_inv]
  exact five_root_annihilator _ (character_power 5 k)

theorem thirteen_fourier_eigenvalue (k : ZMod 13) :
    let t := ZMod.stdAddChar k + ZMod.stdAddChar (-k)
    (t - 2) * psi13 t = 0 := by
  dsimp
  rw [AddChar.map_neg_eq_inv]
  exact thirteen_root_annihilator _ (character_power 13 k)

end Brockian.CyclePolynomialCertificates
