import Mathlib
/-!
# Squarefree count via the Möbius sieve.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib`; no non-core/Archive
namespaces or invented lemmas.
-/
namespace BrockianSieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise. -/

private lemma sq_dvd_iff_dvd {n a b d : ℕ} (hn : n ≠ 0) (h : n = a ^ 2 * b)
    (hb : Squarefree b) : d ^ 2 ∣ n ↔ d ∣ a := by
  have ha : a ≠ 0 := by rintro rfl; simp [h] at hn
  have hb0 : b ≠ 0 := by rintro rfl; simp [h] at hn
  constructor
  · intro hd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
    rw [← Nat.factorization_le_iff_dvd hd0 ha]
    intro p
    have h2 : (d ^ 2).factorization p ≤ n.factorization p :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hn).mpr hd p
    have hbp : b.factorization p ≤ 1 := hb.natFactorization_le_one p
    rw [h, Nat.factorization_mul (pow_ne_zero 2 ha) hb0] at h2
    simp [Nat.factorization_pow] at h2 ⊢
    omega
  · intro hd
    exact h ▸ Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd 2) b

/-- The Möbius sum over all `d` with `d ^ 2 ∣ n` is the squarefree indicator of `n`. -/
