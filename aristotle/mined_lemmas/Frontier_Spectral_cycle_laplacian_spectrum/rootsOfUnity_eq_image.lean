import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/

lemma rootsOfUnity_eq_image (n : ℕ) (hn : n ≠ 0) :
    {z : ℂ | z ^ n = 1} =
      (fun k : ℕ => Complex.exp (2 * Real.pi * Complex.I * k / n)) '' (Finset.range n : Set ℕ) := by
  haveI : NeZero n := ⟨hn⟩
  have hprim := Complex.isPrimitiveRoot_exp n hn
  have hpow : ∀ k : ℕ, Complex.exp (2 * Real.pi * Complex.I / n) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * k / n) := by
    intro k
    rw [← Complex.exp_nat_mul]
    ring_nf
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · intro hz
    obtain ⟨i, hi, hie⟩ := hprim.eq_pow_of_pow_eq_one hz
    exact ⟨i, hi, by rw [← hpow i, hie]⟩
  · rintro ⟨k, hk, rfl⟩
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    have h : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
    push_cast
    ring

/-- The value of the symbol `2 - X - X ^ (n - 1)` at the `n`-th root of unity `exp (2 π i k / n)`
is the real number `2 - 2 cos (2 π k / n)`. -/
