/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Statement: The n-qubit quantum Fourier transform matrix is unitary.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`;
-- the header above is therefore a plain block comment, and is repeated as the
-- module docstring immediately after the import.)


/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

open Complex

/-- The `n`-qubit quantum Fourier transform matrix, acting on the `2^n`-dimensional
state space: its `(j,k)` entry is `exp (2 π i j k / 2^n) / √(2^n)`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / (2 ^ n)) /
    Real.sqrt (2 ^ n)

/-- A geometric sum over the powers of an `N`-th root of unity. -/
lemma sum_pow_root_of_unity (N : ℕ) (x : ℂ) (hx : x ^ N = 1) :
    ∑ m ∈ Finset.range N, x ^ m = if x = 1 then (N : ℂ) else 0 := by
  by_cases h : x = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hx, sub_self, zero_div]

/-- The entries of the QFT matrix, written in terms of the primitive root of unity
`ζ = exp (2 π i / 2^n)`. -/
lemma qft_apply (n : ℕ) (j k : Fin (2 ^ n)) :
    qft n j k =
      Complex.exp (2 * Real.pi * Complex.I / ((2 ^ n : ℕ) : ℂ)) ^ ((j : ℕ) * (k : ℕ)) /
        ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [qft, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hN0 : (2 ^ n : ℕ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    have : 0 < (2 ^ n : ℕ) := Nat.pos_of_ne_zero hN0
    exact_mod_cast this
  have hNC : ((2 ^ n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 ^ n : ℕ) : ℂ)) with hζdef
  have hprim : IsPrimitiveRoot ζ (2 ^ n) := by
    simpa [hζdef, mul_div_assoc] using Complex.isPrimitiveRoot_exp (2 ^ n) hN0
  have hζN : ζ ^ (2 ^ n : ℕ) = 1 := hprim.pow_eq_one
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζN hN0
  have hζne : ζ ≠ 0 := by
    intro h
    rw [h] at hζnorm
    simp at hζnorm
  have hconjζ : (starRingEnd ℂ) ζ = ζ⁻¹ := (Complex.inv_eq_conj hζnorm).symm
  have hsqrt : ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ)
      = ((2 ^ n : ℕ) : ℂ) := by
    have h : Real.sqrt ((2 ^ n : ℕ) : ℝ) * Real.sqrt ((2 ^ n : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ m : Fin (2 ^ n),
      (star (qft n)) a m * qft n m b =
        (ζ⁻¹ ^ (a : ℕ) * ζ ^ (b : ℕ)) ^ (m : ℕ) / ((2 ^ n : ℕ) : ℂ) := by
    intro m
    have h1 : (star (qft n)) a m = (starRingEnd ℂ) (qft n m a) := rfl
    rw [h1, qft_apply, qft_apply, ← hζdef, map_div₀, map_pow, hconjζ, Complex.conj_ofReal,
      div_mul_div_comm, hsqrt]
    congr 1
    rw [mul_comm (m : ℕ) (a : ℕ), mul_comm (m : ℕ) (b : ℕ), pow_mul, pow_mul, ← mul_pow]
  simp only [hterm]
  rw [← Finset.sum_div]
  set x : ℂ := ζ⁻¹ ^ (a : ℕ) * ζ ^ (b : ℕ) with hxdef
  have hxN : x ^ (2 ^ n : ℕ) = 1 := by
    rw [hxdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm (a : ℕ) (2 ^ n : ℕ),
      mul_comm (b : ℕ) (2 ^ n : ℕ), pow_mul, pow_mul, inv_pow, hζN]
    simp
  have hsum : ∑ m : Fin (2 ^ n), x ^ (m : ℕ) = ∑ m ∈ Finset.range (2 ^ n), x ^ m := by
    rw [Finset.sum_range fun i => x ^ i]
  rw [hsum, sum_pow_root_of_unity (2 ^ n) x hxN]
  have hx1 : x = 1 ↔ a = b := by
    rw [hxdef, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hζne)]
    constructor
    · intro h
      exact Fin.ext (hprim.pow_inj a.isLt b.isLt h)
    · intro h
      rw [h]
  by_cases hab : a = b
  · rw [if_pos (hx1.mpr hab), if_pos hab, div_self hNC]
  · rw [if_neg (fun hc => hab (hx1.mp hc)), if_neg hab, zero_div]

end QC

#print axioms QC.qft_unitary

