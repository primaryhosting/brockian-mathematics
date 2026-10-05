import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma fourier_inversion (v : ZMod 9 → ℂ) (x : ZMod 9) :
    ∑ k : ZMod 9, ec (k * x) * (∑ y : ZMod 9, ec (-(k * y)) * v y) = 9 * v x := by
  have step : ∀ k : ZMod 9, ec (k * x) * (∑ y : ZMod 9, ec (-(k * y)) * v y)
      = ∑ y : ZMod 9, ec ((x - y) * k) * v y := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← ec_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
  have h2 : ∀ y : ZMod 9, ∑ k : ZMod 9, ec ((x - y) * k) * v y
      = (if y = x then (9 : ℂ) else 0) * v y := by
    intro y
    rw [← Finset.sum_mul, sum_ec]
    congr 1
    simp [sub_eq_zero, eq_comm]
  rw [Finset.sum_congr rfl (fun y _ => h2 y)]
  simp

