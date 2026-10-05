import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/

lemma sum_omega_zpow_eq_zero {N : ℕ} (hN : N ≠ 0) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ i : Fin N, omegaRoot N ^ (d * (i : ℕ)) = 0 := by
  have hprim := omegaRoot_isPrimitiveRoot hN
  set z : ℂ := omegaRoot N ^ d with hz
  have hz1 : z ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hzN : z ^ N = 1 := by
    rw [hz, ← _root_.zpow_natCast (omegaRoot N ^ d) N, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, _root_.zpow_natCast, hprim.pow_eq_one, _root_.one_zpow]
  have hsum : ∑ i : Fin N, omegaRoot N ^ (d * (i : ℕ)) = ∑ i ∈ Finset.range N, z ^ i := by
    rw [Fin.sum_univ_eq_sum_range (fun i => omegaRoot N ^ (d * (i : ℕ)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz, ← _root_.zpow_natCast (omegaRoot N ^ d) i, ← _root_.zpow_mul]
  rw [hsum, geom_sum_eq hz1, hzN, sub_self, zero_div]

