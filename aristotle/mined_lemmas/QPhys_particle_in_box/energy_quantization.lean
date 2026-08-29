import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace QPhys

/-- The `n`-th stationary state of the infinite square well of width `L`:
`ψ_n(x) = sin (n π x / L)` (unnormalized). -/

theorem energy_quantization (m L : ℝ) (hL : 0 < L) (k : ℝ) (hk : 0 < k) :
    Real.sin (k * L) = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ k = n * Real.pi / L := by
  constructor
  · intro h
    rw [Real.sin_eq_zero_iff] at h
    obtain ⟨z, hz⟩ := h
    have hzpos : 0 < (z : ℝ) := by
      by_contra hc
      push_neg at hc
      have : (z : ℝ) * Real.pi ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc Real.pi_pos.le
      nlinarith
    have hz1 : 1 ≤ z := by exact_mod_cast hzpos
    refine ⟨z.toNat, ?_, ?_⟩
    · omega
    · have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
        have hz0 : (0:ℤ) ≤ z := by omega
        exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) (Int.toNat_of_nonneg hz0)
      rw [hcast, eq_div_iff hL.ne']
      exact hz.symm
  · rintro ⟨n, hn, rfl⟩
    have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
    rw [this, Real.sin_nat_mul_pi]

/-- The admissible energies, written out: if `k = n π / L` then `ℏ² k² / (2 m) = E_n`. -/
