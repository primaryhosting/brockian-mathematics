/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

lemma wavenumber_quantized {L k : ℝ} (hL : 0 < L) (hk : 0 < k) (h : Real.sin (k * L) = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ k = n * Real.pi / L := by
  obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp h
  have hzpos : 0 < (z : ℝ) := by
    have hkl : 0 < k * L := mul_pos hk hL
    nlinarith [Real.pi_pos]
  have hz1 : 1 ≤ z := by exact_mod_cast hzpos
  refine ⟨z.toNat, ?_, ?_⟩
  · omega
  · have : ((z.toNat : ℤ) : ℝ) = (z : ℝ) := by
      rw [Int.toNat_of_nonneg (by omega)]
    push_cast at this ⊢
    rw [this]
    field_simp
    linarith [hz]

/-- **Particle in a box.**  For a well of width `L > 0`, mass `m > 0` and reduced Planck
constant `ℏ > 0`:

1. the state `ψ_n(x) = √(2/L)·sin(nπx/L)` satisfies the box boundary conditions
   `ψ_n(0) = ψ_n(L) = 0`;
2. it solves the time-independent Schrödinger equation
   `-ℏ²/(2m) ψ_n'' = E_n ψ_n` with `E_n = n²π²ℏ²/(2mL²)`;
3. conversely, any positive wave number `k` for which `sin(k·)` vanishes at `x = L`
   (i.e. any solution of the free equation obeying both boundary conditions) has
   energy `ℏ²k²/(2m) = E_n` for some `n ≥ 1`;
4. the energies are strictly increasing in `n`, and positive for `n ≥ 1`. -/
