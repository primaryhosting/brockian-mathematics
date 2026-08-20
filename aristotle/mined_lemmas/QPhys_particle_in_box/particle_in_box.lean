/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain comment and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Real

/-- The (unnormalized-constant times) `n`-th stationary state of the infinite square
well of width `L`: `ψ n x = c * sin (n π x / L)`. -/

theorem particle_in_box (hbar m L : ℝ) (hm : m ≠ 0) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    psi L n 0 = 0 ∧ psi L n L = 0 ∧ (∫ x in (0:ℝ)..L, (psi L n x) ^ 2) = 1 ∧
      ∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x
        = E hbar m L n * psi L n x := by
  refine ⟨by simp [psi], ?_, psi_normalized L hL n hn, ?_⟩
  · have : (n : ℝ) * π * L / L = n * π := by field_simp
    rw [psi, this, Real.sin_nat_mul_pi]
    ring
  · intro x
    rw [deriv2_psi, E]
    have hL' : L ≠ 0 := ne_of_gt hL
    field_simp

/-- Every energy level `E_n` with `n ≥ 1` is positive (for `m, L > 0` and `ℏ ≠ 0`);
in particular the ground state energy `E_1 = π²ℏ²/(2mL²)` is nonzero. -/
