import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

theorem abs_isingEnergy_le (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ)
    (σ : ZMod m × ZMod n → Bool) :
    |isingEnergy m n J σ| ≤ 2 * (m * n) * |J| := by
  have hS : |∑ p : ZMod m × ZMod n,
      (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))|
      ≤ 2 * ((m : ℝ) * n) := by
    calc |∑ p : ZMod m × ZMod n,
            (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))|
        ≤ ∑ p : ZMod m × ZMod n,
            |spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : ZMod m × ZMod n, (2 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro p _
          calc |spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1))|
              ≤ |spin (σ p) * spin (σ (p.1 + 1, p.2))| + |spin (σ p) * spin (σ (p.1, p.2 + 1))| :=
                abs_add_le _ _
            _ = 2 := by simp [abs_mul, abs_spin]; ring
      _ = 2 * ((m : ℝ) * n) := by
          simp [Finset.card_univ, ZMod.card]
          ring
  rw [isingEnergy, abs_mul, abs_neg]
  calc |J| * |∑ p : ZMod m × ZMod n,
      (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))|
      ≤ |J| * (2 * ((m : ℝ) * n)) := mul_le_mul_of_nonneg_left hS (abs_nonneg J)
    _ = 2 * ((m : ℝ) * n) * |J| := by ring

/-- Uniform bounds on the finite-volume free energy density, valid at every temperature. -/
