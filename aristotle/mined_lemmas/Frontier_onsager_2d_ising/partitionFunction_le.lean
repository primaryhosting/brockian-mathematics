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

/-- Sites of the `m × n` square lattice with periodic (toroidal) boundary conditions. -/
abbrev Site (m n : ℕ) : Type := ZMod m × ZMod n

/-- A spin configuration: a `± 1` value (encoded as a `Bool`) at every lattice site. -/
abbrev Config (m n : ℕ) : Type := Site m n → Bool

/-- The real spin value attached to a `Bool`. -/

theorem partitionFunction_le {m n : ℕ} [NeZero m] [NeZero n] (K : ℝ) :
    partitionFunction m n K ≤ 2 ^ (m * n) * Real.exp (2 * |K| * (m * n)) := by
  have h : ∀ σ : Config m n, Real.exp (K * bondSum σ) ≤ Real.exp (2 * |K| * (m * n)) := by
    intro σ
    apply Real.exp_le_exp.mpr
    calc K * bondSum σ ≤ |K * bondSum σ| := le_abs_self _
      _ = |K| * |bondSum σ| := abs_mul _ _
      _ ≤ |K| * (2 * (m * n)) := by
          exact mul_le_mul_of_nonneg_left (abs_bondSum_le σ) (abs_nonneg K)
      _ = 2 * |K| * (m * n) := by ring
  calc partitionFunction m n K ≤ ∑ _σ : Config m n, Real.exp (2 * |K| * (m * n)) :=
        Finset.sum_le_sum fun σ _ => h σ
    _ = 2 ^ (m * n) * Real.exp (2 * |K| * (m * n)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_config]
        push_cast
        ring

