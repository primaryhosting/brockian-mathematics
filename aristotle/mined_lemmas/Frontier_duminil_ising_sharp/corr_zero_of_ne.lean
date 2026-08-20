/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/

theorem corr_zero_of_ne (J : V → V → ℝ) {x y : V} (hxy : x ≠ y) : corr 0 J x y = 0 := by
  have hnum : (∑ σ : V → Bool, weight 0 J σ * (spin (σ x) * spin (σ y))) = 0 := by
    simp only [weight, zero_mul, Real.exp_zero, one_mul]
    set e := (spin_flip_involutive (V := V) x).toPerm _ with he
    have key : (∑ σ : V → Bool, (spin (σ x) * spin (σ y)))
        = ∑ σ : V → Bool, (spin ((e σ) x) * spin ((e σ) y)) :=
      (Equiv.sum_comp e (fun σ => spin (σ x) * spin (σ y))).symm
    have h2 : ∀ σ : V → Bool, spin ((e σ) x) * spin ((e σ) y) = -(spin (σ x) * spin (σ y)) := by
      intro σ
      have hx : (e σ) x = !(σ x) := by simp [he, Function.Involutive.toPerm, Function.update]
      have hy : (e σ) y = σ y := by
        simp [he, Function.Involutive.toPerm, Function.update, (Ne.symm hxy)]
      rw [hx, hy]
      cases σ x <;> cases σ y <;> norm_num [spin]
    have h3 : (∑ σ : V → Bool, spin ((e σ) x) * spin ((e σ) y))
        = -∑ σ : V → Bool, spin (σ x) * spin (σ y) := by
      simp only [h2, Finset.sum_neg_distrib]
    linarith [key.trans h3]
  rw [corr, hnum, zero_div]

/-- The maximal two-point function between the origin `o` and the vertices at
distance `n` (the quantity whose decay is at stake in sharpness). -/
