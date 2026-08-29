/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

lemma mixedProfiles_convex : Convex ℝ (mixedProfiles S) := by
  intro x hx y hy a b ha hb hab i
  refine ⟨fun s => ?_, ?_⟩
  · have := (hx i).1 s
    have := (hy i).1 s
    have h1 : 0 ≤ a * x i s := mul_nonneg ha ((hx i).1 s)
    have h2 : 0 ≤ b * y i s := mul_nonneg hb ((hy i).1 s)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hx i).2, (hy i).2,
      mul_one, mul_one, hab]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
