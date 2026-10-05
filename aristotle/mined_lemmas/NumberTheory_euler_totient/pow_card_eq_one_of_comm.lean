/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace NumberTheory

/-- The group of units of `ZMod n` has order `Nat.totient n`, for `n > 0`. -/

theorem pow_card_eq_one_of_comm {G : Type*} [CommGroup G] [Fintype G] (u : G) :
    u ^ Fintype.card G = 1 := by
  have hperm : ∏ x : G, (u * x) = ∏ x : G, x :=
    Equiv.prod_comp (Equiv.mulLeft u) (fun x => x)
  have hsplit : ∏ x : G, (u * x) = u ^ Fintype.card G * ∏ x : G, x := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have : u ^ Fintype.card G * ∏ x : G, x = 1 * ∏ x : G, x := by
    rw [one_mul, ← hsplit, hperm]
  exact mul_right_cancel this

/-- **Euler's theorem** again, proved without invoking Lagrange's theorem: the argument
goes through the permutation-of-units product identity `pow_card_eq_one_of_comm`. -/
