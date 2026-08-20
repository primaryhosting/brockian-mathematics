import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem rank_ofNat (n : ℕ) : PSet.rank (PSet.ofNat n) = (n : Ordinal) := by
  induction n with
  | zero => exact PSet.rank_empty
  | succ n ih =>
    rw [PSet.ofNat, PSet.rank_insert, ih, max_eq_left (Order.le_succ _), Order.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one]

