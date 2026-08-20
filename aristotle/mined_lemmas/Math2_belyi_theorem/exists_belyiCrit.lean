import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma exists_belyiCrit {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ a b : ℕ, belyiCrit a b = lam := by
  have hnum : 0 < lam.num := Rat.num_pos.2 h0
  have hlt : lam.num < (lam.den : ℤ) := Rat.lt_one_iff_num_lt_denom.mp h1
  set p : ℕ := lam.num.toNat with hp
  have hpnum : (p : ℤ) = lam.num := Int.toNat_of_nonneg (le_of_lt hnum)
  have hp1 : 1 ≤ p := by omega
  have hpq : p + 1 ≤ lam.den := by omega
  refine ⟨p - 1, lam.den - p - 1, ?_⟩
  have hn1 : (p - 1) + 1 = p := by omega
  have hn2 : (p - 1) + (lam.den - p - 1) + 2 = lam.den := by omega
  have hcast1 : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) hn1
  have hcast2 : ((p - 1 : ℕ) : ℚ) + ((lam.den - p - 1 : ℕ) : ℚ) + 2 = (lam.den : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) hn2
  rw [belyiCrit, hcast1, hcast2, show (p:ℚ) = (lam.num : ℚ) by exact_mod_cast hpnum]
  exact Rat.num_div_den lam

