import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem exists_ratio (l : ℚ) (h0 : 0 < l) (h1 : l < 1) :
    ∃ m n : ℕ, l = ((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) := by
  have hnum : 0 < l.num := Rat.num_pos.mpr h0
  have hdq : (0 : ℚ) < (l.den : ℚ) := by exact_mod_cast l.pos
  have hlt : l.num < (l.den : ℤ) := by
    rw [← Rat.num_div_den l, div_lt_one hdq] at h1
    exact_mod_cast h1
  set a : ℕ := l.num.toNat with ha
  have ha1 : 1 ≤ a := by omega
  have had : a + 1 ≤ l.den := by omega
  refine ⟨a - 1, l.den - a - 1, ?_⟩
  have e1 : (a - 1 : ℕ) + 1 = a := by omega
  have e2 : (a - 1 : ℕ) + (l.den - a - 1 : ℕ) + 2 = l.den := by omega
  have hm : ((a - 1 : ℕ) : ℚ) + 1 = (a : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) e1
  have hd : ((a - 1 : ℕ) : ℚ) + ((l.den - a - 1 : ℕ) : ℚ) + 2 = (l.den : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) e2
  rw [hm, hd]
  have hna : (a : ℚ) = (l.num : ℚ) := by
    rw [ha]; exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) (Int.toNat_of_nonneg hnum.le)
  rw [hna]
  exact (Rat.num_div_den l).symm

/-- The identity is a Belyi map for any set of points already lying in `{0,1}`. -/
