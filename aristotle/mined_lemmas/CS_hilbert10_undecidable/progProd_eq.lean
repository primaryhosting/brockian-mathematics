import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem progProd_eq (y b m : ℕ) (hb : 0 < b) (hm : y ≤ m)
    (hcong : b * m ≡ 1 + y * b [MOD (b * (1 + y * b) ^ (y + 1) + 1)]) :
    progProd y b = (b ^ y * m.descFactorial y) % (b * (1 + y * b) ^ (y + 1) + 1) := by
  set M := b * (1 + y * b) ^ (y + 1) + 1 with hM
  have hZ : ((b ^ y * m.descFactorial y : ℕ) : ℤ)
      = ∏ j ∈ Finset.range y, ((b : ℤ) * m - j * b) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    have hbp : (b : ℤ) ^ y = ∏ _j ∈ Finset.range y, (b : ℤ) := by simp
    rw [hbp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have hjm : j ≤ m := by omega
    have hc : ((m - j : ℕ) : ℤ) = (m : ℤ) - j := by push_cast [hjm]; omega
    rw [hc]; ring
  have hc : ((b * m : ℕ) : ℤ) ≡ ((1 + y * b : ℕ) : ℤ) [ZMOD (M : ℤ)] :=
    Int.natCast_modEq_iff.mpr hcong
  push_cast at hc
  have hprod : ∏ j ∈ Finset.range y, ((b : ℤ) * m - j * b)
      ≡ ∏ j ∈ Finset.range y, ((1 + (y : ℤ) * b) - j * b) [ZMOD (M : ℤ)] :=
    Int.ModEq.prod fun j _ => Int.ModEq.sub hc (Int.ModEq.refl _)
  have hrefl : ∏ j ∈ Finset.range y, ((1 + (y : ℤ) * b) - j * b) = ((progProd y b : ℕ) : ℤ) := by
    unfold progProd
    push_cast
    rw [← Finset.prod_range_reflect (fun k => (1 : ℤ) + ((k : ℤ) + 1) * b) y]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have h1 : ((y - 1 - j : ℕ) : ℤ) = (y : ℤ) - 1 - j := by
      have : j ≤ y - 1 := by omega
      push_cast [this]
      omega
    rw [h1]; ring
  have hfinal : ((progProd y b : ℕ) : ℤ) ≡ ((b ^ y * m.descFactorial y : ℕ) : ℤ) [ZMOD (M : ℤ)] := by
    rw [hZ, ← hrefl]; exact hprod.symm
  have hnat : progProd y b ≡ b ^ y * m.descFactorial y [MOD M] := Int.natCast_modEq_iff.mp hfinal
  have hlt := progProd_lt y b hb
  unfold Nat.ModEq at hnat
  rw [← hnat, Nat.mod_eq_of_lt (by omega)]

/-- The auxiliary variable in the Diophantine description of `progProd` always exists. -/
