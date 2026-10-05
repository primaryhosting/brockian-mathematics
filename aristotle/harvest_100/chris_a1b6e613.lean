/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Balance Nullspace

Category: Chemistry
Target: `Chem.balance_nullspace`
Provenance: Aristotle theorem prover (Harmonic)

A chemical reaction is encoded by its stoichiometric matrix `A` (rows = chemical elements,
columns = chemical species, `A i j` = signed number of atoms of element `i` in species `j`).
The reaction *balances* when the species can be given strictly positive amounts so that every
element is conserved.  A priori those amounts are arbitrary positive numbers (a chemist solving
the linear system by Gaussian elimination gets rational ones), whereas a chemical equation must
be written with positive *integer* coefficients.

`Chem.balance_nullspace` says these two notions agree: a reaction balances if and only if its
stoichiometric matrix has a strictly positive integer null vector.  The nontrivial direction
clears denominators, multiplying a positive rational solution by the product of its
denominators.
-/

namespace Chem

variable {m n : ℕ}

/-- A reaction with stoichiometric matrix `A` *balances* if strictly positive (rational)
amounts of the species can be chosen so that every element is conserved. -/
def Balances (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ j, 0 < x j) ∧ ∀ i, ∑ j, (A i j : ℚ) * x j = 0

/-- `A` has a strictly positive integer null vector: the coefficients of a written-out
balanced chemical equation. -/
def HasPosIntNullVector (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℤ, (∀ j, 0 < x j) ∧ A.mulVec x = 0

/-- Auxiliary: multiplying a rational by a multiple of its denominator gives an integer. -/
lemma exists_int_mul_den_dvd (q : ℚ) (d : ℕ) (h : (q.den : ℕ) ∣ d) :
    ∃ z : ℤ, (z : ℚ) = q * d := by
  obtain ⟨k, hk⟩ := h
  refine ⟨q.num * k, ?_⟩
  push_cast [hk]
  rw [← mul_assoc, Rat.mul_den_eq_num]

/-- **Balance nullspace theorem.**  A chemical reaction balances if and only if its
stoichiometric matrix has a strictly positive integer null vector. -/
theorem balance_nullspace (A : Matrix (Fin m) (Fin n) ℤ) :
    Balances A ↔ HasPosIntNullVector A := by
  constructor
  · rintro ⟨x, hx, hA⟩
    -- clear denominators with the product of all denominators
    set d : ℕ := ∏ j, (x j).den with hd
    have hdpos : 0 < d := Finset.prod_pos fun j _ => (x j).pos
    have hdvd : ∀ j, ((x j).den : ℕ) ∣ d := fun j =>
      Finset.dvd_prod_of_mem (fun j => (x j).den) (Finset.mem_univ j)
    choose y hy using fun j => exists_int_mul_den_dvd (x j) d (hdvd j)
    have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hdpos
    refine ⟨y, fun j => ?_, ?_⟩
    · have hpos : (0 : ℚ) < (y j : ℚ) := by rw [hy j]; exact mul_pos (hx j) hdQ
      exact_mod_cast hpos
    · funext i
      have hcast : ((∑ j, A i j * y j : ℤ) : ℚ) = 0 := by
        push_cast
        simp only [hy]
        calc ∑ j, ((A i j : ℚ)) * (x j * (d : ℚ))
            = (∑ j, ((A i j : ℚ)) * x j) * (d : ℚ) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by rw [hA i, zero_mul]
      have h0 : ∑ j, A i j * y j = 0 := by exact_mod_cast hcast
      simpa [Matrix.mulVec, dotProduct] using h0
  · rintro ⟨x, hx, hA⟩
    refine ⟨fun j => (x j : ℚ), fun j => ?_, fun i => ?_⟩
    · show (0 : ℚ) < ((x j : ℤ) : ℚ)
      exact_mod_cast hx j
    · have hi : ∑ j, A i j * x j = 0 := by
        have := congrFun hA i
        simpa [Matrix.mulVec, dotProduct] using this
      have : ((∑ j, A i j * x j : ℤ) : ℚ) = 0 := by rw [hi]; norm_num
      push_cast at this
      exact this

/-! ### Worked examples

These show that both sides of `balance_nullspace` are non-vacuous: a genuine reaction balances,
and an impossible one does not. -/

/-- Stoichiometric matrix of `a H₂ + b O₂ → c H₂O`: rows are the elements H, O, columns are the
species H₂, O₂, H₂O, with products entered negatively. -/
def waterMatrix : Matrix (Fin 2) (Fin 3) ℤ := !![2, 0, -2; 0, 2, -1]

/-- The synthesis of water balances: `2 H₂ + O₂ → 2 H₂O`. -/
theorem waterMatrix_balances : Balances waterMatrix := by
  rw [balance_nullspace]
  refine ⟨![2, 1, 2], by decide, ?_⟩
  funext i
  fin_cases i <;> simp [waterMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Stoichiometric matrix of the impossible "reaction" `a H₂ + b O₂ → ` (nothing). -/
def noProductMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 2]

/-- A reaction consuming H₂ and O₂ and producing nothing cannot balance. -/
theorem noProductMatrix_not_balances : ¬ Balances noProductMatrix := by
  rintro ⟨x, hx, h⟩
  have h0 := h 0
  have hx0 := hx 0
  simp [noProductMatrix, Fin.sum_univ_succ] at h0
  simp_all

end Chem

import Mathlib

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

