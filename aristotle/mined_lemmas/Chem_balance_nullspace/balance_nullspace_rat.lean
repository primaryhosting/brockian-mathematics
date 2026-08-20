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

set_option grind.warning false

namespace Chem

/-- A chemical reaction over `m` chemical elements and `n` chemical species.

`comp i e` is the number of atoms of element `e` in one formula unit of species `i`,
and `isProduct i` says whether species `i` sits on the product side of the reaction
(otherwise it is a reactant). -/
structure Reaction (m n : ℕ) where
  /-- `comp i e` = number of atoms of element `e` in one unit of species `i`. -/
  comp : Fin n → Fin m → ℕ
  /-- whether species `i` is on the product side. -/
  isProduct : Fin n → Bool

variable {m n : ℕ}

/-- The stoichiometric matrix of a reaction: rows are elements, columns are species,
the entry being the atom count of the element in the species, signed `+` for products
and `-` for reactants. -/

theorem balance_nullspace_rat (A : Matrix (Fin m) (Fin n) ℤ) :
    (∃ x : Fin n → ℤ, (∀ i, 0 < x i) ∧ A.mulVec x = 0) ↔
      ∃ y : Fin n → ℚ, (∀ i, 0 < y i) ∧ (A.map (fun a : ℤ => (a : ℚ))).mulVec y = 0 := by
  constructor
  · rintro ⟨x, hx, hker⟩
    refine ⟨fun i => (x i : ℚ),
      fun i => by simpa using (by exact_mod_cast hx i : (0:ℚ) < (x i : ℚ)), ?_⟩
    funext e
    have h : ∑ i, A e i * x i = 0 := congrFun hker e
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, Pi.zero_apply]
    have h' : ((∑ i, A e i * x i : ℤ) : ℚ) = 0 := by rw [h]; norm_num
    push_cast at h'
    exact h'
  · rintro ⟨y, hy, hker⟩
    set d : ℕ := ∏ i, (y i).den with hd
    have hdpos : 0 < d := Finset.prod_pos (fun j _ => (y j).pos)
    have key : ∀ i, ∃ z : ℤ, 0 < z ∧ ((z : ℚ) = (d : ℚ) * y i) := by
      intro i
      have hdvd : (y i).den ∣ d := Finset.dvd_prod_of_mem (fun i => (y i).den) (Finset.mem_univ i)
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c * (y i).num, ?_, ?_⟩
      · have hnum : 0 < (y i).num := Rat.num_pos.mpr (hy i)
        have hc0 : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h | h
          · rw [h, Nat.mul_zero] at hc; omega
          · exact h
        positivity
      · have h1 := Rat.mul_den_eq_num (y i)
        rw [hc]
        push_cast
        nlinarith [h1]
    choose z hzpos hzeq using key
    refine ⟨z, hzpos, ?_⟩
    funext e
    have h : ∑ i, ((A e i : ℚ)) * y i = 0 := by
      have := congrFun hker e
      simpa [Matrix.mulVec, Matrix.map_apply, dotProduct] using this
    have h2 : ((∑ i, A e i * z i : ℤ) : ℚ) = 0 := by
      push_cast
      have hstep : ∑ i, (A e i : ℚ) * (z i : ℚ) = (d : ℚ) * ∑ i, (A e i : ℚ) * y i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hzeq i]; ring
      rw [hstep, h, mul_zero]
    have h3 : ∑ i, A e i * z i = 0 := by exact_mod_cast h2
    simpa [Matrix.mulVec, dotProduct] using h3

/-- A reaction balances iff its stoichiometric matrix has a strictly positive rational
null vector. -/
