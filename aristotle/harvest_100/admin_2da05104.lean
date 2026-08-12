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
def Reaction.stoich (R : Reaction m n) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun e i => (if R.isProduct i then (1 : ℤ) else -1) * (R.comp i e : ℤ)

/-- A reaction *balances* if one can attach a strictly positive integer coefficient to
every species so that, for each chemical element, the total number of atoms among the
reactants equals the total number of atoms among the products. -/
def Reaction.Balances (R : Reaction m n) : Prop :=
  ∃ x : Fin n → ℤ, (∀ i, 0 < x i) ∧
    ∀ e : Fin m,
      ∑ i ∈ Finset.univ.filter (fun i => ¬ R.isProduct i), x i * (R.comp i e : ℤ) =
      ∑ i ∈ Finset.univ.filter (fun i => R.isProduct i), x i * (R.comp i e : ℤ)

/-- **Balancing a chemical reaction = finding a positive integer null vector of the
stoichiometric matrix.** -/
theorem balance_nullspace (R : Reaction m n) :
    R.Balances ↔ ∃ x : Fin n → ℤ, (∀ i, 0 < x i) ∧ R.stoich.mulVec x = 0 := by
  constructor
  · rintro ⟨x, hx, hbal⟩
    refine ⟨x, hx, ?_⟩
    funext e
    have h := hbal e
    simp only [Matrix.mulVec, Reaction.stoich, Matrix.of_apply, dotProduct, Pi.zero_apply]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => R.isProduct i)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => R.isProduct i),
        (if R.isProduct i then (1 : ℤ) else -1) * (R.comp i e : ℤ) * x i =
        ∑ i ∈ Finset.univ.filter (fun i => R.isProduct i), x i * (R.comp i e : ℤ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
      ring
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ R.isProduct i),
        (if R.isProduct i then (1 : ℤ) else -1) * (R.comp i e : ℤ) * x i =
        -∑ i ∈ Finset.univ.filter (fun i => ¬ R.isProduct i), x i * (R.comp i e : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
      ring
    rw [h1, h2, h]
    ring
  · rintro ⟨x, hx, hker⟩
    refine ⟨x, hx, ?_⟩
    intro e
    have h : ∑ i, R.stoich e i * x i = 0 := congrFun hker e
    simp only [Reaction.stoich, Matrix.of_apply] at h
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => R.isProduct i)] at h
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => R.isProduct i),
        (if R.isProduct i then (1 : ℤ) else -1) * (R.comp i e : ℤ) * x i =
        ∑ i ∈ Finset.univ.filter (fun i => R.isProduct i), x i * (R.comp i e : ℤ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
      ring
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ R.isProduct i),
        (if R.isProduct i then (1 : ℤ) else -1) * (R.comp i e : ℤ) * x i =
        -∑ i ∈ Finset.univ.filter (fun i => ¬ R.isProduct i), x i * (R.comp i e : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
      ring
    rw [h1, h2] at h
    linarith

/-- Rational relaxation: an integer stoichiometric matrix has a strictly positive *integer*
null vector iff it has a strictly positive *rational* one (clear denominators). -/
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
theorem balance_nullspace_rat_of_reaction (R : Reaction m n) :
    R.Balances ↔ ∃ y : Fin n → ℚ, (∀ i, 0 < y i) ∧
      ((R.stoich.map (fun a : ℤ => (a : ℚ))).mulVec y = 0) :=
  (balance_nullspace R).trans (balance_nullspace_rat R.stoich)

/-! ### Sanity checks: the notions are not vacuous -/

/-- `2 H₂ + O₂ → 2 H₂O`, with element `0 = H` and element `1 = O`,
species `0 = H₂`, `1 = O₂`, `2 = H₂O`. -/
def water : Reaction 2 3 where
  comp := ![![2, 0], ![0, 2], ![2, 1]]
  isProduct := ![false, false, true]

example : water.Balances := by
  refine ⟨![2, 1, 2], ?_, ?_⟩
  · decide
  · decide

/-- `H₂ → O₂` cannot be balanced. -/
def bogus : Reaction 2 2 where
  comp := ![![2, 0], ![0, 2]]
  isProduct := ![false, true]

example : ¬ bogus.Balances := by
  rintro ⟨x, hx, hbal⟩
  have h := hbal 0
  have h0 := hx 0
  simp only [Finset.sum_filter, Fin.sum_univ_two] at h
  simp [bogus] at h
  omega

end Chem

