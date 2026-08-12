import Mathlib

/-!
# Balancing chemical reactions and the null space of the stoichiometric matrix

A chemical reaction is given by a family of reactant species and a family of product
species, together with the atom counts of each chemical element in each species
(`R e j` = number of atoms of element `e` in reactant `j`, and likewise `P e k` for the
products).

The reaction *balances* if one can choose strictly positive integer stoichiometric
coefficients for the reactants and the products so that, for each element, the total
number of atoms among the reactants equals the total number among the products.

The *stoichiometric matrix* is the integer matrix whose columns are indexed by all
species, with reactant columns given by the atom counts and product columns given by
the negated atom counts.

The main theorem `Chem.balance_nullspace` states that a reaction balances if and only
if its stoichiometric matrix has a strictly positive integer null vector.

We also record `Chem.exists_pos_int_nullVec_iff_exists_pos_rat_nullVec`: an integer
matrix has a strictly positive integer null vector iff it has a strictly positive
rational one (clearing denominators).
-/

namespace Chem

open Finset

variable {ε ρ π : Type*} [Fintype ρ] [Fintype π]

/-- The stoichiometric matrix of a reaction with reactant atom-count matrix `R` and
product atom-count matrix `P`: reactant columns carry the atom counts, product columns
carry the negated atom counts. -/
def stoich (R : Matrix ε ρ ℕ) (P : Matrix ε π ℕ) : Matrix ε (ρ ⊕ π) ℤ :=
  Matrix.of fun e s => Sum.elim (fun j => (R e j : ℤ)) (fun k => -(P e k : ℤ)) s

/-- A reaction balances: there are strictly positive integer coefficients for the
reactants and the products making the atom counts of every element agree on both
sides. -/
def Balances (R : Matrix ε ρ ℕ) (P : Matrix ε π ℕ) : Prop :=
  ∃ (a : ρ → ℤ) (b : π → ℤ), (∀ j, 0 < a j) ∧ (∀ k, 0 < b k) ∧
    ∀ e, ∑ j, a j * (R e j : ℤ) = ∑ k, b k * (P e k : ℤ)

/-- A strictly positive integer vector in the kernel of a matrix. -/
def HasPosNullVec {m n : Type*} [Fintype n] (A : Matrix m n ℤ) : Prop :=
  ∃ x : n → ℤ, (∀ i, 0 < x i) ∧ A.mulVec x = 0

/-- The entries of a matrix-vector product, as a sum. -/
theorem mulVec_apply' {m n R : Type*} [Fintype n] [NonUnitalNonAssocSemiring R]
    (A : Matrix m n R) (x : n → R) (e : m) : A.mulVec x e = ∑ j, A e j * x j := by
  simp [Matrix.mulVec, dotProduct]

/-- The stoichiometric equation for a single element, written out. -/
theorem stoich_mulVec_apply (R : Matrix ε ρ ℕ) (P : Matrix ε π ℕ)
    (a : ρ → ℤ) (b : π → ℤ) (e : ε) :
    (stoich R P).mulVec (Sum.elim a b) e
      = (∑ j, a j * (R e j : ℤ)) - ∑ k, b k * (P e k : ℤ) := by
  rw [mulVec_apply']
  rw [Fintype.sum_sum_type]
  simp only [stoich, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun k _ => by ring

/-- **A chemical reaction balances iff its stoichiometric matrix has a strictly
positive integer null vector.** -/
theorem balance_nullspace (R : Matrix ε ρ ℕ) (P : Matrix ε π ℕ) :
    Balances R P ↔ HasPosNullVec (stoich R P) := by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    refine ⟨Sum.elim a b, ?_, ?_⟩
    · rintro (j | k)
      · exact ha j
      · exact hb k
    · funext e
      rw [stoich_mulVec_apply, h e]
      simp
  · rintro ⟨x, hx, h0⟩
    refine ⟨fun j => x (Sum.inl j), fun k => x (Sum.inr k), fun j => hx _, fun k => hx _, ?_⟩
    intro e
    have hxe : x = Sum.elim (fun j => x (Sum.inl j)) (fun k => x (Sum.inr k)) := by
      funext s; cases s <;> rfl
    have := congrFun h0 e
    rw [hxe, stoich_mulVec_apply] at this
    have h0' : (0 : (ε → ℤ)) e = 0 := rfl
    rw [h0'] at this
    linarith [sub_eq_zero.mp this]

/-- Clearing denominators: an integer matrix has a strictly positive integer null vector
iff it has a strictly positive rational null vector. -/
theorem exists_pos_int_nullVec_iff_exists_pos_rat_nullVec
    {m n : Type*} [Fintype n] (A : Matrix m n ℤ) :
    HasPosNullVec A ↔
      ∃ v : n → ℚ, (∀ i, 0 < v i) ∧ (A.map (Int.cast : ℤ → ℚ)).mulVec v = 0 := by
  constructor
  · rintro ⟨x, hx, h0⟩
    refine ⟨fun i => (x i : ℚ), fun i => by simpa using (by exact_mod_cast hx i : (0:ℚ) < (x i : ℚ)), ?_⟩
    funext e
    have hE : ∑ i, A e i * x i = 0 := by
      rw [← mulVec_apply']; exact congrFun h0 e
    have : ((∑ i, A e i * x i : ℤ) : ℚ) = 0 := by rw [hE]; simp
    push_cast at this
    rw [mulVec_apply']
    simpa [Matrix.map_apply] using this
  · rintro ⟨v, hv, h0⟩
    classical
    set d : ℤ := ∏ i : n, ((v i).den : ℤ) with hd
    have hdpos : 0 < d := by
      refine Finset.prod_pos fun i _ => ?_
      exact_mod_cast (v i).pos
    have hdvd : ∀ i : n, ((v i).den : ℤ) ∣ d := fun i =>
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have key : ∀ i : n, ∃ z : ℤ, (z : ℚ) = v i * (d : ℚ) := by
      intro i
      obtain ⟨c, hc⟩ := hdvd i
      refine ⟨(v i).num * c, ?_⟩
      have hnum : v i * ((v i).den : ℚ) = ((v i).num : ℚ) := by
        exact_mod_cast Rat.mul_den_eq_num (v i)
      push_cast [hc]
      rw [show v i * (((v i).den : ℚ) * (c : ℚ)) = (v i * ((v i).den : ℚ)) * (c : ℚ) by ring,
        hnum]
    choose z hz using key
    refine ⟨z, ?_, ?_⟩
    · intro i
      have hpos : (0 : ℚ) < (z i : ℚ) := by
        rw [hz i]
        exact mul_pos (hv i) (by exact_mod_cast hdpos)
      exact_mod_cast hpos
    · funext e
      have hE : ∑ i, ((A e i : ℚ)) * v i = 0 := by
        have := congrFun h0 e
        rw [mulVec_apply'] at this
        simpa [Matrix.map_apply] using this
      have hQ : ((∑ i, A e i * z i : ℤ) : ℚ) = 0 := by
        push_cast
        simp_rw [hz]
        rw [show ∑ i, (A e i : ℚ) * (v i * (d : ℚ))
              = (∑ i, (A e i : ℚ) * v i) * (d : ℚ) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring]
        rw [hE, zero_mul]
      have : (∑ i, A e i * z i) = 0 := by exact_mod_cast hQ
      rw [mulVec_apply']
      simpa using this

/-! ### A worked example: `2 H₂ + O₂ → 2 H₂O` -/

/-- Reactant atom counts for `H₂` and `O₂`, with elements `H` (index `0`) and
`O` (index `1`). -/
def waterReactants : Matrix (Fin 2) (Fin 2) ℕ := !![2, 0; 0, 2]

/-- Product atom counts for `H₂O`. -/
def waterProducts : Matrix (Fin 2) (Fin 1) ℕ := !![2; 1]

/-- The reaction `2 H₂ + O₂ → 2 H₂O` balances, and hence (by `balance_nullspace`) its
stoichiometric matrix has a strictly positive integer null vector. -/
theorem water_balances : Balances waterReactants waterProducts := by
  refine ⟨![2, 1], ![2], ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

theorem water_hasPosNullVec : HasPosNullVec (stoich waterReactants waterProducts) :=
  (balance_nullspace _ _).mp water_balances

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

