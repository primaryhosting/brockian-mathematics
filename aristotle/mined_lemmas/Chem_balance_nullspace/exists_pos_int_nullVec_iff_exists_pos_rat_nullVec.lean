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
