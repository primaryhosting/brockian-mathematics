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
