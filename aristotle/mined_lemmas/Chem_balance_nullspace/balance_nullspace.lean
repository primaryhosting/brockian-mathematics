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
