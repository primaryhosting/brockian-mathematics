/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Statement: A chemical reaction balances iff the stoichiometric matrix has a positive integer null vector.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

variable {m n : ℕ}

/-- `A` is the *stoichiometric matrix* of a reaction: rows are elements, columns are chemical
species, and `A i j` is the (signed) number of atoms of element `i` in species `j`.  A vector
`x` of stoichiometric coefficients *conserves* every element when each row of `A` is orthogonal
to `x`. -/
def Conserves (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) : Prop :=
  ∀ i, ∑ j, A i j * x j = 0

/-- A reaction *balances* when some assignment of strictly positive (rational) stoichiometric
coefficients conserves every element. -/
def Balances (A : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ j, 0 < x j) ∧ Conserves A x

/-- Membership in the null space of the stoichiometric matrix is exactly conservation of every
element. -/
theorem mem_ker_mulVecLin_iff (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) :
    x ∈ LinearMap.ker (Matrix.mulVecLin A) ↔ Conserves A x := by
  simp [Conserves, Matrix.mulVec, dotProduct, funext_iff]

/-- Clearing denominators: a finite family of positive rationals can be scaled by a single
positive integer to a family of positive integers. -/
theorem exists_common_denom (x : Fin n → ℚ) (hx : ∀ j, 0 < x j) :
    ∃ (k : ℤ) (z : Fin n → ℤ), 0 < k ∧ (∀ j, 0 < z j) ∧ ∀ j, (z j : ℚ) = (k : ℚ) * x j := by
  classical
  set K : ℕ := ∏ j, (x j).den with hK
  have hKpos : 0 < K := Finset.prod_pos fun j _ => (x j).pos
  -- for each `j`, choose the cofactor `c j` with `K = (x j).den * c j`
  have hdvd : ∀ j : Fin n, (x j).den ∣ K := fun j =>
    Finset.dvd_prod_of_mem (fun j => (x j).den) (Finset.mem_univ j)
  choose c hc using hdvd
  have hcpos : ∀ j, 0 < c j := by
    intro j
    rcases Nat.eq_zero_or_pos (c j) with h | h
    · exact absurd (hc j) (by simp [h, hKpos.ne'])
    · exact h
  refine ⟨(K : ℤ), fun j => (c j : ℤ) * (x j).num, by exact_mod_cast hKpos, ?_, ?_⟩
  · intro j
    exact mul_pos (by exact_mod_cast hcpos j) (Rat.num_pos.mpr (hx j))
  · intro j
    have h1 : ((K : ℚ)) = ((x j).den : ℚ) * (c j : ℚ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) (hc j)
    have h2 : x j * ((x j).den : ℚ) = ((x j).num : ℚ) := Rat.mul_den_eq_num (x j)
    push_cast
    rw [h1]
    calc (c j : ℚ) * ((x j).num : ℚ)
        = (c j : ℚ) * (x j * ((x j).den : ℚ)) := by rw [h2]
      _ = ((x j).den : ℚ) * (c j : ℚ) * x j := by ring

/-- **A chemical reaction balances iff its stoichiometric matrix has a positive integer null
vector.**  Here `Balances A` says that some strictly positive *rational* coefficient vector
conserves every element; the right-hand side produces strictly positive *integer*
stoichiometric coefficients lying in the null space (kernel) of the stoichiometric matrix. -/
theorem balance_nullspace (A : Matrix (Fin m) (Fin n) ℚ) :
    Balances A ↔ ∃ z : Fin n → ℤ, (∀ j, 0 < z j) ∧
      (fun j => (z j : ℚ)) ∈ LinearMap.ker (Matrix.mulVecLin A) := by
  constructor
  · rintro ⟨x, hxpos, hx⟩
    obtain ⟨k, z, hk, hzpos, hz⟩ := exists_common_denom x hxpos
    refine ⟨z, hzpos, (mem_ker_mulVecLin_iff A _).mpr ?_⟩
    intro i
    have : ∑ j, A i j * (z j : ℚ) = (k : ℚ) * ∑ j, A i j * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hz j]; ring
    rw [this, hx i, mul_zero]
  · rintro ⟨z, hzpos, hz⟩
    exact ⟨fun j => (z j : ℚ), fun j => by simpa using (Int.cast_pos (R := ℚ)).mpr (hzpos j),
      (mem_ker_mulVecLin_iff A _).mp hz⟩

end Chem


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

