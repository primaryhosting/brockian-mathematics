/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem exists_schmidt (psi : A → B → ℂ) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → A → ℂ) (v : Fin r → B → ℂ),
      IsSchmidtDecomposition psi s u v := by
  classical
  obtain ⟨w, mu, hw1, hw2, hw3⟩ := exists_eigen_data psi
  set y : B → A → ℂ := fun j i => ∑ b, psi i b * w j b with hy
  -- the vectors `y j = psi *ᵥ w j` are orthogonal with squared norms the eigenvalues
  have hyy : ∀ k l, ∑ i, conj (y k i) * y l i = (mu l : ℂ) * (if k = l then 1 else 0) := by
    intro k l
    have e0 : ∀ i, conj (y k i) * y l i
        = ∑ a, ∑ b, (conj (psi i a) * conj (w k a)) * (psi i b * w l b) := by
      intro i
      show (conj (∑ b, psi i b * w k b)) * (∑ b, psi i b * w l b) = _
      rw [map_sum]
      simp only [map_mul]
      exact sum_mul_sum_expand _ _
    calc ∑ i, conj (y k i) * y l i
        = ∑ i, ∑ a, ∑ b, (conj (psi i a) * conj (w k a)) * (psi i b * w l b) :=
          Finset.sum_congr rfl fun i _ => e0 i
      _ = ∑ a, ∑ b, ∑ i, (conj (psi i a) * conj (w k a)) * (psi i b * w l b) := sum3_comm _
      _ = ∑ a, conj (w k a) * ((mu l : ℂ) * w l a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← hw3 l a, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (mu l : ℂ) * (if k = l then 1 else 0) := by
          rw [← hw1 k l, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
  have hnorm : ∀ j, mu j = ∑ i, Complex.normSq (y j i) := by
    intro j
    have h1 : ∑ i, conj (y j i) * y j i = ((mu j : ℝ) : ℂ) := by simpa using hyy j j
    have h2 : ((mu j : ℝ) : ℂ) = ((∑ i, Complex.normSq (y j i) : ℝ) : ℂ) := by
      rw [← h1, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_conj_mul_self).symm
    exact_mod_cast h2
  have hmu : ∀ j, 0 ≤ mu j := by
    intro j
    rw [hnorm j]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hy0 : ∀ j, mu j = 0 → ∀ i, y j i = 0 := by
    intro j hj i
    have h2 : ∑ i, Complex.normSq (y j i) = 0 := by rw [← hnorm j, hj]
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg (y j i))).mp h2 i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp this
  have hrec0 : ∀ i b, psi i b = ∑ j, y j i * conj (w j b) := by
    intro i b
    have e1 : ∑ j, y j i * conj (w j b) = ∑ a, psi i a * (∑ j, w j a * conj (w j b)) := by
      simp only [hy, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]
    simp [hw2]
  -- the Schmidt data, indexed by the positive eigenvalues
  set S := {j : B // 0 < mu j} with hS
  set e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S with he
  have hinj : ∀ k l : Fin (Fintype.card S),
      ((e.symm k : S) : B) = ((e.symm l : S) : B) ↔ k = l := by
    intro k l
    constructor
    · intro hh
      have : e.symm k = e.symm l := Subtype.ext hh
      simpa using congrArg e this
    · rintro rfl; rfl
  have hposk : ∀ k : Fin (Fintype.card S), 0 < Real.sqrt (mu ((e.symm k : S) : B)) :=
    fun k => Real.sqrt_pos.mpr (e.symm k).2
  refine ⟨Fintype.card S, fun k => Real.sqrt (mu ((e.symm k : S) : B)),
    fun k i => ((Real.sqrt (mu ((e.symm k : S) : B)))⁻¹ : ℝ) * y ((e.symm k : S) : B) i,
    fun k b => conj (w ((e.symm k : S) : B) b), hposk, ?_, ?_, ?_⟩
  · -- orthonormality of the `u`'s
    intro k l
    have hstep : ∀ (c d : ℝ) (j j' : B),
        ∑ i, conj ((c : ℂ) * y j i) * ((d : ℂ) * y j' i)
          = (c : ℂ) * (d : ℂ) * ((mu j' : ℂ) * (if j = j' then 1 else 0)) := by
      intro c d j j'
      rw [← hyy j j', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, Complex.conj_ofReal]
      ring
    rw [hstep _ _ _ _]
    by_cases hkl : k = l
    · subst hkl
      have hp := hposk k
      rw [if_pos rfl, if_pos rfl, mul_one]
      have hreal : (Real.sqrt (mu ((e.symm k : S) : B)))⁻¹
          * (Real.sqrt (mu ((e.symm k : S) : B)))⁻¹ * mu ((e.symm k : S) : B) = 1 := by
        have hsq : Real.sqrt (mu ((e.symm k : S) : B)) * Real.sqrt (mu ((e.symm k : S) : B))
            = mu ((e.symm k : S) : B) := Real.mul_self_sqrt (hmu _)
        have hne : Real.sqrt (mu ((e.symm k : S) : B)) ≠ 0 := (hposk k).ne'
        field_simp
        linarith [hsq]
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hreal
    · rw [if_neg hkl, if_neg (fun hcon => hkl ((hinj k l).mp hcon))]
      ring
  · -- orthonormality of the `v`'s
    intro k l
    have e2 : ∑ b, conj (conj (w ((e.symm k : S) : B) b)) * conj (w ((e.symm l : S) : B) b)
        = conj (∑ b, conj (w ((e.symm k : S) : B) b) * w ((e.symm l : S) : B) b) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun b _ => by simp
    rw [e2, hw1]
    by_cases hkl : k = l
    · subst hkl; simp
    · rw [if_neg (fun hcon => hkl ((hinj k l).mp hcon)), if_neg hkl, map_zero]
  · -- reconstruction
    intro i b
    have hsum : ∀ k : Fin (Fintype.card S),
        ((Real.sqrt (mu ((e.symm k : S) : B)) : ℝ) : ℂ)
            * (((Real.sqrt (mu ((e.symm k : S) : B)))⁻¹ : ℝ) * y ((e.symm k : S) : B) i)
            * conj (w ((e.symm k : S) : B) b)
          = y ((e.symm k : S) : B) i * conj (w ((e.symm k : S) : B) b) := by
      intro k
      have hp := (hposk k).ne'
      have : ((Real.sqrt (mu ((e.symm k : S) : B)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hp
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hsum k]
    rw [Equiv.sum_comp e.symm (fun j : S => y (j : B) i * conj (w (j : B) b))]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun j => 0 < mu j)) (by simp)
      (fun j => y j i * conj (w j b))]
    rw [hrec0 i b]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    rw [hy0 j (le_antisymm hj (hmu j)) i, zero_mul]

/-! ### Uniqueness -/

/-- The eigenspace of a matrix, as a submodule of `A → ℂ`. -/
