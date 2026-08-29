/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/
def ksVec : Fin 18 → (Fin 4 → ℝ) :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![1, 1, 0, 0],
    ![1, -1, 0, 0],
    ![0, 1, 0, 0],
    ![1, 0, 1, 0],
    ![1, 0, -1, 0],
    ![1, -1, 1, -1],
    ![1, -1, -1, 1],
    ![0, 0, 1, 1],
    ![1, 1, 1, 1],
    ![0, 1, 0, -1],
    ![1, 0, 0, 1],
    ![1, 0, 0, -1],
    ![0, 1, -1, 0],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![-1, 1, 1, 1]]

/-- The 9 orthogonal bases of the Kochen–Specker set, given as quadruples of indices into
`ksVec`.  Each of the 18 vectors occurs in exactly two of the bases. -/
def ksBasis : Fin 9 → (Fin 4 → Fin 18) :=
  ![![0, 1, 2, 3],
    ![0, 4, 5, 6],
    ![7, 8, 2, 9],
    ![7, 10, 6, 11],
    ![1, 4, 12, 13],
    ![8, 10, 13, 14],
    ![15, 16, 3, 9],
    ![15, 17, 5, 11],
    ![16, 17, 12, 14]]

/-- A base-3 style separating functional for the 18 vectors. -/
private def ksCode : Fin 18 → ℤ :=
  ![27, 9, 4, -2, 3, 10, -8, -20, 16, 36, 40, -24, 28, -26, -6, 22, -14, 38]

private lemma ksCode_spec (k : Fin 18) :
    ksVec k 0 + 3 * ksVec k 1 + 9 * ksVec k 2 + 27 * ksVec k 3 = (ksCode k : ℝ) := by
  fin_cases k <;> simp [ksVec, ksCode] <;> norm_num

private lemma ksCode_injective : Function.Injective ksCode := by
  decide

/-- If `P` holds for exactly one index, the corresponding `0/1` sum is `1`. -/
private lemma sum_ite_of_existsUnique {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : ∃! i, P i) : ∑ i, (if P i then (1 : ℕ) else 0) = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have hcongr : ∀ j : Fin n, (if P j then (1 : ℕ) else 0) = if j = i then 1 else 0 := by
    intro j
    by_cases hj : P j
    · rw [if_pos hj, if_pos (hu j hj)]
    · have : j ≠ i := by rintro rfl; exact hj hi
      simp [hj, this]
  simp [Finset.sum_congr rfl (fun j _ => hcongr j)]

/-- **Kochen–Specker (18 vectors).**  The explicit 18-vector configuration in `ℝ⁴` of
Cabello, Estebaranz and García-Alcaine consists of 18 distinct nonzero vectors arranged into
9 orthogonal bases (four pairwise orthogonal vectors each), and admits no `{0,1}`-coloring:
there is no assignment of a truth value to each vector such that in every one of the nine
bases exactly one vector is assigned `true`. -/
theorem kochen_specker_18 :
    Function.Injective ksVec ∧
    (∀ k : Fin 18, ksVec k ≠ 0) ∧
    (∀ b : Fin 9, ∀ i j : Fin 4, i ≠ j →
      ∑ t : Fin 4, ksVec (ksBasis b i) t * ksVec (ksBasis b j) t = 0) ∧
    ¬ ∃ c : (Fin 4 → ℝ) → Bool,
        ∀ b : Fin 9, ∃! i : Fin 4, c (ksVec (ksBasis b i)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply ksCode_injective
    have h : (ksCode a : ℝ) = (ksCode b : ℝ) := by
      rw [← ksCode_spec, ← ksCode_spec, hab]
    exact_mod_cast h
  · intro k hk
    have h : (ksCode k : ℝ) = 0 := by
      rw [← ksCode_spec, hk]; norm_num
    have h' : ksCode k = 0 := by exact_mod_cast h
    revert h'
    fin_cases k <;> decide
  · intro b i j hij
    fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp_all [ksVec, ksBasis, Fin.sum_univ_four]
  · rintro ⟨c, hc⟩
    set g : Fin 18 → ℕ := fun k => if c (ksVec k) = true then 1 else 0 with hg
    have key : ∀ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 1 := by
      intro b
      exact sum_ite_of_existsUnique (fun i : Fin 4 => c (ksVec (ksBasis b i)) = true) (hc b)
    have h0 := key 0
    have h1 := key 1
    have h2 := key 2
    have h3 := key 3
    have h4 := key 4
    have h5 := key 5
    have h6 := key 6
    have h7 := key 7
    have h8 := key 8
    simp only [Fin.sum_univ_four, ksBasis, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    omega

end Phys

