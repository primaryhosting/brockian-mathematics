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

/-- Integer coordinates of the 18 vectors of the Cabello–Estebaranz–García-Alcaine
Kochen–Specker set in `ℝ⁴`. -/
def ksVecZ : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1],    -- 0
    ![0, 0, 1, 0],    -- 1
    ![1, 1, 0, 0],    -- 2
    ![1, -1, 0, 0],   -- 3
    ![0, 1, 0, 0],    -- 4
    ![1, 0, 1, 0],    -- 5
    ![1, 0, -1, 0],   -- 6
    ![1, -1, 1, -1],  -- 7
    ![1, -1, -1, 1],  -- 8
    ![0, 0, 1, 1],    -- 9
    ![1, 1, 1, 1],    -- 10
    ![0, 1, 0, -1],   -- 11
    ![1, 0, 0, 1],    -- 12
    ![1, 0, 0, -1],   -- 13
    ![0, 1, -1, 0],   -- 14
    ![1, 1, -1, 1],   -- 15
    ![1, 1, 1, -1],   -- 16
    ![-1, 1, 1, 1]]   -- 17

/-- The 18 Kochen–Specker vectors, as elements of the Euclidean space `ℝ⁴`. -/
def ksVec (i : Fin 18) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (fun k => ((ksVecZ i k : ℤ) : ℝ))

/-- The nine orthogonal bases of the Kochen–Specker configuration, given as
sets of indices of the 18 vectors.  Every index occurs in exactly two of them. -/
def ksBasis : Fin 9 → Finset (Fin 18) :=
  ![{0, 1, 2, 3},
    {0, 4, 5, 6},
    {7, 8, 2, 9},
    {7, 10, 6, 11},
    {1, 4, 12, 13},
    {8, 10, 13, 14},
    {15, 16, 3, 9},
    {15, 17, 5, 11},
    {16, 17, 12, 14}]

lemma ksVec_inner (i i' : Fin 18) :
    (inner ℝ (ksVec i) (ksVec i') : ℝ) = ((∑ k : Fin 4, ksVecZ i k * ksVecZ i' k : ℤ) : ℝ) := by
  simp only [ksVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Int.cast_sum,
    Int.cast_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Each of the nine sets of indices has four elements. -/
lemma ksBasis_card (j : Fin 9) : (ksBasis j).card = 4 := by
  fin_cases j <;> decide

/-- Within each of the nine sets, the corresponding vectors are pairwise orthogonal. -/
lemma ksBasis_orthogonal_Z (j : Fin 9) :
    ∀ i ∈ ksBasis j, ∀ i' ∈ ksBasis j, i ≠ i' → ∑ k : Fin 4, ksVecZ i k * ksVecZ i' k = 0 := by
  fin_cases j <;> decide

/-- Each index lies in exactly two of the nine sets. -/
lemma ksBasis_count (i : Fin 18) :
    (Finset.univ.filter (fun j : Fin 9 => i ∈ ksBasis j)).card = 2 := by
  fin_cases i <;> decide

lemma ksVecZ_ne_zero (i : Fin 18) : ∃ k : Fin 4, ksVecZ i k ≠ 0 := by
  fin_cases i <;> decide

lemma ksVecZ_injective : Function.Injective ksVecZ := by decide

/-- **No `{0,1}`-coloring**: there is no assignment of values in `{0,1}` to the 18 vectors
such that exactly one vector of each of the nine orthogonal bases receives the value `1`. -/
lemma no_coloring :
    ¬ ∃ f : Fin 18 → ℕ, (∀ i, f i ≤ 1) ∧ ∀ j : Fin 9, ∑ i ∈ ksBasis j, f i = 1 := by
  rintro ⟨f, -, hf⟩
  have h1 : ∑ j : Fin 9, ∑ i ∈ ksBasis j, f i = 9 := by
    simp [hf]
  have h2 : ∑ j : Fin 9, ∑ i ∈ ksBasis j, f i
      = ∑ j : Fin 9, ∑ i : Fin 18, (if i ∈ ksBasis j then f i else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h3 : ∀ i : Fin 18, ∑ j : Fin 9, (if i ∈ ksBasis j then f i else 0) = 2 * f i := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, ksBasis_count i, smul_eq_mul]
  rw [h2, Finset.sum_comm] at h1
  simp only [h3] at h1
  rw [← Finset.mul_sum] at h1
  omega

/-- **Kochen–Specker theorem, 18-vector version.**
The 18 explicit vectors `ksVec` in `ℝ⁴` are nonzero and pairwise distinct, the nine index
sets `ksBasis` each consist of four indices whose vectors are pairwise orthogonal (hence
form an orthogonal basis of `ℝ⁴`), and yet there is no `{0,1}`-valued coloring of the
18 vectors assigning the value `1` to exactly one vector in each of the nine bases. -/
theorem kochen_specker_18 :
    (∀ i : Fin 18, ksVec i ≠ 0) ∧
    Function.Injective ksVec ∧
    (∀ j : Fin 9, (ksBasis j).card = 4) ∧
    (∀ j : Fin 9, ∀ i ∈ ksBasis j, ∀ i' ∈ ksBasis j, i ≠ i' →
      (inner ℝ (ksVec i) (ksVec i') : ℝ) = 0) ∧
    ¬ ∃ f : Fin 18 → ℕ, (∀ i, f i ≤ 1) ∧ ∀ j : Fin 9, ∑ i ∈ ksBasis j, f i = 1 := by
  refine ⟨?_, ?_, ksBasis_card, ?_, no_coloring⟩
  · intro i hi
    obtain ⟨k, hk⟩ := ksVecZ_ne_zero i
    have h0 : ksVec i k = 0 := by rw [hi]; rfl
    simp only [ksVec, WithLp.ofLp_toLp] at h0
    exact hk (by exact_mod_cast h0)
  · intro i i' h
    have hz : ksVecZ i = ksVecZ i' := by
      funext k
      have : ((ksVecZ i k : ℤ) : ℝ) = ((ksVecZ i' k : ℤ) : ℝ) := by
        have hk : ksVec i k = ksVec i' k := by rw [h]
        simpa [ksVec] using hk
      exact_mod_cast this
    exact ksVecZ_injective hz
  · intro j i hi i' hi' hne
    rw [ksVec_inner, ksBasis_orthogonal_Z j i hi i' hi' hne]
    norm_num

#print axioms Phys.kochen_specker_18

end Phys

