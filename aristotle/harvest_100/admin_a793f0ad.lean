/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
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

namespace Brockian

/-! ## Setup

We model a function on the vertices of a regular `n`-gon as a function `ℤ → ℝ` which is
`n`-periodic (the vertex labelled `j` is the vertex `j mod n`).  The dihedral group `D n`
acts by the rotation `j ↦ j + 1` and the reflection `j ↦ -j`.

The `k`-th *mode subspace* is the span of the two "Fourier" functions
`j ↦ cos (2πkj/n)` and `j ↦ sin (2πkj/n)`.  For the pentagon (`n = 5`) the modes `k = 1, 2`
are exactly the two two-dimensional isotypic components of the vertex representation of
`D 5`; the results below establish the corresponding statements for arbitrary `n`. -/

/-- The cosine Fourier mode of index `k` on the vertices of the `n`-gon. -/
noncomputable def ngonCos (n k : ℕ) (j : ℤ) : ℝ := Real.cos (2 * π * k * j / n)

/-- The sine Fourier mode of index `k` on the vertices of the `n`-gon. -/
noncomputable def ngonSin (n k : ℕ) (j : ℤ) : ℝ := Real.sin (2 * π * k * j / n)

/-- The rotation of the `n`-gon, acting on vertex functions. -/
def ngonRot : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ) where
  toFun f := fun j => f (j + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The reflection of the `n`-gon, acting on vertex functions. -/
def ngonRefl : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ) where
  toFun f := fun j => f (-j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `k`-th mode subspace of the `n`-gon: the span of the `k`-th cosine and sine modes. -/
noncomputable def ngonMode (n k : ℕ) : Submodule ℝ (ℤ → ℝ) :=
  Submodule.span ℝ (Set.range ![ngonCos n k, ngonSin n k])

/-! ## Basic identities for the modes -/

lemma ngonCos_zero (n k : ℕ) : ngonCos n k 0 = 1 := by
  simp [ngonCos]

lemma ngonSin_one (n k : ℕ) : ngonSin n k 1 = Real.sin (2 * π * k / n) := by
  simp [ngonSin]

lemma ngonCos_succ (n k : ℕ) (j : ℤ) :
    ngonCos n k (j + 1) =
      Real.cos (2 * π * k / n) * ngonCos n k j - Real.sin (2 * π * k / n) * ngonSin n k j := by
  have h : (2 * π * k * ((j : ℝ) + 1) / n) = 2 * π * k * j / n + 2 * π * k / n := by
    ring
  simp only [ngonCos, ngonSin, Int.cast_add, Int.cast_one, h, Real.cos_add]
  ring

lemma ngonSin_succ (n k : ℕ) (j : ℤ) :
    ngonSin n k (j + 1) =
      Real.sin (2 * π * k / n) * ngonCos n k j + Real.cos (2 * π * k / n) * ngonSin n k j := by
  have h : (2 * π * k * ((j : ℝ) + 1) / n) = 2 * π * k * j / n + 2 * π * k / n := by
    ring
  simp only [ngonCos, ngonSin, Int.cast_add, Int.cast_one, h, Real.sin_add]
  ring

lemma ngonCos_neg (n k : ℕ) (j : ℤ) : ngonCos n k (-j) = ngonCos n k j := by
  have h : (2 * π * k * ((-j : ℤ) : ℝ) / n) = -(2 * π * k * j / n) := by
    push_cast; ring
  simp only [ngonCos, h, Real.cos_neg]

lemma ngonSin_neg (n k : ℕ) (j : ℤ) : ngonSin n k (-j) = -ngonSin n k j := by
  have h : (2 * π * k * ((-j : ℤ) : ℝ) / n) = -(2 * π * k * j / n) := by
    push_cast; ring
  simp only [ngonSin, h, Real.sin_neg]

lemma ngonCos_periodic {n : ℕ} (hn : 0 < n) (k : ℕ) (j : ℤ) :
    ngonCos n k (j + n) = ngonCos n k j := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * π * k * ((j : ℝ) + n) / n) = 2 * π * k * j / n + (k : ℝ) * (2 * π) := by
    field_simp
  simp only [ngonCos, Int.cast_add, Int.cast_natCast, h, Real.cos_add_nat_mul_two_pi]

lemma ngonSin_periodic {n : ℕ} (hn : 0 < n) (k : ℕ) (j : ℤ) :
    ngonSin n k (j + n) = ngonSin n k j := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * π * k * ((j : ℝ) + n) / n) = 2 * π * k * j / n + (k : ℝ) * (2 * π) := by
    field_simp
  simp only [ngonSin, Int.cast_add, Int.cast_natCast, h, Real.sin_add_nat_mul_two_pi]

lemma ngonCos_three_term (n k : ℕ) (j : ℤ) :
    ngonCos n k (j + 2) = 2 * Real.cos (2 * π * k / n) * ngonCos n k (j + 1) - ngonCos n k j := by
  have h2 : j + 2 = (j + 1) + 1 := by ring
  rw [h2, ngonCos_succ, ngonCos_succ, ngonSin_succ]
  linear_combination (-(ngonCos n k j)) * (Real.sin_sq_add_cos_sq (2 * π * k / n))

lemma ngonSin_three_term (n k : ℕ) (j : ℤ) :
    ngonSin n k (j + 2) = 2 * Real.cos (2 * π * k / n) * ngonSin n k (j + 1) - ngonSin n k j := by
  have h2 : j + 2 = (j + 1) + 1 := by ring
  rw [h2, ngonSin_succ, ngonCos_succ, ngonSin_succ]
  linear_combination (-(ngonSin n k j)) * (Real.sin_sq_add_cos_sq (2 * π * k / n))

/-! ## The mode subspaces are subrepresentations -/

lemma ngonCos_mem (n k : ℕ) : ngonCos n k ∈ ngonMode n k :=
  Submodule.subset_span ⟨0, rfl⟩

lemma ngonSin_mem (n k : ℕ) : ngonSin n k ∈ ngonMode n k :=
  Submodule.subset_span ⟨1, rfl⟩

lemma ngonRot_mode (n k : ℕ) : Submodule.map ngonRot (ngonMode n k) ≤ ngonMode n k := by
  rw [ngonMode, Submodule.map_span_le]
  rintro m ⟨i, rfl⟩
  fin_cases i
  · show ngonRot (ngonCos n k) ∈ _
    have : ngonRot (ngonCos n k) =
        Real.cos (2 * π * k / n) • ngonCos n k - Real.sin (2 * π * k / n) • ngonSin n k := by
      funext j
      simpa [ngonRot] using ngonCos_succ n k j
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (ngonCos_mem n k))
      (Submodule.smul_mem _ _ (ngonSin_mem n k))
  · show ngonRot (ngonSin n k) ∈ _
    have : ngonRot (ngonSin n k) =
        Real.sin (2 * π * k / n) • ngonCos n k + Real.cos (2 * π * k / n) • ngonSin n k := by
      funext j
      simpa [ngonRot] using ngonSin_succ n k j
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (ngonCos_mem n k))
      (Submodule.smul_mem _ _ (ngonSin_mem n k))

lemma ngonRefl_mode (n k : ℕ) : Submodule.map ngonRefl (ngonMode n k) ≤ ngonMode n k := by
  rw [ngonMode, Submodule.map_span_le]
  rintro m ⟨i, rfl⟩
  fin_cases i
  · show ngonRefl (ngonCos n k) ∈ _
    have : ngonRefl (ngonCos n k) = ngonCos n k := by
      funext j; simpa [ngonRefl] using ngonCos_neg n k j
    rw [this]
    exact ngonCos_mem n k
  · show ngonRefl (ngonSin n k) ∈ _
    have : ngonRefl (ngonSin n k) = (-1 : ℝ) • ngonSin n k := by
      funext j; simpa [ngonRefl] using ngonSin_neg n k j
    rw [this]
    exact Submodule.smul_mem _ _ (ngonSin_mem n k)

lemma ngonMode_periodic {n : ℕ} (hn : 0 < n) (k : ℕ) (f : ℤ → ℝ) (hf : f ∈ ngonMode n k)
    (j : ℤ) : f (j + n) = f j := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact ngonCos_periodic hn k j
      · exact ngonSin_periodic hn k j
  | zero => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [Pi.smul_apply, hx]

/-! ## Distinct modes are independent -/

lemma ngonMode_three_term {n k : ℕ} (f : ℤ → ℝ) (hf : f ∈ ngonMode n k) (j : ℤ) :
    f (j + 2) = 2 * Real.cos (2 * π * k / n) * f (j + 1) - f j := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact ngonCos_three_term n k j
      · exact ngonSin_three_term n k j
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]; ring
  | smul a x _ hx => simp only [Pi.smul_apply, hx, smul_eq_mul]; ring

/-- Two modes with different rotation eigenvalue-traces meet only in `0`: the isotypic
components of the vertex representation of the `n`-gon are independent. -/
lemma ngonMode_disjoint {n k l : ℕ}
    (h : Real.cos (2 * π * k / n) ≠ Real.cos (2 * π * l / n)) :
    ngonMode n k ⊓ ngonMode n l = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro f ⟨hk, hl⟩
  funext j
  have h1 := ngonMode_three_term f hk (j - 1)
  have h2 := ngonMode_three_term f hl (j - 1)
  have e1 : j - 1 + 1 = j := by ring
  have e2 : j - 1 + 2 = j + 1 := by ring
  rw [e1, e2] at h1 h2
  have h3 : 2 * (Real.cos (2 * π * k / n) - Real.cos (2 * π * l / n)) * f j = 0 := by
    have := h1.symm.trans h2
    linarith [this]
  have h4 : Real.cos (2 * π * k / n) - Real.cos (2 * π * l / n) ≠ 0 := sub_ne_zero.mpr h
  have := mul_eq_zero.mp h3
  rcases this with h5 | h5
  · exact absurd h5 (by simpa using mul_ne_zero two_ne_zero h4)
  · simpa using h5

/-! ## Two-dimensionality of a nondegenerate mode -/

lemma ngonMode_linearIndependent {n k : ℕ} (h : Real.sin (2 * π * k / n) ≠ 0) :
    LinearIndependent ℝ ![ngonCos n k, ngonSin n k] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hcon
    apply h
    have := congrFun hcon 1
    simpa [ngonSin_one] using this
  · intro a hcon
    have h0 := congrFun hcon 0
    have h1 := congrFun hcon 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
      smul_eq_mul] at h0 h1
    rw [ngonCos_zero] at h0
    have ha : a = 0 := by
      have : ngonSin n k 0 = 0 := by simp [ngonSin]
      rw [this] at h0; simpa using h0.symm
    rw [ha] at h0
    simp at h0

lemma ngonMode_finrank {n k : ℕ} (h : Real.sin (2 * π * k / n) ≠ 0) :
    Module.finrank ℝ (ngonMode n k) = 2 := by
  have := finrank_span_eq_card (ngonMode_linearIndependent h)
  simpa [ngonMode] using this

/-! ## The pentagon -/

lemma sin_two_pi_div_five_ne_zero : Real.sin (2 * π * (1 : ℕ) / (5 : ℕ)) ≠ 0 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 : (0 : ℝ) < 2 * π * (1 : ℕ) / (5 : ℕ) := by
    push_cast; positivity
  have h2 : 2 * π * (1 : ℕ) / (5 : ℕ) < π := by
    push_cast
    nlinarith [Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

lemma sin_four_pi_div_five_ne_zero : Real.sin (2 * π * (2 : ℕ) / (5 : ℕ)) ≠ 0 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 : (0 : ℝ) < 2 * π * (2 : ℕ) / (5 : ℕ) := by
    push_cast; positivity
  have h2 : 2 * π * (2 : ℕ) / (5 : ℕ) < π := by
    push_cast
    nlinarith [Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

lemma cos_two_pi_div_five_ne_cos_four_pi_div_five :
    Real.cos (2 * π * (1 : ℕ) / (5 : ℕ)) ≠ Real.cos (2 * π * (2 : ℕ) / (5 : ℕ)) := by
  have hlt : Real.cos (2 * π * (2 : ℕ) / (5 : ℕ)) < Real.cos (2 * π * (1 : ℕ) / (5 : ℕ)) := by
    refine Real.cos_lt_cos_of_nonneg_of_le_pi ?_ ?_ ?_
    · push_cast; positivity
    · push_cast; nlinarith [Real.pi_pos]
    · push_cast; nlinarith [Real.pi_pos]
  exact ne_of_gt hlt

/-! ## Main theorem -/

/--
**Pentagon isotypic components, generalized to higher `n`.**

For every `n`-gon (`0 < n`) and every mode index `k`:

* the mode subspace `ngonMode n k` (spanned by `j ↦ cos (2πkj/n)` and `j ↦ sin (2πkj/n)`)
  is invariant under the rotation `j ↦ j + 1` and the reflection `j ↦ -j`, i.e. it is a
  subrepresentation of the dihedral group of the `n`-gon;
* every element of it is `n`-periodic, i.e. is a genuine function on the vertices of
  the `n`-gon;
* whenever `sin (2πk/n) ≠ 0`, the two generating modes are linearly independent and the
  mode subspace is exactly two-dimensional;
* two mode subspaces with `cos (2πk/n) ≠ cos (2πl/n)` intersect trivially.

Specializing to the pentagon `n = 5`, the modes `k = 1, 2` give the two two-dimensional
isotypic components of the vertex representation of the dihedral group `D 5`.
-/
theorem PentagonPentagonIsotypicHigherN :
    (∀ n k : ℕ, 0 < n →
        Submodule.map ngonRot (ngonMode n k) ≤ ngonMode n k ∧
        Submodule.map ngonRefl (ngonMode n k) ≤ ngonMode n k ∧
        (∀ f ∈ ngonMode n k, ∀ j : ℤ, f (j + n) = f j) ∧
        (Real.sin (2 * π * k / n) ≠ 0 →
          LinearIndependent ℝ ![ngonCos n k, ngonSin n k] ∧
            Module.finrank ℝ (ngonMode n k) = 2)) ∧
      (∀ n k l : ℕ, Real.cos (2 * π * k / n) ≠ Real.cos (2 * π * l / n) →
        ngonMode n k ⊓ ngonMode n l = ⊥) ∧
      (Module.finrank ℝ (ngonMode 5 1) = 2 ∧ Module.finrank ℝ (ngonMode 5 2) = 2 ∧
        ngonMode 5 1 ⊓ ngonMode 5 2 = ⊥) := by
  refine ⟨fun n k hn => ⟨ngonRot_mode n k, ngonRefl_mode n k,
      fun f hf j => ngonMode_periodic hn k f hf j,
      fun h => ⟨ngonMode_linearIndependent h, ngonMode_finrank h⟩⟩,
    fun _ _ _ h => ngonMode_disjoint h,
    ngonMode_finrank sin_two_pi_div_five_ne_zero,
    ngonMode_finrank sin_four_pi_div_five_ne_zero,
    ngonMode_disjoint cos_two_pi_div_five_ne_cos_four_pi_div_five⟩

end Brockian

