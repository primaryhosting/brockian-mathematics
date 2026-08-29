/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix ComplexConjugate

namespace QI

variable {A B : Type*}

/-- `IsSchmidtDecomposition M r lam e f` says that the bipartite pure state whose amplitude
matrix is `M` (so that the state is `∑ i j, M i j • |i⟩ ⊗ |j⟩`) is written as

`M i j = ∑ k, (lam k) * e k i * f k j`

where the `lam k` are strictly positive real *Schmidt coefficients* and `e`, `f` are
orthonormal families in the two tensor factors. -/
structure IsSchmidtDecomposition [Fintype A] [Fintype B] (M : Matrix A B ℂ) (r : ℕ)
    (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ) : Prop where
  /-- Schmidt coefficients are strictly positive. -/
  coeff_pos : ∀ k, 0 < lam k
  /-- The left Schmidt vectors are orthonormal. -/
  left_orthonormal : ∀ k l, ∑ i, conj (e k i) * e l i = if k = l then 1 else 0
  /-- The right Schmidt vectors are orthonormal. -/
  right_orthonormal : ∀ k l, ∑ j, conj (f k j) * f l j = if k = l then 1 else 0
  /-- The state is the corresponding sum of product states. -/
  sum_eq : ∀ i j, M i j = ∑ k, (lam k : ℂ) * e k i * f k j

/-! ### A multiset of positive reals is determined by its power sums -/


theorem multiset_eq_of_powerSums {s t : Multiset ℝ}
    (hs : ∀ x ∈ s, 0 < x) (ht : ∀ x ∈ t, 0 < x)
    (h : ∀ p : ℕ, (s.map (fun x => x ^ (p + 1))).sum = (t.map (fun x => x ^ (p + 1))).sum) :
    s = t := by
  classical
  -- The key step: the two multisets give the same sum for any function of the form
  -- `x ↦ x ^ (m+1) * ∏ v ∈ F, (x - v)`.
  have key : ∀ (F : Finset ℝ) (m : ℕ),
      (s.map (fun x => x ^ (m + 1) * ∏ v ∈ F, (x - v))).sum
        = (t.map (fun x => x ^ (m + 1) * ∏ v ∈ F, (x - v))).sum := by
    intro F
    induction F using Finset.induction with
    | empty => intro m; simpa using h m
    | insert w F' hw ih =>
        intro m
        have expand : ∀ x : ℝ, x ^ (m + 1) * ∏ v ∈ insert w F', (x - v)
            = x ^ (m + 1 + 1) * (∏ v ∈ F', (x - v))
              + (-w) * (x ^ (m + 1) * ∏ v ∈ F', (x - v)) := by
          intro x
          rw [Finset.prod_insert hw]
          ring
        simp only [expand]
        rw [Multiset.sum_map_add, Multiset.sum_map_add,
          Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, ih (m + 1), ih m]
  refine Multiset.ext.2 fun a => ?_
  rcases le_or_gt a 0 with ha | ha
  · rw [Multiset.count_eq_zero_of_notMem (fun hmem => absurd (hs a hmem) (not_lt.2 ha)),
      Multiset.count_eq_zero_of_notMem (fun hmem => absurd (ht a hmem) (not_lt.2 ha))]
  · set V : Finset ℝ := s.toFinset ∪ t.toFinset with hV
    set F : Finset ℝ := V.erase a with hF
    set c : ℝ := a * ∏ v ∈ F, (a - v) with hc
    have hcne : c ≠ 0 := by
      refine mul_ne_zero (ne_of_gt ha) (Finset.prod_ne_zero_iff.2 fun v hv => ?_)
      have hva : v ≠ a := Finset.ne_of_mem_erase hv
      exact sub_ne_zero.2 (Ne.symm hva)
    have hval : ∀ (m : Multiset ℝ), (∀ x ∈ m, x ∈ V) →
        (m.map (fun x => x ^ (0 + 1) * ∏ v ∈ F, (x - v))).sum = c * (m.count a : ℝ) := by
      intro m hm
      rw [← sum_map_ite_eq_count (a := a) (c := c) m]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun x hx => ?_)
      rcases eq_or_ne x a with rfl | hxa
      · rw [if_pos rfl, hc]
        ring
      · have hxF : x ∈ F := Finset.mem_erase.2 ⟨hxa, hm x hx⟩
        rw [if_neg hxa, Finset.prod_eq_zero hxF (by ring)]
        ring
    have h1 : (∀ x ∈ s, x ∈ V) := fun x hx =>
      Finset.mem_union_left _ (Multiset.mem_toFinset.2 hx)
    have h2 : (∀ x ∈ t, x ∈ V) := fun x hx =>
      Finset.mem_union_right _ (Multiset.mem_toFinset.2 hx)
    have hkey := key F 0
    rw [hval s h1, hval t h2] at hkey
    exact_mod_cast mul_left_cancel₀ hcne hkey

/-! ### Traces of powers of the reduced density matrix -/

section Trace

variable [Fintype A] [Fintype B] [DecidableEq A]
variable {M : Matrix A B ℂ} {r : ℕ} {lam : Fin r → ℝ} {e : Fin r → A → ℂ} {f : Fin r → B → ℂ}

/-- The matrix whose columns are the left Schmidt vectors. -/
