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


private lemma sum_map_ite_eq_count {a c : ℝ} (s : Multiset ℝ) :
    (s.map (fun x => if x = a then c else 0)).sum = c * (s.count a : ℝ) := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons x s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      rcases eq_or_ne x a with rfl | hx
      · rw [if_pos rfl, Multiset.count_cons_self]
        push_cast
        ring
      · rw [if_neg hx, Multiset.count_cons_of_ne (Ne.symm hx), zero_add]

/-- Two finite multisets of strictly positive reals with the same power sums are equal. -/
