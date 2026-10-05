/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
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

namespace Frontier

/-- An explicit vector of the real Hilbert space `ℝ⁴`. -/
def ksVec (a b c d : ℝ) : EuclideanSpace ℝ (Fin 4) := !₂[a, b, c, d]

@[simp] lemma ksVec_inner (a b c d a' b' c' d' : ℝ) :
    inner ℝ (ksVec a b c d) (ksVec a' b' c' d') = a * a' + b * b' + c * c' + d * d' := by
  simp [ksVec, PiLp.inner_apply, Fin.sum_univ_four]
  ring

lemma ksVec_ne_zero {a b c d : ℝ} (h : a * a + b * b + c * c + d * d ≠ 0) :
    ksVec a b c d ≠ 0 := by
  intro hv
  apply h
  have h0 : inner ℝ (ksVec a b c d) (ksVec a b c d) = (0 : ℝ) := by rw [hv]; simp
  rw [ksVec_inner] at h0
  exact h0

/-- A (noncontextual) hidden-variable value assignment on the rays of `ℝ⁴`: a `{0,1}`-valued
function `f` on vectors such that in every orthogonal basis exactly one vector gets value `1`.
This is exactly the assignment postulated by a noncontextual hidden-variable theory for the
four-dimensional quantum system: the value of the projection onto a ray does not depend on which
complete measurement (basis) the projection is measured in. -/
def IsKSValuation (f : EuclideanSpace ℝ (Fin 4) → Prop) : Prop :=
  ∀ v : Fin 4 → EuclideanSpace ℝ (Fin 4), (∀ i, v i ≠ 0) →
    (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) → ∃! i, f (v i)

/-- The `{0,1}` indicator of a proposition. -/
noncomputable def ind (p : Prop) : ℕ := if p then 1 else 0

lemma ind_of_true {p : Prop} (h : p) : ind p = 1 := if_pos h

lemma ind_of_false {p : Prop} (h : ¬ p) : ind p = 0 := if_neg h

/-- In every orthogonal basis of `ℝ⁴` the four indicator values sum to `1`. -/
lemma row_eq_one {f : EuclideanSpace ℝ (Fin 4) → Prop} (hf : IsKSValuation f)
    (a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : ℝ)
    (h : (a0 * a0 + b0 * b0 + c0 * c0 + d0 * d0 ≠ 0) ∧
         (a1 * a1 + b1 * b1 + c1 * c1 + d1 * d1 ≠ 0) ∧
         (a2 * a2 + b2 * b2 + c2 * c2 + d2 * d2 ≠ 0) ∧
         (a3 * a3 + b3 * b3 + c3 * c3 + d3 * d3 ≠ 0) ∧
         (a0 * a1 + b0 * b1 + c0 * c1 + d0 * d1 = 0) ∧
         (a0 * a2 + b0 * b2 + c0 * c2 + d0 * d2 = 0) ∧
         (a0 * a3 + b0 * b3 + c0 * c3 + d0 * d3 = 0) ∧
         (a1 * a2 + b1 * b2 + c1 * c2 + d1 * d2 = 0) ∧
         (a1 * a3 + b1 * b3 + c1 * c3 + d1 * d3 = 0) ∧
         (a2 * a3 + b2 * b3 + c2 * c3 + d2 * d3 = 0)) :
    ind (f (ksVec a0 b0 c0 d0)) + ind (f (ksVec a1 b1 c1 d1)) +
      ind (f (ksVec a2 b2 c2 d2)) + ind (f (ksVec a3 b3 c3 d3)) = 1 := by
  obtain ⟨n0, n1, n2, n3, o01, o02, o03, o12, o13, o23⟩ := h
  set v : Fin 4 → EuclideanSpace ℝ (Fin 4) :=
    ![ksVec a0 b0 c0 d0, ksVec a1 b1 c1 d1, ksVec a2 b2 c2 d2, ksVec a3 b3 c3 d3] with hv
  have hnz : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i <;> simp only [hv] <;> exact ksVec_ne_zero (by assumption)
  have horth : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  obtain ⟨i, hi, hu⟩ := hf v hnz horth
  have key : ∀ j : Fin 4, j ≠ i → ¬ f (v j) := fun j hj hfj => hj (hu j hfj)
  have e0 : v 0 = ksVec a0 b0 c0 d0 := rfl
  have e1 : v 1 = ksVec a1 b1 c1 d1 := rfl
  have e2 : v 2 = ksVec a2 b2 c2 d2 := rfl
  have e3 : v 3 = ksVec a3 b3 c3 d3 := rfl
  fin_cases i <;>
    simp only [← e0, ← e1, ← e2, ← e3] <;>
    [ (rw [ind_of_true (by simpa using hi), ind_of_false (key 1 (by decide)),
          ind_of_false (key 2 (by decide)), ind_of_false (key 3 (by decide))]);
      (rw [ind_of_false (key 0 (by decide)), ind_of_true (by simpa using hi),
          ind_of_false (key 2 (by decide)), ind_of_false (key 3 (by decide))]);
      (rw [ind_of_false (key 0 (by decide)), ind_of_false (key 1 (by decide)),
          ind_of_true (by simpa using hi), ind_of_false (key 3 (by decide))]);
      (rw [ind_of_false (key 0 (by decide)), ind_of_false (key 1 (by decide)),
          ind_of_false (key 2 (by decide)), ind_of_true (by simpa using hi)])]

/-- **Kochen–Specker theorem** (base case, dimension four).

There is no noncontextual hidden-variable value assignment for quantum mechanics: no
`{0,1}`-valued function on the vectors of `ℝ⁴` can assign the value `1` to exactly one member
of every orthogonal basis.

The proof is Cabello's 18-vector parity proof: there are 18 vectors arranged into 9 orthogonal
bases in such a way that each vector occurs in exactly two of the bases. Summing the "exactly
one" condition over the 9 bases gives 9, while counting vector-by-vector gives twice the number
of vectors valued `1`, an even number. -/
theorem kochen_specker : ¬ ∃ f : EuclideanSpace ℝ (Fin 4) → Prop, IsKSValuation f := by
  rintro ⟨f, hf⟩
  have h1 := row_eq_one hf 0 0 0 1  0 0 1 0  1 1 0 0  1 (-1) 0 0 (by norm_num)
  have h2 := row_eq_one hf 0 0 0 1  0 1 0 0  1 0 1 0  1 0 (-1) 0 (by norm_num)
  have h3 := row_eq_one hf 1 (-1) 1 (-1)  1 (-1) (-1) 1  1 1 0 0  0 0 1 1 (by norm_num)
  have h4 := row_eq_one hf 1 (-1) 1 (-1)  1 1 1 1  1 0 (-1) 0  0 1 0 (-1) (by norm_num)
  have h5 := row_eq_one hf 0 0 1 0  0 1 0 0  1 0 0 1  1 0 0 (-1) (by norm_num)
  have h6 := row_eq_one hf 1 (-1) (-1) 1  1 1 1 1  1 0 0 (-1)  0 1 (-1) 0 (by norm_num)
  have h7 := row_eq_one hf 1 1 (-1) 1  1 1 1 (-1)  1 (-1) 0 0  0 0 1 1 (by norm_num)
  have h8 := row_eq_one hf 1 1 (-1) 1  (-1) 1 1 1  1 0 1 0  0 1 0 (-1) (by norm_num)
  have h9 := row_eq_one hf 1 1 1 (-1)  (-1) 1 1 1  1 0 0 1  0 1 (-1) 0 (by norm_num)
  omega

end Frontier

