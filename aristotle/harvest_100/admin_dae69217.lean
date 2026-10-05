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

set_option grind.warning false

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
recorded with integer entries. -/
def ksVecZ : Fin 18 → Fin 4 → ℤ :=
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

/-- The 18 vectors of the Kochen–Specker set, as vectors in `ℝ⁴`. -/
def ksVec (i : Fin 18) : Fin 4 → ℝ := fun m => ((ksVecZ i m : ℤ) : ℝ)

/-- The 9 bases: `ksBasis j k` is the index of the `k`-th vector of the `j`-th basis. -/
def ksBasis : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3],
    ![0, 4, 5, 6],
    ![7, 8, 2, 9],
    ![7, 10, 6, 11],
    ![1, 4, 12, 13],
    ![8, 10, 13, 14],
    ![15, 16, 3, 9],
    ![15, 17, 5, 11],
    ![16, 17, 12, 14]]

/-- The 18 vectors are pairwise distinct. -/
theorem ksVecZ_injective : Function.Injective ksVecZ := by decide

/-- None of the 18 vectors is zero. -/
theorem ksVecZ_ne_zero (i : Fin 18) : ksVecZ i ≠ 0 := by
  revert i; decide

/-- Each of the 9 quadruples consists of pairwise orthogonal vectors (integer version). -/
theorem ksBasis_orthogonalZ (j : Fin 9) (k l : Fin 4) (h : k ≠ l) :
    ∑ m : Fin 4, ksVecZ (ksBasis j k) m * ksVecZ (ksBasis j l) m = 0 := by
  revert j k l; decide

/-- Each of the 9 quadruples consists of pairwise orthogonal vectors of `ℝ⁴`. -/
theorem ksBasis_orthogonal (j : Fin 9) (k l : Fin 4) (h : k ≠ l) :
    ∑ m : Fin 4, ksVec (ksBasis j k) m * ksVec (ksBasis j l) m = 0 := by
  have h0 : ((∑ m : Fin 4, ksVecZ (ksBasis j k) m * ksVecZ (ksBasis j l) m : ℤ) : ℝ) = 0 := by
    rw [ksBasis_orthogonalZ j k l h]; norm_num
  simpa [ksVec] using h0

/-- None of the 18 vectors is the zero vector of `ℝ⁴`. -/
theorem ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  intro h
  refine ksVecZ_ne_zero i (funext fun m => ?_)
  have hm : ((ksVecZ i m : ℤ) : ℝ) = 0 := congrFun h m
  exact_mod_cast hm

/-- The 18 vectors, viewed as elements of the Euclidean space `ℝ⁴`. -/
noncomputable def ksVecE (i : Fin 18) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (ksVec i)

/-- Each of the 9 quadruples is a genuine (orthogonal) basis of `ℝ⁴`: its four vectors are
linearly independent. -/
theorem ksBasis_linearIndependent (j : Fin 9) :
    LinearIndependent ℝ (fun k : Fin 4 => ksVecE (ksBasis j k)) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro k h
    exact ksVec_ne_zero (ksBasis j k) (congrArg WithLp.ofLp h)
  · intro k l hkl
    simp only [ksVecE, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simpa [mul_comm] using ksBasis_orthogonal j k l hkl

/-- Each of the 9 quadruples spans `ℝ⁴`, hence is an orthogonal basis. -/
theorem ksBasis_span_eq_top (j : Fin 9) :
    Submodule.span ℝ (Set.range fun k : Fin 4 => ksVecE (ksBasis j k)) = ⊤ :=
  (ksBasis_linearIndependent j).span_eq_top_of_card_eq_finrank (by
    simp [finrank_euclideanSpace])

/-- Every one of the 18 vectors occurs in exactly two of the 9 bases; consequently,
summing any weight function over all bases counts each vector twice. -/
theorem ks_double_count (g : Fin 18 → ℕ) :
    ∑ j : Fin 9, ∑ k : Fin 4, g (ksBasis j k) = 2 * ∑ i : Fin 18, g i := by
  simp [ksBasis, Fin.sum_univ_succ]
  ring

/-- **Kochen–Specker theorem, 18-vector version.**
There is no `{0,1}`-coloring of the vectors of `ℝ⁴` assigning the value `1` to exactly one
vector of each of the nine orthogonal bases of the Cabello–Estebaranz–García-Alcaine set.
(The hypothesis that `f` takes only the values `0` and `1` is part of the requested
statement; it is in fact implied by the second condition.) -/
theorem kochen_specker_18 :
    ¬ ∃ f : (Fin 4 → ℝ) → ℕ, (∀ v, f v = 0 ∨ f v = 1) ∧
      ∀ j : Fin 9, ∑ k : Fin 4, f (ksVec (ksBasis j k)) = 1 := by
  rintro ⟨f, -, hf⟩
  have h1 : ∑ j : Fin 9, ∑ k : Fin 4, f (ksVec (ksBasis j k)) = 9 := by
    simp [hf]
  have h2 := ks_double_count (fun i => f (ksVec i))
  omega

end Phys

