/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
with integer entries. -/
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

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
as vectors in `ℝ⁴`. -/
def ksVec (i : Fin 18) (k : Fin 4) : ℝ := ((ksVecZ i k : ℤ) : ℝ)

/-- The Euclidean inner product of two of the vectors. -/
def ksDot (i j : Fin 18) : ℝ := ∑ k : Fin 4, ksVec i k * ksVec j k

/-- Integer version of the inner product. -/
def ksDotZ (i j : Fin 18) : ℤ := ∑ k : Fin 4, ksVecZ i k * ksVecZ j k

lemma ksDot_eq_cast (i j : Fin 18) : ksDot i j = ((ksDotZ i j : ℤ) : ℝ) := by
  simp [ksDot, ksDotZ, ksVec]

lemma ksDot_eq_zero_of_int {i j : Fin 18} (h : ksDotZ i j = 0) : ksDot i j = 0 := by
  rw [ksDot_eq_cast, h, Int.cast_zero]

/-- The 18 vectors are pairwise distinct. -/
theorem ksVec_injective : Function.Injective ksVec := by
  have h : Function.Injective ksVecZ := by decide
  intro i j hij
  refine h ?_
  funext k
  have := congrFun hij k
  simpa [ksVec] using this

/-- **Kochen–Specker (18 vectors, 9 contexts).**
The explicit 18-vector set `ksVec` in `ℝ⁴` admits no `{0,1}`-coloring assigning
value `1` to exactly one vector of every quadruple of pairwise distinct, pairwise
orthogonal vectors of the set. -/
theorem kochen_specker_18 :
    ¬ ∃ f : Fin 18 → ℕ,
      (∀ i, f i = 0 ∨ f i = 1) ∧
      (∀ a b c d : Fin 18,
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        ksDot a b = 0 → ksDot a c = 0 → ksDot a d = 0 →
        ksDot b c = 0 → ksDot b d = 0 → ksDot c d = 0 →
        f a + f b + f c + f d = 1) := by
  rintro ⟨f, -, hf⟩
  have key : ∀ a b c d : Fin 18,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ksDotZ a b = 0 → ksDotZ a c = 0 → ksDotZ a d = 0 →
      ksDotZ b c = 0 → ksDotZ b d = 0 → ksDotZ c d = 0 →
      f a + f b + f c + f d = 1 := by
    intro a b c d h1 h2 h3 h4 h5 h6 o1 o2 o3 o4 o5 o6
    exact hf a b c d h1 h2 h3 h4 h5 h6 (ksDot_eq_zero_of_int o1) (ksDot_eq_zero_of_int o2)
      (ksDot_eq_zero_of_int o3) (ksDot_eq_zero_of_int o4) (ksDot_eq_zero_of_int o5)
      (ksDot_eq_zero_of_int o6)
  have c1 := key 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c2 := key 0 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c3 := key 7 8 2 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c4 := key 7 10 6 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c5 := key 1 4 12 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c6 := key 8 10 13 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c7 := key 15 16 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c8 := key 15 17 5 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have c9 := key 16 17 12 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  omega

end Phys

