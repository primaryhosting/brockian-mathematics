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
def ksVec : Fin 18 → EuclideanSpace ℝ (Fin 4) :=
  ![ !₂[0, 0, 0, 1],      -- 0
     !₂[0, 0, 1, 0],      -- 1
     !₂[1, 1, 0, 0],      -- 2
     !₂[1, -1, 0, 0],     -- 3
     !₂[0, 1, 0, 0],      -- 4
     !₂[1, 0, 1, 0],      -- 5
     !₂[1, 0, -1, 0],     -- 6
     !₂[1, 0, 0, 1],      -- 7
     !₂[1, 0, 0, -1],     -- 8
     !₂[0, 0, 1, 1],      -- 9
     !₂[1, -1, 1, -1],    -- 10
     !₂[1, -1, -1, 1],    -- 11
     !₂[1, 1, 1, -1],     -- 12
     !₂[1, 1, -1, 1],     -- 13
     !₂[0, 1, 0, 1],      -- 14
     !₂[1, 1, -1, -1],    -- 15
     !₂[1, -1, 1, 1],     -- 16
     !₂[0, 1, 1, 0] ]     -- 17

/-- The 9 orthogonal bases of the Kochen–Specker set, given as quadruples of indices into
`Phys.ksVec`.  Every one of the 18 vectors occurs in exactly two of these bases. -/
def ksBasis : Fin 9 → Fin 4 → Fin 18 :=
  ![ ![0, 1, 2, 3],
     ![0, 4, 5, 6],
     ![1, 4, 7, 8],
     ![9, 2, 10, 11],
     ![9, 12, 13, 3],
     ![14, 5, 15, 11],
     ![14, 6, 12, 16],
     ![17, 7, 15, 10],
     ![17, 8, 13, 16] ]

/-- All 18 vectors of the set are nonzero. -/
theorem ksVec_ne_zero (j : Fin 18) : ksVec j ≠ 0 := by
  fin_cases j <;>
    · intro h
      have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 0) h
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 1) h
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 2) h
      have h3 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 3) h
      simp [ksVec] at h0 h1 h2 h3

/-- Within each of the nine listed quadruples, the vectors are pairwise orthogonal; hence each
quadruple really is an orthogonal basis of `ℝ⁴`. -/
theorem ksBasis_orthogonal (i : Fin 9) (a b : Fin 4) (hab : a ≠ b) :
    inner ℝ (ksVec (ksBasis i a)) (ksVec (ksBasis i b)) = 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp_all [ksVec, ksBasis, PiLp.inner_apply, Fin.sum_univ_four]

/-- The vectors occurring in a single basis are pairwise distinct. -/
theorem ksBasis_injective (i : Fin 9) : Function.Injective (ksBasis i) := by
  intro a b hab
  by_contra hne
  have h := ksBasis_orthogonal i a b hne
  rw [hab] at h
  have := (inner_self_eq_zero (𝕜 := ℝ)).1 h
  exact ksVec_ne_zero (ksBasis i b) this

/-- **Kochen–Specker (18 vectors, 9 bases).**  There is no `{0,1}`-coloring of `ℝ⁴` which assigns
the value `1` to exactly one vector in each of the nine orthogonal bases of the
Cabello–Estebaranz–García-Alcaine configuration. -/
theorem kochen_specker_18 :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 4) → ℕ,
        (∀ v : EuclideanSpace ℝ (Fin 4), f v = 0 ∨ f v = 1) ∧
        ∀ i : Fin 9, ∑ a : Fin 4, f (ksVec (ksBasis i a)) = 1 := by
  rintro ⟨f, -, h⟩
  set c : Fin 18 → ℕ := fun j => f (ksVec j) with hc
  have key : ∀ i : Fin 9, ∑ a : Fin 4, c (ksBasis i a) = 1 := h
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
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

end Phys

#print axioms Phys.kochen_specker_18
#print axioms Phys.ksBasis_orthogonal
#print axioms Phys.ksVec_ne_zero
#print axioms Phys.ksBasis_injective

