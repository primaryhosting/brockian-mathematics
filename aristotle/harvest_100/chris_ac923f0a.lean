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

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
given with integer coordinates. -/
def ksVecInt : Fin 18 → Fin 4 → ℤ :=
  ![ ![0, 0, 0, 1],    -- 0
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
     ![1, 1, -1, 1],   -- 14
     ![1, 1, 1, -1],   -- 15
     ![-1, 1, 1, 1],   -- 16
     ![0, 1, -1, 0] ]  -- 17

/-- The 18 vectors of the Kochen–Specker set, as real vectors in `ℝ⁴`. -/
def ksVec (i : Fin 18) : Fin 4 → ℝ := fun t => ((ksVecInt i t : ℤ) : ℝ)

/-- The nine orthogonal bases (contexts), given as quadruples of indices of vectors. -/
def ksCtx : Fin 9 → Fin 4 → Fin 18 :=
  ![ ![0, 1, 2, 3],
     ![0, 4, 5, 6],
     ![7, 8, 2, 9],
     ![7, 10, 6, 11],
     ![1, 4, 12, 13],
     ![8, 10, 13, 17],
     ![14, 15, 3, 9],
     ![14, 16, 5, 11],
     ![15, 16, 12, 17] ]

/-- All 18 vectors are nonzero. -/
theorem ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  intro h
  have h4 : ∀ t : Fin 4, ksVecInt i t = 0 := by
    intro t
    have := congrFun h t
    simpa [ksVec] using this
  clear h
  revert h4
  revert i
  decide

/-- The 18 vectors are pairwise distinct. -/
theorem ksVec_injective : Function.Injective ksVec := by
  intro i j h
  have hInt : ksVecInt i = ksVecInt j := by
    funext t
    have := congrFun h t
    simpa [ksVec] using this
  clear h
  revert hInt
  revert i j
  decide

/-- Each of the nine contexts consists of four pairwise orthogonal vectors. -/
theorem ksCtx_orthogonal (i : Fin 9) (j k : Fin 4) (h : j ≠ k) :
    ∑ t : Fin 4, ksVec (ksCtx i j) t * ksVec (ksCtx i k) t = 0 := by
  have key : ∀ a b : Fin 18, (∑ t : Fin 4, ksVecInt a t * ksVecInt b t = 0) →
      ∑ t : Fin 4, ksVec a t * ksVec b t = 0 := by
    intro a b hab
    have : ((∑ t : Fin 4, ksVecInt a t * ksVecInt b t : ℤ) : ℝ) = 0 := by
      rw [hab]; norm_num
    simpa [ksVec, Fin.sum_univ_four] using this
  refine key _ _ ?_
  revert h
  revert i j k
  decide

/-- Counting lemma: if exactly one of four booleans is true, the corresponding
`0/1` values sum to one. -/
private lemma exactly_one_sum (p : Fin 4 → Bool) (j : Fin 4) (hj : p j = true)
    (hu : ∀ y : Fin 4, p y = true → y = j) :
    (cond (p 0) 1 0) + (cond (p 1) 1 0) + (cond (p 2) 1 0) + (cond (p 3) 1 0) = (1 : ℕ) := by
  revert hj hu
  revert j
  revert p
  decide

/--
**Kochen–Specker theorem (18-vector version).**
The explicit set of 18 vectors in `ℝ⁴` above, grouped into nine orthogonal bases,
admits no `{0,1}`-coloring assigning to each vector a value in `{false, true}`
such that each of the nine bases contains exactly one vector coloured `true`.
-/
theorem kochen_specker_18 :
    ¬ ∃ f : (Fin 4 → ℝ) → Bool, ∀ i : Fin 9, ∃! j : Fin 4, f (ksVec (ksCtx i j)) = true := by
  rintro ⟨f, hf⟩
  set a : Fin 18 → ℕ := fun k => cond (f (ksVec k)) 1 0
  have key : ∀ i : Fin 9,
      a (ksCtx i 0) + a (ksCtx i 1) + a (ksCtx i 2) + a (ksCtx i 3) = 1 := by
    intro i
    obtain ⟨j, hj, hu⟩ := hf i
    exact exactly_one_sum (fun j => f (ksVec (ksCtx i j))) j hj hu
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  have h6 := key 6
  have h7 := key 7
  have h8 := key 8
  simp only [ksCtx, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

end Phys

import Mathlib

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

