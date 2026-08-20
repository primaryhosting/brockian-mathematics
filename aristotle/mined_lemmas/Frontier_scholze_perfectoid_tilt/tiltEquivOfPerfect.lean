/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
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

namespace Frontier

/-! ## The tilt: inverse limit along Frobenius -/

section Tilt

variable (p : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] [CharP R p]

/-- The **tilt** of a commutative ring `R` of characteristic `p`: the inverse limit
`lim_{x ↦ x^p} R`, realised as the subring of sequences `f : ℕ → R` satisfying
`f (n+1) ^ p = f n`. -/

noncomputable def tiltEquivOfPerfect : R ≃+* Tilt p R := by
  refine
    { toFun := fun x => ⟨fun n => (pRoot hperf)^[n] x, ?_⟩
      invFun := fun f => (f : ℕ → R) 0
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · intro n
    show ((pRoot hperf)^[n + 1] x) ^ p = (pRoot hperf)^[n] x
    rw [Function.iterate_succ_apply', pRoot_pow]
  · intro x; rfl
  · intro f
    apply Subtype.ext
    funext n
    show (pRoot hperf)^[n] ((f : ℕ → R) 0) = (f : ℕ → R) n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← f.2 n, pRoot_of_pow]
  · intro x y
    apply Subtype.ext
    funext n
    show (pRoot hperf)^[n] (x * y) = ((pRoot hperf)^[n] x) * ((pRoot hperf)^[n] y)
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply', ih]
      exact map_mul (pRoot hperf) _ _
  · intro x y
    apply Subtype.ext
    funext n
    show (pRoot hperf)^[n] (x + y) = ((pRoot hperf)^[n] x) + ((pRoot hperf)^[n] y)
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply', ih]
      exact map_add (pRoot hperf) _ _

