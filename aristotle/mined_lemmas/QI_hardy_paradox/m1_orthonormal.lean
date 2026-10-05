import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
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

namespace QI

open MeasureTheory

/-! ## The local hidden variable (local realism) side

In a local hidden variable model every run of the experiment is described by a hidden
variable `ω`, and the outcome of each of the two possible measurements on each side is a
definite function of `ω`: `A₁, A₂ : Ω → Bool` for Alice and `B₁, B₂ : Ω → Bool` for Bob
(locality: Alice's outcomes do not depend on Bob's setting and vice versa). -/

/-- **Hardy's no-go for local realism.**  If the three "Hardy constraints" hold with
probability one, namely `P(A₁ = 1, B₂ = 1) = 0`, `P(A₂ = 1, B₁ = 1) = 0` and
`P(A₂ = 0, B₂ = 0) = 0`, then the Hardy event `A₁ = 1, B₁ = 1` must have probability
zero.  (The pointwise argument: if `A₁ ω = 1` and `B₁ ω = 1`, then `B₂ ω = 0` by the
first constraint and `A₂ ω = 0` by the second, contradicting the third.) -/

theorem m1_orthonormal :
    (∑ i : Fin 2, Complex.normSq (m1one i)) = 1 ∧
      (∑ i : Fin 2, Complex.normSq (m1zero i)) = 1 ∧
      (∑ i : Fin 2, (starRingEnd ℂ) (m1one i) * m1zero i) = 0 := by
  have h2 := sqrt_two_sq
  have h2' := sqrt_two_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_two, m1one, m1zero, Complex.normSq_ofReal] <;>
    field_simp <;> linarith [h2]

/-- The two outcome vectors of the second setting form an orthonormal basis of `ℂ²`. -/
