/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n A : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]

/-- A *code* is given by the orthogonal projection `P` onto the code subspace: `P` is
self-adjoint, idempotent, and nonzero (the code subspace is nontrivial). -/
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  nontrivial : P ≠ 0

/-- The error set `E` is the Kraus family of a quantum channel (trace preserving). -/

lemma corrects_of_isRecovery {K : Type*} [Fintype K] {P : Matrix n n ℂ} {E : A → Matrix n n ℂ}
    {R : K → Matrix n n ℂ} (h : IsRecovery P E R) : Corrects P E := by
  refine ⟨Fintype.card K, R ∘ (Fintype.equivFin K).symm, ?_, ?_⟩
  · rw [← h.1]
    exact Equiv.sum_comp (Fintype.equivFin K).symm (fun k => (R k)ᴴ * R k)
  · intro rho hrho
    exact (Equiv.sum_comp (Fintype.equivFin K).symm
      (fun k => ∑ a, R k * E a * rho * (E a)ᴴ * (R k)ᴴ)).trans (h.2 rho hrho)

