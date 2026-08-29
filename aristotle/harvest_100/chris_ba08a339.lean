import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix

variable {A B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]

/-- The reduced state (partial trace over the second subsystem `B`) of a bipartite
state `ρ` on `A ⊗ B`.  This is the object that encodes *all* statistics available to
an observer who only has access to subsystem `A`. -/
noncomputable def ptraceB (ρ : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  Matrix.of fun a a' => ∑ b, ρ (a, b) (a', b)

/-- A local quantum operation (completely positive trace preserving map given in Kraus
form) acting on subsystem `B` only, i.e. the channel `ρ ↦ ∑ i, (1 ⊗ Kᵢ) ρ (1 ⊗ Kᵢ)†`. -/
noncomputable def localOpB (K : I → Matrix B B ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => ∑ i, ∑ c, ∑ c', K i p.2 c * ρ (p.1, c) (q.1, c') * star (K i q.2 c')

/-- Helper: the Kraus completeness relation `∑ i, Kᵢ† Kᵢ = 1` written out in coordinates. -/
lemma kraus_sum_eq (K : I → Matrix B B ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) (c c' : B) :
    ∑ b, ∑ i, K i b c * star (K i b c') = if c' = c then 1 else 0 := by
  have h := congrFun (congrFun hK c') c
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] at h
  rw [Finset.sum_comm]
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

/-- **No-communication theorem** (Kraus / CPTP form).

If `ρ` is any (bipartite) state of a composite system `A ⊗ B` -- in particular an
entangled one -- and Bob performs an arbitrary local operation on his half `B`,
described by Kraus operators `K i` satisfying the completeness relation
`∑ i, (K i)ᴴ * (K i) = 1`, then Alice's reduced state, obtained by tracing out `B`,
is completely unchanged.  Since the reduced state determines every measurement
statistic accessible to Alice, no information can be transmitted from Bob to Alice
by local operations. -/
theorem no_communication (K : I → Matrix B B ℂ) (hK : ∑ i, (K i)ᴴ * (K i) = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceB (localOpB K ρ) = ptraceB ρ := by
  ext a a'
  simp only [ptraceB, localOpB, Matrix.of_apply]
  have swap : ∀ f : B → I → B → B → ℂ,
      ∑ b, ∑ i, ∑ c, ∑ c', f b i c c' = ∑ c, ∑ c', ∑ b, ∑ i, f b i c c' := by
    intro f
    have h1 : ∀ b, (∑ i, ∑ c, ∑ c', f b i c c') = ∑ c, ∑ c', ∑ i, f b i c c' := by
      intro b
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    simp only [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
  calc ∑ b, ∑ i, ∑ c, ∑ c', K i b c * ρ (a, c) (a', c') * star (K i b c')
      = ∑ c, ∑ c', ∑ b, ∑ i, K i b c * ρ (a, c) (a', c') * star (K i b c') := swap _
    _ = ∑ c, ∑ c', ρ (a, c) (a', c') * ∑ b, ∑ i, K i b c * star (K i b c') := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ c, ρ (a, c) (a', c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_eq_single c]
        · rw [kraus_sum_eq K hK c c]
          simp
        · intro c' _ hne
          rw [kraus_sum_eq K hK c c']
          simp [hne]
        · intro h
          exact absurd (Finset.mem_univ c) h

/-- Special case: a local **unitary** rotation on Bob's subsystem leaves Alice's
reduced state unchanged. -/
theorem no_communication_unitary (U : Matrix B B ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceB (localOpB (fun _ : PUnit => U) ρ) = ptraceB ρ := by
  refine no_communication _ ?_ ρ
  simpa using hU

/-- Consequence: every expectation value of every observable `M` measured by Alice
is unaffected by Bob's local operation, so Bob's choice of operation carries no
signal to Alice. -/
theorem no_communication_expectation [Fintype A] (K : I → Matrix B B ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix A A ℂ) :
    (M * ptraceB (localOpB K ρ)).trace = (M * ptraceB ρ).trace := by
  rw [no_communication K hK ρ]

end Frontier
#print axioms Frontier.no_communication

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

