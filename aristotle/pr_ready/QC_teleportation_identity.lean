/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Statement: The teleportation protocol's post-correction state equals the input state.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma invSqrt2_conj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2]

lemma invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrt2, ← Complex.ofReal_mul, h]
  norm_num

/-- The `±1` sign `(-1)^(a*i)` occurring in the Pauli `Z` operator. -/
def sgn (a i : Bool) : ℂ := if a && i then -1 else 1

/-- Amplitudes of the Bell basis state `|B_{a,b}⟩ = (1/√2) Σ_i (-1)^(a i) |i, i ⊕ b⟩`
on the two-qubit computational basis. -/
noncomputable def bell (a b i j : Bool) : ℂ :=
  invSqrt2 * sgn a i * (if j = xor i b then 1 else 0)

/-- The initial three-qubit state `|ψ⟩ ⊗ |B_{0,0}⟩`, where qubit `1` carries the
unknown state `ψ` and qubits `2,3` are a shared EPR pair. -/
noncomputable def init (psi : Bool → ℂ) (i j k : Bool) : ℂ :=
  psi i * invSqrt2 * (if j = k then 1 else 0)

/-- The (unnormalized) state of the receiver's qubit after a Bell measurement with
outcome `(a, b)` on the first two qubits. -/
noncomputable def measured (psi : Bool → ℂ) (a b k : Bool) : ℂ :=
  ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bell a b i j) * init psi i j k

/-- The receiver's state after applying the Pauli correction `Z^a X^b` dictated by the
classical outcome `(a, b)` and renormalizing (the measurement outcome has probability
`1/4`, so the correct normalization factor is `2`). -/
noncomputable def corrected (psi : Bool → ℂ) (a b k : Bool) : ℂ :=
  2 * (sgn a k * measured psi a b (xor k b))

/-- **Teleportation identity.** For every input qubit state `ψ` and every Bell-measurement
outcome `(a, b)`, the receiver's post-correction state equals the input state `ψ`. -/
theorem teleportation_identity (psi : Bool → ℂ) (a b : Bool) :
    corrected psi a b = psi := by
  funext k
  cases a <;> cases b <;> cases k <;>
    simp [corrected, measured, bell, init, sgn, invSqrt2_conj] <;>
    ring_nf <;>
    rw [show invSqrt2 ^ 2 = invSqrt2 * invSqrt2 from sq invSqrt2, invSqrt2_sq] <;> ring

section Sanity

/-- Sanity check: without the Pauli correction the receiver's state is genuinely wrong,
e.g. for outcome `(a, b) = (false, true)` it is the bit-flipped input. -/
example (psi : Bool → ℂ) (k : Bool) :
    2 * measured psi false true k = psi (xor k true) := by
  cases k <;>
    simp [measured, bell, init, sgn, invSqrt2_conj] <;>
    ring_nf <;>
    rw [show invSqrt2 ^ 2 = invSqrt2 * invSqrt2 from sq invSqrt2, invSqrt2_sq] <;> ring

end Sanity

end QC

#print axioms QC.teleportation_identity


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

