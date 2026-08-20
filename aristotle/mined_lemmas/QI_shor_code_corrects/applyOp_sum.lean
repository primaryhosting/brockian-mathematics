/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma applyOp_sum {ι : Type} [Fintype ι] (k : Idx) (M : Bool → Bool → ℂ) (co : ι → ℂ)
    (F : ι → Bits → ℂ) :
    applyOp k M (fun v => ∑ i, co i * F i v) = fun v => ∑ i, co i * applyOp k M (F i) v := by
  funext v
  unfold applyOp
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- For an arbitrary error `M` on an arbitrary single qubit `k`, all inner products between
code states are scaled by one and the same constant `w`.  In particular no information about
the encoded state leaks into the environment, and the error is correctable. -/
