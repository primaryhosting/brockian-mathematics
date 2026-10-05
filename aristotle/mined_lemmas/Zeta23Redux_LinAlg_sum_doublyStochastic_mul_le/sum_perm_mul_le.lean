import Mathlib

/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
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

namespace Zeta23Redux.LinAlg

open Finset Matrix

/-- Rearrangement inequality: for antitone weights, permuting one of them cannot increase the
pairing sum. -/

lemma sum_perm_mul_le {n : ℕ} (σ : Equiv.Perm (Fin n)) {mu nu : Fin n → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, mu i * nu (σ i) ≤ ∑ i, mu i * nu i := by
  simpa [smul_eq_mul] using (hmu.monovary hnu).sum_smul_comp_perm_le_sum_smul (σ := σ)

/--
**Rearrangement / Birkhoff step.**
If `S` is a doubly stochastic matrix and `mu`, `nu` are antitone weight sequences, then
`∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i`.
-/
