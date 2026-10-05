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

import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real

/-- Shannon entropy (in nats) of a probability distribution `p` on a finite type,
`H(p) = -∑ i, p i * log (p i)`, written with Mathlib's `Real.negMulLog`. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- A *deterministic* (fully erased) state — every outcome has probability `0` or `1` —
carries zero entropy. -/
theorem shannonEntropy_eq_zero_of_deterministic {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, q i = 0 ∨ q i = 1) : shannonEntropy q = 0 := by
  unfold shannonEntropy
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases hq i with h | h <;> simp [h, Real.negMulLog]

/-- The uniform distribution on two states (one bit) has entropy `log 2` nats. -/
theorem shannonEntropy_uniform_two (p : Fin 2 → ℝ) (hp : ∀ i, p i = 1 / 2) :
    shannonEntropy p = Real.log 2 := by
  unfold shannonEntropy
  simp only [hp, Fin.sum_univ_two, Real.negMulLog]
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- **Landauer's principle.**

Consider a one-bit memory in contact with a heat bath at temperature `T > 0`, with Boltzmann
constant `k > 0`.  Initially the bit is in the uniform distribution over its two states
(`p i = 1/2`), and after the erasure operation the memory is in a deterministic state
(`q i ∈ {0, 1}` for each outcome).  Let `Q` be the heat dissipated into the bath, so that the
bath's entropy change is `Q / T`.

The second law (`hsecond`: the total entropy change of system plus bath is non-negative) then
forces
`Q ≥ k * T * log 2`,
i.e. erasing one bit dissipates at least `kT log 2` of heat.

(Positivity of the Boltzmann constant `k` is not needed for the derivation, so it is not
assumed.) -/
theorem landauer_principle
    (k T Q : ℝ) (hT : 0 < T)
    (p q : Fin 2 → ℝ)
    (hp : ∀ i, p i = 1 / 2)
    (hq : ∀ i, q i = 0 ∨ q i = 1)
    (hsecond : 0 ≤ Q / T + k * (shannonEntropy q - shannonEntropy p)) :
    k * T * Real.log 2 ≤ Q := by
  rw [shannonEntropy_uniform_two p hp, shannonEntropy_eq_zero_of_deterministic q hq] at hsecond
  have h : k * Real.log 2 ≤ Q / T := by nlinarith [hsecond]
  calc k * T * Real.log 2 = (k * Real.log 2) * T := by ring
    _ ≤ (Q / T) * T := by nlinarith
    _ = Q := by field_simp

#print axioms Phys.landauer_principle

end Phys

