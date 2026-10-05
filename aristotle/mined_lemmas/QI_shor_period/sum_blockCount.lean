import Mathlib
/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

open Finset Complex

/-!
## The Shor sampling distribution

We model the period-finding core of Shor's algorithm.  Fix a modulus `N`, a unit
`u : (ZMod N)ˣ` and a power-of-two-sized (any size, really) register `Q`.
The algorithm prepares

  `Q^{-1/2} ∑_{j < Q} |j⟩ |u ^ j⟩`,

applies the quantum Fourier transform modulo `Q` to the first register and
measures.  The probability of observing `c` in the first register and `y` in the
second one is `Q^{-2} ‖∑_{j < Q, u ^ j = y} e^{2πι c j / Q}‖^2`, so the marginal
probability of observing `c` is the following quantity.
-/

/-- Probability that Shor's period-finding circuit, run with modulus `N`, base `u`
and register size `Q`, outputs the value `c`. -/

lemma sum_blockCount {Q r : ℕ} (hr : 0 < r) (hrQ : r ≤ Q) :
    ∑ k ∈ range r, blockCount Q r k = Q := by
  have h : (range Q).card = ∑ k ∈ range r, ((range Q).filter (fun j => j % r = k)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x _
    simp [Nat.mod_lt _ hr]
  have h2 : ∑ k ∈ range r, blockCount Q r k
      = ∑ k ∈ range r, ((range Q).filter (fun j => j % r = k)).card := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [fiberNat_eq hr (lt_of_lt_of_le hk hrQ) hk,
      Finset.card_image_of_injective _ (add_mul_injective hr k), Finset.card_range]
  rw [h2, ← h, Finset.card_range]

/-! ### A lower bound for a truncated geometric sum of phases -/

