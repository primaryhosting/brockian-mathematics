import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

/-- Cauchy–Schwarz in the form `|⟪f, g⟫| ≤ ‖f‖ ‖g‖` for finite sums of reals. -/

lemma sum_centered_indicator {V : Type*} [Fintype V] (S : Finset V)
    (hn : (0 : ℝ) < Fintype.card V) :
    ∑ i, ((if i ∈ S then (1 : ℝ) else 0) - S.card / Fintype.card V) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- The squared norm of the centered indicator vector of `S` is at most `|S|`. -/
