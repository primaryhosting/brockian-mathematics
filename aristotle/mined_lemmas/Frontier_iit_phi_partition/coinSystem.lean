import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/

noncomputable def coinSystem (V : Type*) [Fintype V] [DecidableEq V] : System V where
  E := fun _ _ => False
  f := fun _ _ _ => 1 / 2
  f_nonneg := by norm_num
  f_sum := by norm_num
  f_local := by intro v s s' _; rfl

/-- The two-node system of independent coins is disconnected, hence has `Φ = 0`. -/
example : Phi (coinSystem Bool) = 0 := by
  refine iit_phi_partition _ {true} ⟨true, by decide⟩ ⟨false, by decide⟩ ?_
  intro u v hE
  exact absurd hE (by simp [coinSystem])

end Frontier

