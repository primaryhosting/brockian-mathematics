/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ### Arithmetic in `ZMod 2` -/


lemma chi_flipAt {k : ℕ} (s x : Cube k) (i : Fin k) :
    chi s (flipAt x i) = sgn (s i) * chi s x := by
  classical
  unfold chi
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => sgn (s j * x j)) (Finset.mem_univ i)]
  have h1 : sgn (s i * flipAt x i i) = sgn (s i) * sgn (s i * x i) := by
    rw [flipAt_self, mul_add, mul_one, add_comm, sgn_add]
  rw [h1]
  have h2 : ∀ j ∈ Finset.univ.erase i, sgn (s j * flipAt x i j) = sgn (s j * x j) := by
    intro j hj
    rw [flipAt_of_ne _ (Finset.mem_erase.mp hj).1]
  rw [Finset.prod_congr rfl h2]
  ring

