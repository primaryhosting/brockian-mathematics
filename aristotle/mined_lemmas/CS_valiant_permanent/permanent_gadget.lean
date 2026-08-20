import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem permanent_gadget : (gadget W).permanent = W.permanent := by
  classical
  rw [permanent_eq_card_witnesses (gadget W) (gadget_zeroOne W), permanent_eq_sum W,
    ← Nat.card_eq_of_bijective _ (gPerm_bijective W)]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_pi]

end Simulation

/-! ## Main statement -/

/--
**Valiant's theorem on the 0/1 permanent** (core formalized content).

The two components proved here are:

1. *Membership in `#P`.*  For a matrix with entries in `{0,1}`, the permanent is literally a
   counting function: it equals the number of permutations `σ` satisfying the explicitly
   checkable condition `∀ i, M i (σ i) = 1` (equivalently, the number of perfect matchings of
   the associated bipartite graph, or the number of cycle covers of the associated digraph).

2. *0/1 entries are as hard as arbitrary nonnegative integer weights.*  For every matrix `W`
   with natural number entries there is an explicit `0/1` matrix `B`, of size
   `n + ∑ i, ∑ j, W i j`, with `B.permanent = W.permanent`.  Thus computing permanents of 0/1
   matrices is as hard as computing permanents of arbitrary nonnegative integer matrices
   (the size of `B` is linear in the total weight, i.e. polynomial in the unary encoding of `W`).

*Scope.*  These are the two statements about the 0/1 permanent that can be phrased purely
matrix-theoretically, without fixing a machine model.  The remaining ingredient of Valiant's
theorem — the gadget reduction turning a Boolean formula `φ` into a weighted matrix whose
permanent determines the number of satisfying assignments of `φ` — is not formalized here.
-/
