/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

theorem reingold_hypotheses_satisfiable (c d : ℕ) (hc : 0 < c) :
    ∃ nbr : Fin (2 ^ d) → Fin (2 ^ d) → Fin (2 ^ d),
      (∀ (v : Fin (2 ^ d)) (e : Fin (2 ^ d)), ∃ e' : Fin (2 ^ d), nbr (nbr v e) e' = v) ∧
      (∀ u v : Fin (2 ^ d), Reach nbr u v →
        ReachWithin nbr u v (c * (Nat.log 2 (2 ^ d) + 1))) ∧
      (∀ u v : Fin (2 ^ d), Reach nbr u v) := by
  refine ⟨fun _ e => e, fun v _ => ⟨v, rfl⟩, fun u v _ => ⟨fun _ => v, 1, ?_, rfl⟩,
    fun u v => ⟨fun _ => v, 1, rfl⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))

end CS

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

