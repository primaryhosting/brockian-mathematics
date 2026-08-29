/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem Frontier.Aronszajn_tree_exists :
    ∃ (T : Type 1) (inst : PartialOrder T) (ht : T → Ordinal.{0}), @IsAronszajnTree T inst ht := by
  refine ⟨Node, inferInstance, Node.len, ?_⟩
  exact
    { ht_lt_omega1 := fun s => s.len_lt
      ht_strictMono := fun _ _ h => Node.len_lt_len_of_lt h
      pred_linear := Node.pred_linear
      pred_exists := Node.pred_exists
      levels_nonempty := fun α hα => ⟨Node.canonical α hα, rfl⟩
      levels_countable := Node.level_countable
      chains_countable := Node.chain_countable }

import Mathlib
import RequestProject.Aronszajn

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

