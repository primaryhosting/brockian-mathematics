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

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma card_queries_le {T : DTree n} {d : ℕ} (hd : DepthLE T d) (f : Vec n → ℕ) :
    (T.queries f).card ≤ d := by
  induction hd with
  | leaf out d => simp [queries]
  | node q k d h ih =>
      have hle := ih (f q)
      calc (queries f (.node q k)).card
          ≤ (queries f (k (f q))).card + 1 := by
            simpa [queries] using Finset.card_insert_le q (queries f (k (f q)))
        _ ≤ d + 1 := by omega

/-- If two oracles agree on all points queried along the path of the first, the tree
behaves identically on both. -/
