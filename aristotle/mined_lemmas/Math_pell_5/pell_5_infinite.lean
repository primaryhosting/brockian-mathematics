import Mathlib

/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
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

namespace Math

/-- **Pell's equation for `d = 5`**: `x² - 5·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).  The witness is `(x, y) = (9, 4)`. -/

theorem pell_5_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 5 * p.2 ^ 2 = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => pellSeq5 n) (fun a b hab => ?_) (fun n => (pellSeq5_spec n).1)
  exact pellSeq5_snd_strictMono.injective (congrArg Prod.snd hab)

end Math

