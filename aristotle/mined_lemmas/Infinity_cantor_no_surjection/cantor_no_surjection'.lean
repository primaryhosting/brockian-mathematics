import Mathlib

/-!
# Cantor No Surjection
Category: Frontier — Set Theory
Target: Infinity.cantor_no_surjection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module docstrings (`/-! ... -/`), so the header block above is placed directly after
-- the single `import Mathlib` line.

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

namespace Infinity

/-- **Cantor's theorem**: for any type `X`, no function `f : X → Set X` is surjective.

The proof considers the diagonal set `D = {i | i ∉ f i}`.  If `f` were surjective there
would be some `j` with `f j = D`; splitting on whether `j ∈ f j` holds gives a
contradiction in both branches. -/

theorem cantor_no_surjection' {X : Type*} (f : X → Set X) : ¬ Function.Surjective f :=
  fun hf => Function.cantor_surjective f hf

end Infinity

