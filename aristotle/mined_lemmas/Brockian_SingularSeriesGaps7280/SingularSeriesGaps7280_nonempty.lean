import Mathlib
/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other piece of syntax,
-- including module doc comments, so the required header appears immediately after
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

namespace Brockian

/-- A finite set of natural numbers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues of the
elements of `H` do not cover all of `ZMod p`.  Equivalently, the local factor of the
singular series attached to `H` at `p` is nonzero for every prime `p`. -/

theorem SingularSeriesGaps7280_nonempty :
    ((Finset.Ico 7281 (7281 + 7280)).filter Nat.Prime).Nonempty := by
  refine ⟨7283, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

end Brockian

