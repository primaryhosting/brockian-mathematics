/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `Unbdd A` says that the set of naturals satisfying `A` is unbounded, i.e. infinite. -/

noncomputable def stepOf (c : Nat → Nat → Bool) (s : St c) : StepData c s.A :=
  Classical.choice (stepData_nonempty c s.A s.hA)

/-- The sequence of nested unbounded sets produced by the construction. -/
