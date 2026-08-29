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

noncomputable def elt (c : Nat → Nat → Bool) (n : Nat) : Nat := (stepOf c (seq c n)).a

/-- The colour with which the `n`-th point is joined to all later chosen points. -/
