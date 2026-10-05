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

theorem elt_mem (c : Nat → Nat → Bool) (n : Nat) : (seq c n).A (elt c n) :=
  (stepOf c (seq c n)).mem

