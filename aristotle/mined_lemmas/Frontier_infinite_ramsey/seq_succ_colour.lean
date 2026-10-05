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

theorem seq_succ_colour (c : Nat → Nat → Bool) (n b : Nat) (hb : (seq c (n + 1)).A b) :
    c (elt c n) b = col c n :=
  (stepOf c (seq c n)).colour b hb

