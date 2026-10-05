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

theorem seq_succ_apply (c : Nat → Nat → Bool) (n b : Nat) (hb : (seq c (n + 1)).A b) :
    (seq c n).A b ∧ elt c n < b :=
  (stepOf c (seq c n)).sub b hb

