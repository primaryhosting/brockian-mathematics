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

theorem elt_lt (c : Nat → Nat → Bool) {m n : Nat} (h : m < n) : elt c m < elt c n :=
  (seq_succ_apply c m _ (seq_mono c h (elt_mem c n))).2

