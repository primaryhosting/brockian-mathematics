/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A predicate on `Nat` is `Unbounded` when it holds arbitrarily far out; for subsets of `Nat`
this is exactly the same as being infinite. -/

theorem enum_lt_succ {p : Nat → Prop} (hp : Unbounded p) (k : Nat) :
    enum hp k < enum hp (k + 1) :=
  (Classical.choose_spec (hp (enum hp k))).1

