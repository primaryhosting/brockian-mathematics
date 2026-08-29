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

theorem enum_spec {p : Nat → Prop} (hp : Unbounded p) (k : Nat) : p (enum hp k) := by
  cases k with
  | zero => exact (Classical.choose_spec (hp 0)).2
  | succ k => exact (Classical.choose_spec (hp (enum hp k))).2

