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

noncomputable def enum {p : Nat → Prop} (hp : Unbounded p) : Nat → Nat
  | 0 => Classical.choose (hp 0)
  | k + 1 => Classical.choose (hp (enum hp k))

