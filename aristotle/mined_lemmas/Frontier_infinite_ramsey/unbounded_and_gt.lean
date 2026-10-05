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

theorem unbounded_and_gt {p : Nat → Prop} (hp : Unbounded p) (a : Nat) :
    Unbounded (fun x => p x ∧ a < x) := by
  intro n
  obtain ⟨m, hm1, hm2⟩ := hp (max n a)
  exact ⟨m, by omega, hm2, by omega⟩

/-- Given an infinite set `p` and a point `a`, one of the two colour classes of `a` inside `p`
is again infinite. -/
