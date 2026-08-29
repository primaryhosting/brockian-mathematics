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

theorem not_unbounded {p : Nat → Prop} (h : ¬ Unbounded p) : ∃ N, ∀ m, N < m → ¬ p m := by
  apply Classical.byContradiction
  intro hcon
  apply h
  intro n
  apply Classical.byContradiction
  intro hn
  exact hcon ⟨n, fun m hnm hq => hn ⟨m, hnm, hq⟩⟩

