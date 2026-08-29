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

theorem unbounded_iff_infinite (S : Set ℕ) : Unbounded (fun x => x ∈ S) ↔ S.Infinite := by
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt fun a => ?_
    obtain ⟨m, hm, hmS⟩ := h a
    exact ⟨m, hmS, hm⟩
  · intro h a
    obtain ⟨m, hmS, hm⟩ := h.exists_gt a
    exact ⟨m, hm, hmS⟩

/-- **Infinite Ramsey theorem** (pairs, two colours), phrased with `Set.Infinite`:
every 2-colouring of `[ℕ]²` admits an infinite monochromatic set. -/
