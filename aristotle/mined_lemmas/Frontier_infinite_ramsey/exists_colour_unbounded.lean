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

theorem exists_colour_unbounded (c : Nat → Nat → Bool) {p : Nat → Prop} (hp : Unbounded p) (a : Nat) :
    ∃ b : Bool, Unbounded (fun x => p x ∧ c a x = b) := by
  by_cases h : Unbounded (fun x => p x ∧ c a x = true)
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    obtain ⟨N, hN⟩ := not_unbounded h
    intro n
    obtain ⟨m, hm1, hm2⟩ := hp (max n N)
    refine ⟨m, by omega, hm2, ?_⟩
    have hmN := hN m (by omega)
    cases hb : c a m with
    | false => rfl
    | true => exact absurd ⟨hm2, hb⟩ hmN

/-- A state of the construction: an infinite set of naturals. -/
structure State (c : Nat → Nat → Bool) where
  /-- The current infinite set. -/
  p : Nat → Prop
  /-- Proof that it is infinite. -/
  hp : Unbounded p

variable {c : Nat → Nat → Bool}

/-- A distinguished point of the current set. -/
