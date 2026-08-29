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

theorem exists_constant_colour (s : State c) :
    ∃ b : Bool, Unbounded (fun k => s.bcol k = b) := by
  by_cases h : Unbounded (fun k => s.bcol k = true)
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    obtain ⟨N, hN⟩ := not_unbounded h
    intro n
    refine ⟨max n N + 1, by omega, ?_⟩
    have hmN := hN (max n N + 1) (by omega)
    cases hb : s.bcol (max n N + 1) with
    | false => exact hb
    | true => exact absurd hb hmN

/-- A strictly increasing enumeration of an infinite set. -/
