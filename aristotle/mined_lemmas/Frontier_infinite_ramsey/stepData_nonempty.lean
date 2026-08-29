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

theorem stepData_nonempty (c : Nat → Nat → Bool) (A : Nat → Prop) (hA : Unbdd A) :
    Nonempty (StepData c A) := by
  obtain ⟨a, -, hAa⟩ := hA 0
  have hA' : Unbdd (fun b => A b ∧ a < b) := by
    intro n
    obtain ⟨m, hm, hAm⟩ := hA (n + a)
    exact ⟨m, by omega, hAm, by omega⟩
  obtain ⟨k, hk⟩ := unbdd_split _ (fun b => c a b) hA'
  exact ⟨{ a := a
           k := k
           B := fun b => (A b ∧ a < b) ∧ c a b = k
           mem := hAa
           sub := fun b hb => hb.1
           unbdd := hk
           colour := fun b hb => hb.2 }⟩

/-- The state of the construction: an unbounded set together with a proof of unboundedness. -/
structure St (c : Nat → Nat → Bool) where
  A : Nat → Prop
  hA : Unbdd A

