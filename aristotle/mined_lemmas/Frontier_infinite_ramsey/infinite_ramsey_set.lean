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

theorem infinite_ramsey_set (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (k : Bool), S.Infinite ∧ ∀ a ∈ S, ∀ b ∈ S, a < b → c a b = k := by
  obtain ⟨S, k, hS, hmono⟩ := Frontier.infinite_ramsey c
  refine ⟨{n | S n}, k, Set.infinite_of_forall_exists_gt fun a => ?_, ?_⟩
  · obtain ⟨m, hm, hSm⟩ := hS a
    exact ⟨m, hSm, hm⟩
  · exact fun a ha b hb hab => hmono a b ha hb hab

end Frontier

