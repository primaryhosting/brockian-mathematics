/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Pigeonhole principle in arithmetic form: a function `f : Nat → Nat` sending each of the
`n + 1` indices `0, …, n` into `{0, …, n - 1}` cannot be injective on those indices. -/

theorem exists_collision_nat :
    ∀ n : Nat, ∀ f : Nat → Nat, (∀ i, i < n + 1 → f i < n) →
      ∃ i j, i < n + 1 ∧ j < n + 1 ∧ i ≠ j ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
      intro f hf
      exact absurd (hf 0 (by omega)) (by omega)
  | succ n ih =>
      intro f hf
      by_cases hcase : ∃ i, i < n + 1 ∧ f i = f (n + 1)
      · obtain ⟨i, hi, hfi⟩ := hcase
        exact ⟨i, n + 1, by omega, by omega, by omega, hfi⟩
      · -- No earlier index collides with the last one, so we may re-route the value `n`
        -- to the (unused) value `f (n+1)` and apply the inductive hypothesis.
        have hne : ∀ i, i < n + 1 → f i ≠ f (n + 1) := fun i hi hEq => hcase ⟨i, hi, hEq⟩
        have hvle : f (n + 1) ≤ n := by
          have := hf (n + 1) (by omega); omega
        have hg : ∀ i, i < n + 1 → (if f i = n then f (n + 1) else f i) < n := by
          intro i hi
          have h1 : f i < n + 1 := hf i (by omega)
          have h2 : f i ≠ f (n + 1) := hne i hi
          by_cases h3 : f i = n
          · rw [if_pos h3]
            omega
          · rw [if_neg h3]
            omega
        obtain ⟨i, j, hi, hj, hij, hEq⟩ :=
          ih (fun i => if f i = n then f (n + 1) else f i) hg
        refine ⟨i, j, by omega, by omega, hij, ?_⟩
        have h2i : f i ≠ f (n + 1) := hne i hi
        have h2j : f j ≠ f (n + 1) := hne j hj
        have hEq : (if f i = n then f (n + 1) else f i)
            = (if f j = n then f (n + 1) else f j) := hEq
        by_cases h3 : f i = n <;> by_cases h4 : f j = n
        · omega
        · rw [if_pos h3, if_neg h4] at hEq
          exact absurd hEq.symm h2j
        · rw [if_neg h3, if_pos h4] at hEq
          exact absurd hEq h2i
        · rw [if_neg h3, if_neg h4] at hEq
          exact hEq

/-- **Pigeonhole hash**: any hash function from a set of `n + 1` keys to `n` buckets
has a collision, i.e. two distinct keys with the same hash value. -/
