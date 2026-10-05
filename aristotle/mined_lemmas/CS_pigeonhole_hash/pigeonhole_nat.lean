/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including module
-- docstrings, so this file is deliberately self-contained (no imports) in order to begin with
-- the header above.  A Mathlib-based generalisation to arbitrary finite types is given in
-- `RequestProject/PigeonholeHashFintype.lean`.

namespace CS

/-- The involution of `Nat` that transposes `v` and `n` and fixes everything else. -/

private theorem pigeonhole_nat : ∀ (n : Nat) (f : Nat → Nat), (∀ i < n + 1, f i < n) →
    ∃ a b, a < n + 1 ∧ b < n + 1 ∧ a ≠ b ∧ f a = f b := by
  intro n
  induction n with
  | zero => intro f hf; exact absurd (hf 0 (by omega)) (by omega)
  | succ n ih =>
    intro f hf
    have hvle : f (n + 1) ≤ n := by have := hf (n + 1) (by omega); omega
    have hlast : swapAt (f (n + 1)) n (f (n + 1)) = n := by simp [swapAt]
    by_cases hcase : ∃ i, i < n + 1 ∧ swapAt (f (n + 1)) n (f i) = n
    · obtain ⟨i, hi, hieq⟩ := hcase
      refine ⟨i, n + 1, by omega, by omega, by omega, ?_⟩
      have key : swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f i))
          = swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f (n + 1))) := by
        rw [hieq, hlast]
      rwa [swapAt_swapAt, swapAt_swapAt] at key
    · have hcase' : ∀ i, i < n + 1 → swapAt (f (n + 1)) n (f i) ≠ n :=
        fun i hi he => hcase ⟨i, hi, he⟩
      have hb : ∀ i < n + 1, swapAt (f (n + 1)) n (f i) < n := by
        intro i hi
        have h1 : f i < n + 1 := hf i (by omega)
        have h2 := swapAt_le (f (n + 1)) n (f i) hvle (by omega)
        have h3 := hcase' i hi
        omega
      obtain ⟨a, b, ha, hbb, hab, heq⟩ := ih (fun i => swapAt (f (n + 1)) n (f i)) hb
      have heq' : swapAt (f (n + 1)) n (f a) = swapAt (f (n + 1)) n (f b) := heq
      refine ⟨a, b, by omega, by omega, hab, ?_⟩
      have key : swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f a))
          = swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f b)) := by rw [heq']
      rwa [swapAt_swapAt, swapAt_swapAt] at key

/-- **Pigeonhole hash.** Any hash function from a set of `n + 1` keys into a set of `n` buckets
has a collision: there are two distinct keys with the same hash value. -/
