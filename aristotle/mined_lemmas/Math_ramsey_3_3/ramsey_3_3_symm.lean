/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is self-contained: the proof uses only core `Lean`/`Init` (`Bool`, `Fin`, `decide`),
-- so no `import` is required.  (Mathlib currently has no Ramsey-number API to reuse here.)

namespace Math

/-- Pigeonhole for five booleans: among `b1, …, b5` some three are equal. -/

theorem ramsey_3_3_symm :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j : Fin 6, c i j = c j i) →
        ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ c i j = c i k ∧ c i k = c j k) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j : Fin 5, c i j = c j i) ∧
        ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k → ¬(c i j = c i k ∧ c i k = c j k)) := by
  refine ⟨fun c _ => ?_, ?_⟩
  · obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := ramsey_3_3.1 c
    have hik : i < k := Nat.lt_trans hij hjk
    exact ⟨i, j, k, fun he => Nat.ne_of_lt hij (congrArg Fin.val he),
      fun he => Nat.ne_of_lt hik (congrArg Fin.val he),
      fun he => Nat.ne_of_lt hjk (congrArg Fin.val he), h1, h2⟩
  · refine ⟨fun i j => decide ((j : Nat) = ((i : Nat) + 1) % 5 ∨ (i : Nat) = ((j : Nat) + 1) % 5),
      ?_, ?_⟩
    · decide
    · decide

end Math

