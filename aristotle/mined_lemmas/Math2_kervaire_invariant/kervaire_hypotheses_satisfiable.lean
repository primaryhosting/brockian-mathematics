/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-- The dimensions in which the Kervaire invariant is known (or, in the single remaining
edge case, permitted) to be nonzero: `2, 6, 14, 30, 62, 126`. -/

theorem kervaire_hypotheses_satisfiable :
    (∀ n, IsKervaireDimension n → 0 < n ∧ ∃ j : Nat, n + 2 = 2 ^ j) ∧
      (∀ n, IsKervaireDimension n → n ≤ 126) := by
  constructor
  · intro n hn
    unfold IsKervaireDimension at hn
    match hn with
    | Or.inl h => exact ⟨by omega, 2, by omega⟩
    | Or.inr (Or.inl h) => exact ⟨by omega, 3, by omega⟩
    | Or.inr (Or.inr (Or.inl h)) => exact ⟨by omega, 4, by omega⟩
    | Or.inr (Or.inr (Or.inr (Or.inl h))) => exact ⟨by omega, 5, by omega⟩
    | Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))) => exact ⟨by omega, 6, by omega⟩
    | Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))) => exact ⟨by omega, 7, by omega⟩
  · intro n hn
    unfold IsKervaireDimension at hn
    omega

end Math2

#print axioms Math2.kervaire_invariant
#print axioms Math2.kervaire_hypotheses_satisfiable

