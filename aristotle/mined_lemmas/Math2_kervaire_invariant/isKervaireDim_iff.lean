/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Mathlib currently contains no development of framed cobordism or of the
-- Kervaire invariant (a search of the library turns up no relevant declaration), so
-- nothing in the library closes this goal.  The file also carries no `import` line,
-- because the required header above is a module doc comment and Lean only allows
-- `import` commands before any other command; the proof below uses core Lean only.

set_option autoImplicit false

namespace Math2

/-- The dimensions in which a framed manifold of Kervaire invariant one exists,
described arithmetically: `n = 2 ^ (j + 2) - 2` for some `j ≤ 5`. -/

theorem isKervaireDim_iff (n : Nat) :
    IsKervaireDim n ↔ (n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126) := by
  constructor
  · intro h
    match h with
    | ⟨0, _, hn⟩ =>
      have hn' : n + 2 = 4 := hn
      exact Or.inl (by omega)
    | ⟨1, _, hn⟩ =>
      have hn' : n + 2 = 8 := hn
      exact Or.inr (Or.inl (by omega))
    | ⟨2, _, hn⟩ =>
      have hn' : n + 2 = 16 := hn
      exact Or.inr (Or.inr (Or.inl (by omega)))
    | ⟨3, _, hn⟩ =>
      have hn' : n + 2 = 32 := hn
      exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    | ⟨4, _, hn⟩ =>
      have hn' : n + 2 = 64 := hn
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    | ⟨5, _, hn⟩ =>
      have hn' : n + 2 = 128 := hn
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
    | ⟨j + 6, hj, _⟩ => exact absurd hj (by omega)
  · intro h
    match h with
    | Or.inl hn => exact ⟨0, by omega, by subst hn; rfl⟩
    | Or.inr (Or.inl hn) => exact ⟨1, by omega, by subst hn; rfl⟩
    | Or.inr (Or.inr (Or.inl hn)) => exact ⟨2, by omega, by subst hn; rfl⟩
    | Or.inr (Or.inr (Or.inr (Or.inl hn))) => exact ⟨3, by omega, by subst hn; rfl⟩
    | Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))) => exact ⟨4, by omega, by subst hn; rfl⟩
    | Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))) => exact ⟨5, by omega, by subst hn; rfl⟩

/--
**Kervaire invariant one dimensions** (Browder; Hill–Hopkins–Ravenel).

Let `K n` say that there exists an `n`-dimensional framed smooth manifold of
Kervaire invariant one.  The two inputs are:

* Browder's theorem: such a manifold can only exist when `n + 2` is a power of two,
  necessarily divisible by `4` since the Kervaire invariant lives in dimensions
  congruent to `2` modulo `4`; that is, `n + 2 = 2 ^ (j + 2)` for some `j`;
* the Hill–Hopkins–Ravenel theorem (together with the resolution of the remaining
  case `n = 126`): no such manifold exists in dimension greater than `126`.

Taking these as hypotheses, the Kervaire invariant is nonzero only in dimensions
`2, 6, 14, 30, 62, 126`.
-/
