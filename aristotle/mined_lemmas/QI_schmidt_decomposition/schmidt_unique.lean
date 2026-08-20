/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem schmidt_unique {r r' : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} {s' : Fin r' → ℝ} {u' : Fin r' → A → ℂ} {v' : Fin r' → B → ℂ}
    (h : IsSchmidtDecomposition psi s u v) (h' : IsSchmidtDecomposition psi s' u' v') :
    Multiset.map s Finset.univ.val = Multiset.map s' Finset.univ.val := by
  refine Multiset.ext.mpr fun a => ?_
  rw [Multiset.count_map, Multiset.count_map]
  rcases lt_or_ge 0 a with ha | ha
  · have e : ∀ {n : ℕ} (f : Fin n → ℝ),
        (Multiset.filter (fun k => a = f k) (Finset.univ : Finset (Fin n)).val).card
          = Fintype.card {k : Fin n // f k = a} := by
      intro n f
      have hfil : Multiset.filter (fun k : Fin n => a = f k) (Finset.univ : Finset (Fin n)).val
          = Multiset.filter (fun k : Fin n => f k = a) (Finset.univ : Finset (Fin n)).val :=
        Multiset.filter_congr fun k _ => eq_comm
      rw [hfil, ← Finset.filter_val, Fintype.card_subtype]
      rfl
    rw [e s, e s', card_schmidt_eq_finrank h ha, card_schmidt_eq_finrank h' ha]
  · have e : ∀ {n : ℕ} (f : Fin n → ℝ), (∀ k, 0 < f k) →
        (Multiset.filter (fun k => a = f k) (Finset.univ : Finset (Fin n)).val).card = 0 := by
      intro n f hf
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro k _ hk
      exact absurd (hk ▸ hf k) (by simpa using ha)
    rw [e s h.1, e s' h'.1]

omit [DecidableEq B] in
/-- The sum of the squares of the Schmidt coefficients is the squared norm of the state;
in particular, for a normalised state the squared Schmidt coefficients sum to `1`. -/
