import Mathlib
/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE FILE HEADER.  Lean 4 requires `import` to be the very first command of a
module, so the requested `/-! ... -/` module docstring is placed immediately after the
single `import Mathlib` line rather than before it; its text is otherwise verbatim.
-/

open scoped BigOperators

namespace Frontier

/-! ## The superrigidity extension property

Margulis superrigidity says, for `G` a semisimple Lie group of real rank `≥ 2`, `Γ ≤ G` an
irreducible lattice and `π : Γ → H` a homomorphism into a simple algebraic group with
unbounded Zariski-dense image, that `π` is the restriction of a *continuous* homomorphism
`G → H`.  The predicate below isolates the conclusion of that theorem: a homomorphism
defined on the lattice extends to a continuous homomorphism of the ambient group.
-/

/-- The conclusion of a superrigidity statement, in additive notation: a homomorphism `π`
defined on a lattice `L` (mapped into the ambient group `G` by the inclusion `ι`) is the
restriction along `ι` of a continuous homomorphism `G → H`. -/

lemma column_isUnit_of_dvd {m : ℕ} (hm : m < n) (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) (d : ℤ)
    (hd : ∀ i : Fin n, m ≤ (i : ℕ) → d ∣ (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩) :
    IsUnit d := by
  set c : Fin n := ⟨m, hm⟩ with hc
  have hexp : ∑ i : Fin n, Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℤ) c i
      * (A : Matrix (Fin n) (Fin n) ℤ) i c = 1 := by
    have h := congrFun (congrFun (Matrix.adjugate_mul (A : Matrix (Fin n) (Fin n) ℤ)) c) c
    simpa [Matrix.mul_apply, A.2, Matrix.one_apply] using h
  refine isUnit_of_dvd_one ?_
  rw [← hexp]
  refine Finset.dvd_sum fun i _ => ?_
  by_cases hi : m ≤ (i : ℕ)
  · exact Dvd.dvd.mul_left (hd i hi) _
  · push_neg at hi
    have h0 : (A : Matrix (Fin n) (Fin n) ℤ) i c = 0 := by
      rw [hA i c (Or.inl hi)]
      have : i ≠ c := fun h => by rw [h] at hi; simp [hc] at hi
      simp [this]
    simp [h0]

/-- A matrix agreeing with the identity on all rows and columns is the identity. -/
