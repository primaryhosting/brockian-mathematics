import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- Multiplication by `m : ℕ` on an additive commutative group, as a group homomorphism. -/

lemma exists_finite_representatives {A : Type*} [AddCommGroup A] (m : ℕ)
    (hquot : Finite (A ⧸ multiples A m)) :
    ∃ R : Set A, R.Finite ∧ ∀ P : A, ∃ Q ∈ R, ∃ P' : A, P = m • P' + Q := by
  classical
  refine ⟨Set.range (fun q : A ⧸ multiples A m => Quotient.out q), Set.finite_range _, ?_⟩
  intro P
  refine ⟨Quotient.out (QuotientAddGroup.mk' (multiples A m) P), ⟨_, rfl⟩, ?_⟩
  set Q : A := Quotient.out (QuotientAddGroup.mk' (multiples A m) P) with hQ
  have hmk : (QuotientAddGroup.mk' (multiples A m)) Q
      = (QuotientAddGroup.mk' (multiples A m)) P := by
    rw [hQ]
    exact Quotient.out_eq _
  have : P - Q ∈ multiples A m := by
    have : (QuotientAddGroup.mk' (multiples A m)) (P - Q) = 0 := by
      rw [map_sub, hmk, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp this
  obtain ⟨P', hP'⟩ := this
  exact ⟨P', by rw [show m • P' = P - Q from hP']; abel⟩

/-! ## The descent theorem -/

/-- **Descent theorem** (Silverman, *The Arithmetic of Elliptic Curves*, VIII.3.1).
Let `A` be an abelian group equipped with a "height" function `h : A → ℝ` such that

* for every `Q : A` there is a constant `C` with `h (P + Q) ≤ 2 * h P + C` for all `P`;
* there is `m ≥ 2` and a constant `C` with `m ^ 2 * h P - C ≤ h (m • P)` for all `P`;
* for every bound `C` the set `{P | h P ≤ C}` is finite;

and such that the quotient `A / mA` is finite. Then `A` is a finitely generated group. -/
