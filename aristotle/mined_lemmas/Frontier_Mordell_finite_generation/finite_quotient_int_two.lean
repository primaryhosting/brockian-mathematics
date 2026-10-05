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

lemma finite_quotient_int_two : Finite (ℤ ⧸ multiples ℤ 2) := by
  have hsurj : Function.Surjective
      (fun i : Fin 2 => (QuotientAddGroup.mk' (multiples ℤ 2)) (i : ℤ)) := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | _ n =>
      rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · refine ⟨0, ?_⟩
        simp only [QuotientAddGroup.mk'_apply]
        rw [QuotientAddGroup.eq_iff_sub_mem]
        exact ⟨-k, by simp [nsmulHom]; omega⟩
      · refine ⟨1, ?_⟩
        simp only [QuotientAddGroup.mk'_apply]
        rw [QuotientAddGroup.eq_iff_sub_mem]
        exact ⟨-k, by simp [nsmulHom]; omega⟩
  exact Finite.of_surjective _ hsurj

