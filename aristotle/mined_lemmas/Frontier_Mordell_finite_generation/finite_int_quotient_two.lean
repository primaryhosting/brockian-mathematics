/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/

lemma finite_int_quotient_two : Finite (ℤ ⧸ (doubleHom ℤ).range) := by
  apply Finite.of_surjective (fun (i : Fin 2) => (QuotientAddGroup.mk (i : ℤ) :
    ℤ ⧸ (doubleHom ℤ).range))
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H n =>
    rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨0, by rw [QuotientAddGroup.eq]; exact ⟨m, by simp [doubleHom]; omega⟩⟩
    · exact ⟨1, by rw [QuotientAddGroup.eq]; exact ⟨m, by simp [doubleHom]; omega⟩⟩

/-- The descent theorem applied to `ℤ`, showing that its hypotheses are satisfiable by an
infinite group. -/
example : AddGroup.FG ℤ :=
  fg_of_isWeilHeight_of_finite_quotient _ isWeilHeight_int_sq finite_int_quotient_two

/-- The group of rational points of an elliptic curve over `ℚ`, in Weierstrass form. -/
abbrev RationalPoints (W : WeierstrassCurve ℚ) : Type := W.toAffine.Point

/-- The Mordell–Weil statement: for every elliptic curve over `ℚ`, the group of its rational
points is finitely generated. -/
