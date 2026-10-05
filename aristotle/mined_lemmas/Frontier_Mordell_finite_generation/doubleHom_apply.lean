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

lemma doubleHom_apply {A : Type*} [AddCommGroup A] (a : A) :
    doubleHom A a = (2 : ℕ) • a := rfl

/-- The axioms satisfied by a (naive or canonical) Weil height `h` on an abelian group `A`:

* `translate`: for every `Q`, the height of `P + Q` is at most `2 * h P` up to a constant
  depending only on `Q`;
* `double`: the height of `2 • P` is at least `4 * h P` up to a constant;
* `finite_le`: only finitely many points have bounded height.

These are exactly the properties of the naive height on the rational points of an elliptic
curve over `ℚ` that are used in the descent step of the Mordell–Weil theorem. -/
structure IsWeilHeight (A : Type*) [AddCommGroup A] (h : A → ℝ) : Prop where
  translate : ∀ Q : A, ∃ C : ℝ, ∀ P : A, h (P + Q) ≤ 2 * h P + C
  double : ∃ C : ℝ, ∀ P : A, 4 * h P ≤ h ((2 : ℕ) • P) + C
  finite_le : ∀ C : ℝ, {P : A | h P ≤ C}.Finite

variable {A : Type*} [AddCommGroup A]

/-- **Descent theorem.** An abelian group carrying a Weil height and having finite quotient
`A / 2A` is finitely generated. This is the group-theoretic heart of the Mordell–Weil
theorem: it turns the *weak* Mordell–Weil theorem (finiteness of `A / 2A`) into full finite
generation. -/
