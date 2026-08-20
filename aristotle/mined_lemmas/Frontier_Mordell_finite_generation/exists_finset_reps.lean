/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-! ## The multiplication-by-`m` subgroup and its quotient -/

/-- Multiplication by `m` as an endomorphism of an additive commutative group. -/

lemma exists_finset_reps {A : Type*} [AddCommGroup A] (H : AddSubgroup A)
    [Finite (A ⧸ H)] : ∃ S : Finset A, ∀ P : A, ∃ Q ∈ S, P - Q ∈ H := by
  classical
  have : Fintype (A ⧸ H) := Fintype.ofFinite _
  refine ⟨Finset.image (fun q : A ⧸ H => Quotient.out q) Finset.univ, fun P => ?_⟩
  refine ⟨Quotient.out (QuotientAddGroup.mk' H P), Finset.mem_image_of_mem _ (Finset.mem_univ _),
    ?_⟩
  have h1 : (QuotientAddGroup.mk' H) (Quotient.out (QuotientAddGroup.mk' H P))
      = (QuotientAddGroup.mk' H) P := by
    simp
  have h2 := (QuotientAddGroup.eq (s := H)).mp h1
  simpa [sub_eq_add_neg, add_comm] using h2

/-! ## The abstract descent theorem

This is the group-theoretic engine behind the Mordell–Weil theorem
(the "descent theorem", Silverman, *The Arithmetic of Elliptic Curves*, VIII.3.1):
an abelian group carrying a height function with the standard properties and with
`A/mA` finite is finitely generated. -/

/-- **Descent theorem.** Let `A` be an abelian group, `m ≥ 2`, and `h : A → ℝ` a function
("height") such that

* `H1`: for every `Q` there is a constant `C` with `h (P + Q) ≤ 2 * h P + C` for all `P`;
* `H2`: there is a constant `C` with `m ^ 2 * h P ≤ h (m • P) + C` for all `P`;
* `H3`: for every `C` the set `{P | h P ≤ C}` is finite;

and such that `A / mA` is finite.  Then `A` is finitely generated. -/
