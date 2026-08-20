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

lemma transvection_commutator_matrix {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hkj : k ≠ j) (a : ℤ) :
    transvection i k a * transvection k j 1 * transvection i k (-a) * transvection k j (-1)
      = transvection i j a := by
  have hneg : ∀ (p q : Fin n) (c : ℤ), single p q (-c) = -single p q c := by
    intro p q c
    have h := Matrix.single_add p q c (-c)
    simp only [add_neg_cancel, Matrix.single_zero] at h
    linear_combination (norm := abel) -h
  simp only [transvection]
  noncomm_ring
  simp [single_mul_single_same, single_mul_single_of_ne, hij.symm, hik.symm, hkj.symm]
  rw [hneg, hneg, hneg]
  abel

/-- The inverse of an elementary matrix is elementary. -/
