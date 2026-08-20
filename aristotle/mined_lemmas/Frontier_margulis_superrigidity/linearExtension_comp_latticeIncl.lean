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

lemma linearExtension_comp_latticeIncl (π : (Fin n → ℤ) →+ E) (v : Fin n → ℤ) :
    linearExtension π (latticeIncl n v) = π v := by
  have hv : latticeIncl n v
      = ∑ i : Fin n, (v i : ℝ) • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext j
    simp [Pi.single_apply]
  have hv' : v = ∑ i : Fin n, (v i) • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    funext j
    simp [Pi.single_apply]
  have h1 : linearExtension π (latticeIncl n v)
      = ∑ i : Fin n, (v i) • π (Pi.single i (1 : ℤ)) := by
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, linearExtension_basis, Int.cast_smul_eq_zsmul]
  have h2 : π v = ∑ i : Fin n, (v i) • π (Pi.single i (1 : ℤ)) := by
    conv_lhs => rw [hv']
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul π _ _
  rw [h1, h2]

/-- Uniqueness: a continuous homomorphism `ℝ ^ n → E` is determined by its values on the
lattice `ℤ ^ n`. -/
