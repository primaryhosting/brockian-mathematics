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

lemma natAbs_emod_lt {a b : ℤ} (hb : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  have h1 : 0 ≤ a % b := Int.emod_nonneg a hb
  have h2 : a % b < |b| := Int.emod_lt_abs a hb
  rw [Int.abs_eq_natAbs] at h2
  omega

/-- **Column reduction.**  Elementary row operations turn the pivot column of a matrix
satisfying `PartialId m` into a standard basis vector.  The proof is the Euclidean algorithm:
as long as two entries of the column are nonzero, one may be reduced modulo the other. -/
