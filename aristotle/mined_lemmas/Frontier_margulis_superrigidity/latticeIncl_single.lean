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

lemma latticeIncl_single {n : ℕ} (i : Fin n) :
    latticeIncl n (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i <;> simp [h, Pi.single_apply]

section

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The candidate extension of a homomorphism `π : ℤ ^ n → E`: the unique real-linear map
sending the `i`-th standard basis vector to `π (δ i)`. -/
