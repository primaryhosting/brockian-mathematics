import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma one_sub_cos_le (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := t)
  linarith

end

end Phys

import RequestProject.Spin

/-!
# Gibbs measures on a finite product of circles, and the spin-wave estimate

For a finite index set `ι` we consider the configuration space `ι → Spin` of a classical
spin system, equipped with the (translation invariant) Haar measure, and the Gibbs
expectation associated with a continuous Hamiltonian `H` at inverse temperature `β`.

The main result `Phys.gibbs_shift_bound` is the quantitative version of the spin-wave
(Bogoliubov / relative entropy) argument: if the *second difference*
`H (θ + g) + H (θ - g) - 2 H θ` of the Hamiltonian along a deformation `g` is bounded
by `K`, then the Gibbs expectation of a bounded observable changes by at most
`‖F‖_∞ √(2βK)` when the configuration is shifted by `g`.
-/

namespace Phys

noncomputable section

open MeasureTheory

variable {ι : Type} [Fintype ι]

/-- The Boltzmann weight `exp (-β H θ)`. -/
