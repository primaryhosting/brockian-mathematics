/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the spin–statistics connection for a relativistic quantum field in the
Wightman framework, at the level of the two–point function, and proves it from the standard
axiomatic inputs.

## Setup

* `Frontier.Minkowski` is `ℝ^{1,3}` with quadratic form `Frontier.minkowskiSq` of signature
  `(+,-,-,-)`; two events are spacelike separated when the interval between them is negative.
* Test functions are complex valued functions on Minkowski space; two of them are *causally
  disjoint* (`Frontier.SpacelikeSupported`) when every point of the support of the first is
  spacelike separated from every point of the support of the second.
* A `Frontier.WightmanField` packages a Hilbert space with a vacuum vector, smeared field
  operators `op f`, a spin (recorded through `twoSpin`, twice the spin, so that integer spin
  means `twoSpin` even) and a choice of statistics (`fermionic`), together with three of the
  Wightman axioms that are used here:
  - hermiticity of the smeared field,
  - the (graded) local commutation relation at spacelike separation, with the sign dictated by
    the chosen statistics,
  - *weak locality*: at spacelike separation the two point function is symmetric up to the sign
    `(-1)^{2j}` dictated by the spin.  This is the Bargmann–Hall–Wightman consequence of Lorentz
    covariance, the spectral condition and the existence of Jost points.

## Results

* `Frontier.twoPoint_eq_zero_of_wrong_statistics`: if the statistics sign disagrees with the
  spin sign, the two point function vanishes for all causally disjoint test functions.
* `Frontier.op_vac_eq_zero_of_wrong_statistics`: adding the Reeh–Schlieder / edge–of–the–wedge
  input (a two point function vanishing on an open set of spacelike configurations vanishes
  identically) the field annihilates the vacuum, i.e. the theory is trivial.
* `Frontier.spin_statistics`: the spin–statistics connection.  A field that does not annihilate
  the vacuum must have statistics matching its spin: Bose statistics for integer spin, Fermi
  statistics for half–integer spin.
-/

namespace Frontier

open scoped InnerProductSpace

/-! ## Minkowski space and causal disjointness -/

/-- Minkowski spacetime `ℝ^{1,3}`, coordinates indexed by `Fin 4` with `0` the time coordinate. -/
abbrev Minkowski := Fin 4 → ℝ

/-- The Minkowski quadratic form, in signature `(+,-,-,-)`. -/

theorem op_vac_eq_zero_of_wrong_statistics (F : WightmanField H)
    (hRS : (∀ f g : TestFn, SpacelikeSupported f g → F.twoPoint f g = 0) →
      ∀ f g : TestFn, F.twoPoint f g = 0)
    (hmis : statSign F.fermionic ≠ spinSign F.twoSpin) (f : TestFn) :
    F.op f F.vac = 0 := by
  have hall : ∀ f g : TestFn, F.twoPoint f g = 0 := by
    refine hRS ?_
    intro f g h
    exact twoPoint_eq_zero_of_wrong_statistics F hmis h
  have : inner ℂ (F.op f F.vac) (F.op f F.vac) = (0 : ℂ) := by
    rw [F.normSq_op_vac f]; exact hall _ _
  exact inner_self_eq_zero.mp this

/-- **The spin–statistics connection.**

Let `F` be a relativistic quantum field in the Wightman framework: hermitian smeared fields,
graded local commutation relations at spacelike separation with the sign given by its statistics,
and weak locality with the sign `(-1)^{2j}` given by its spin.  Assume the Reeh–Schlieder /
edge-of-the-wedge input `hRS`, and that the field is nontrivial, i.e. it does not annihilate the
vacuum.  Then its statistics are determined by its spin:
`(-1)^{2j} = +1` (integer spin) forces Bose statistics, and `(-1)^{2j} = -1` (half-integer spin)
forces Fermi statistics. -/
