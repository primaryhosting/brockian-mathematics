import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter MeasureTheory Topology

namespace Frontier

/-!
## Setting

Arithmetic quantum unique ergodicity (Lindenstrauss) concerns a compact congruence
surface `M = Γ \ ℍ` and the sequence of probability measures
`μₙ = |ψₙ|² dvol` (or their microlocal lifts to the unit cotangent bundle
`X = Γ \ PSL₂(ℝ)`) attached to an orthonormal sequence of Hecke–Maass eigenforms
`ψₙ` with Laplace eigenvalue tending to infinity.  The theorem asserts that
`μₙ` converges weak-* to the normalized Haar (Liouville) measure `ν`.

Here `X` is modelled as an arbitrary compact metrizable Borel space (the unit
cotangent bundle of a compact congruence surface is such a space), `mu` is the
sequence of quantum limits candidates, and `nu` is the reference (Haar/Liouville)
probability measure.

The analytic heart of Lindenstrauss's theorem is the *measure classification*
step: every weak-* limit point of the sequence `mu` is `nu`.  The statement
proved below is the (Lean-checked) reduction of quantum unique ergodicity to
that classification step: once all weak-* limit points are known to equal `nu`,
the full sequence equidistributes, and consequently the quantum expectation
values `∫ f dμₙ` of every continuous observable `f` converge to `∫ f dν`.

The topological inputs are `MeasureTheory.instCompactSpaceProbabilityMeasure`
(compactness of the space of probability measures on a compact space, from
Mathlib's `Mathlib/MeasureTheory/Measure/Prokhorov.lean`),
`MeasureTheory.instMetrizableSpaceProbabilityMeasure`, together with
`TopologicalSpace.FirstCountableTopology.tendsto_subseq` and
`tendsto_nhds_of_unique_mapClusterPt`.  The translation between weak-* convergence and
convergence of expectation values uses
`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.
-/

section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Quantum unique ergodicity for a sequence of probability measures `mu` with respect to
a reference probability measure `nu`: the expectation value of every continuous observable
converges to its `nu`-average. -/

def QUE (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure X) : Prop :=
  ∀ f : X → ℝ, Continuous f →
    Tendsto (fun n ↦ ∫ x, f x ∂(mu n : Measure X)) atTop (𝓝 (∫ x, f x ∂(nu : Measure X)))

/-- The measure-classification hypothesis: every weak-* limit point of the sequence `mu`
(that is, every limit of a convergent subsequence) is the reference measure `nu`. -/
