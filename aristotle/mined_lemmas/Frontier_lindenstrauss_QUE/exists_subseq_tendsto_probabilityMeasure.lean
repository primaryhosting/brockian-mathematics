/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology

namespace Frontier

section QUE

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Sequential compactness of the space of probability measures.**

On a compact metric space `X`, the space of Borel probability measures with the topology of
weak-* convergence is compact and metrizable, hence sequentially compact: every sequence of
probability measures has a weak-* convergent subsequence.

This is the compactness half of the standard quantum-unique-ergodicity argument: the microlocal
lifts of a sequence of eigenfunctions always have weak-* limit points ("quantum limits"). -/

theorem exists_subseq_tendsto_probabilityMeasure (mu : ℕ → ProbabilityMeasure X) :
    ∃ (nu : ProbabilityMeasure X) (ms : ℕ → ℕ), StrictMono ms ∧
      Tendsto (fun n => mu (ms n)) atTop (𝓝 nu) := by
  obtain ⟨nu, -, ms, hms, h⟩ :=
    (isCompact_univ (X := ProbabilityMeasure X)).tendsto_subseq (x := mu)
      (fun n => Set.mem_univ _)
  exact ⟨nu, ms, hms, h⟩

/-- **Arithmetic quantum unique ergodicity: the classification-to-equidistribution reduction.**

Setting: `X` is a compact metric space carrying its Borel σ-algebra — in the arithmetic QUE
situation this is the unit cotangent bundle `Γ \ PSL₂(ℝ)` of a compact congruence surface — and
`vol` is the normalized Liouville (Haar) probability measure on it. The sequence
`mu : ℕ → ProbabilityMeasure X` is the sequence of microlocal lifts of an orthonormal sequence
of Hecke–Maass eigenforms with eigenvalue tending to infinity.

Hypothesis (Lindenstrauss' measure classification input): *every* weak-* limit of a subsequence
of the microlocal lifts is the normalized volume measure — i.e. the only possible quantum limit
is Liouville measure.

Conclusion (quantum unique ergodicity): the whole sequence of microlocal lifts converges weak-*
to the volume measure; equivalently, for every continuous observable `f` on `X`,
`∫ f dmu n → ∫ f dvol`.

The proof is the compactness argument that turns Lindenstrauss' classification of quantum limits
into equidistribution of the full sequence: the space of probability measures on a compact metric
space is compact and metrizable, so a sequence with a unique subsequential limit converges. -/
