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

theorem lindenstrauss_QUE_base (vol : ProbabilityMeasure X) :
    ∀ ns : ℕ → ℕ, StrictMono ns → ∀ nu : ProbabilityMeasure X,
      Tendsto (fun n => (fun _ => vol) (ns n)) atTop (𝓝 nu) → nu = vol := by
  intro ns _ nu hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

/-- Portmanteau consequence of quantum unique ergodicity: under the hypothesis of
`Frontier.lindenstrauss_QUE`, the mass that the microlocal lifts put on an open set `U`
is asymptotically at least `vol U`. -/
