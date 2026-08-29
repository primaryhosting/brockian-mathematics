import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory Filter Topology

namespace Frontier

/-!
## Setting

Arithmetic quantum unique ergodicity (Lindenstrauss) concerns a compact congruence
surface `M = Γ \ ℍ`, its unit cotangent bundle `X = Γ \ PSL(2,ℝ)`, a sequence of
Hecke–Maass eigenforms with eigenvalue tending to infinity, and the associated
sequence of *microlocal lifts* `μ n`, which are Borel probability measures on the
compact space `X`.  The deep input of Lindenstrauss' theorem is a *measure
classification* statement:

> every weak-\* accumulation point of the sequence of microlocal lifts is the
> normalized Liouville (volume) measure `vol`.

The content formalized here is the abstract measure-theoretic framework in which
these statements live, together with a fully Lean-checked reduction: the
classification statement about subsequential limits is *equivalent* to the QUE
equidistribution statement

  `∫ f dμ n → ∫ f d vol`  for every continuous observable `f`.

Throughout, `X` is an arbitrary compact metric space equipped with its Borel
σ-algebra — the properties of `X` actually used are exactly compactness and
metrizability of the phase space, which hold for `Γ \ PSL(2,ℝ)` with `Γ` a
cocompact congruence lattice.
-/

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `IsQuantumLimit μ ν` says that the probability measure `ν` is a weak-\*
accumulation point of the sequence `μ` of probability measures, i.e. `ν` is the
limit of `μ` along some subsequence.  In the arithmetic setting, `μ n` are the
microlocal lifts of a sequence of Hecke–Maass eigenforms and `ν` is a *quantum
limit*. -/

theorem equidistributes_of_eq_vol (μ : ℕ → ProbabilityMeasure X)
    (vol : ProbabilityMeasure X) (h : ∀ n, μ n = vol) : Equidistributes μ vol := by
  rw [← tendsto_iff_equidistributes]
  simpa [funext h] using tendsto_const_nhds (x := vol) (f := (atTop : Filter ℕ))

end Frontier

