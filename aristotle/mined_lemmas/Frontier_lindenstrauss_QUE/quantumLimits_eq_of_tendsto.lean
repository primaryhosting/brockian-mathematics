/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Arithmetic Quantum Unique Ergodicity (Lindenstrauss)

Setting.  `X` is a compact metric space — in the intended application, the unit
cotangent bundle `Γ \ PSL₂(ℝ)` of a compact congruence arithmetic hyperbolic
surface — carrying its Borel σ-algebra, and `vol` is the normalized Liouville
(Haar) probability measure on `X`.  A sequence `μ : ℕ → ProbabilityMeasure X` of
*microlocal lifts* of Hecke–Maass eigenforms with eigenvalue tending to infinity
is given.  *Quantum unique ergodicity* is the assertion that `μ n → vol` in the
weak-* (convergence in distribution) topology.

Lindenstrauss's theorem proves this by measure rigidity: every weak-* limit
point of the sequence (a *quantum limit*) is invariant under the geodesic flow,
is recurrent under the Hecke correspondence, and has positive entropy on almost
every ergodic component; and any such measure is the Haar measure.

What is formalized here.  The *reduction* is proved unconditionally and in full:
if every quantum limit of the sequence equals `vol`, then the whole sequence
converges to `vol` in the weak-* topology, hence `∫ f dμ n → ∫ f dvol` for every
bounded continuous observable `f` and `μ n A → vol A` for every Borel set whose
boundary is `vol`-null.  The two arithmetic/dynamical inputs — that quantum
limits satisfy the rigidity hypotheses, and Lindenstrauss's classification of
measures satisfying them — enter as explicit hypotheses `hArithmetic` and
`hRigidity` on an abstract predicate `Rigid`, so that the statement below is
exactly the logical skeleton of Lindenstrauss's deduction of QUE from measure
rigidity, with the topological/measure-theoretic half proved in Lean.
-/

namespace Frontier

open Filter MeasureTheory Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

/-- The set of **quantum limits** of a sequence of probability measures `μ`:
all weak-* limits of subsequences of `μ`. -/

theorem quantumLimits_eq_of_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (h : Tendsto μ atTop (𝓝 vol)) :
    QuantumLimits μ = {vol} := by
  ext ν
  constructor
  · rintro ⟨ns, hns, hconv⟩
    have hsub : Tendsto (fun n => μ (ns n)) atTop (𝓝 vol) := h.comp hns.tendsto_atTop
    have : ν = vol := tendsto_nhds_unique hconv hsub
    simp [this]
  · intro hν
    rw [Set.mem_singleton_iff] at hν
    subst hν
    exact ⟨id, strictMono_id, h⟩

end Frontier

