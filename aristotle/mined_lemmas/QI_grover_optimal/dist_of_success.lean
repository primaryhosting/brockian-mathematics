import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
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

/-!
## The BBBV lower bound for unstructured quantum search

We formalise the Bennett–Bernstein–Brassard–Vazirani hybrid argument: any quantum
algorithm that makes `T` queries to a phase oracle marking an unknown element `x`
of a search space `κ` of size `N`, and that identifies `x` with probability at
least `2/3`, must satisfy `T ≥ √N / 25`.  In particular `T = Ω(√N)`, so Grover's
algorithm, which uses `O(√N)` queries, is optimal up to a constant factor.

The computational model:

* the algorithm works on a finite dimensional Hilbert space `EuclideanSpace ℂ ι`,
  whose basis vectors are indexed by `ι` (query register together with an arbitrary
  workspace);
* `Q x ⊆ ι` is the set of basis vectors on which the oracle for the marked element
  `x` flips the phase; different marked elements flip disjoint sets of basis states
  (a basis state queries at most one index);
* the algorithm alternates arbitrary unitaries `U 0, U 1, …` with oracle calls,
  starting from an arbitrary unit vector `psi0`;
* the answer is read off by measuring: `Ans x ⊆ ι` is the set of basis states on
  which the algorithm outputs `x`, and these sets are pairwise disjoint.
-/

namespace QI

open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The state space of the algorithm: amplitudes indexed by the basis `ι`. -/
abbrev St (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι

/-- Restriction of a state to the coordinates in `S` (orthogonal projection). -/

lemma dist_of_success (A B : Finset ι) (hAB : Disjoint A B) (f g : St ι)
    (hg : ‖g‖ = 1) (hf : (2 : ℝ) / 3 ≤ ‖restrict A f‖ ^ 2)
    (hgB : (2 : ℝ) / 3 ≤ ‖restrict B g‖ ^ 2) :
    Real.sqrt (2 / 3) - Real.sqrt (1 / 3) ≤ ‖f - g‖ := by
  have hgA : ‖restrict A g‖ ^ 2 ≤ 1 / 3 := by
    have := two_restrict_sq_le A B hAB g
    rw [hg] at this; nlinarith
  have h1 : Real.sqrt (2 / 3) ≤ ‖restrict A f‖ := by
    rw [show ‖restrict A f‖ = Real.sqrt (‖restrict A f‖ ^ 2) by
      rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_le_sqrt hf
  have h2 : ‖restrict A g‖ ≤ Real.sqrt (1 / 3) := by
    rw [show ‖restrict A g‖ = Real.sqrt (‖restrict A g‖ ^ 2) by
      rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_le_sqrt hgA
  have h3 : ‖restrict A f‖ - ‖restrict A g‖ ≤ ‖restrict A f - restrict A g‖ :=
    norm_sub_norm_le _ _
  have h4 : ‖restrict A f - restrict A g‖ ≤ ‖f - g‖ := by
    rw [← restrict_sub]; exact norm_restrict_le _ _
  linarith

/-- Numerical bound on the distinguishability constant. -/
