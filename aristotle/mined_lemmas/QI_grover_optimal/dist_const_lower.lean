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

lemma dist_const_lower : (0.239 : ℝ) ≤ Real.sqrt (2 / 3) - Real.sqrt (1 / 3) := by
  have h1 : (0.8164 : ℝ) ≤ Real.sqrt (2 / 3) := by
    rw [show (0.8164 : ℝ) = Real.sqrt (0.8164 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : Real.sqrt (1 / 3) ≤ 0.5774 := by
    rw [show (0.5774 : ℝ) = Real.sqrt (0.5774 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **BBBV bound / optimality of Grover's algorithm.**

Let `κ` be a search space of size `N ≥ 2`.  Consider a `T`-query quantum algorithm:
it starts in a unit state `psi0`, alternates arbitrary unitaries `U t` with calls to
the phase oracle for the unknown marked element `x` (which flips the phase of the
basis states in `Q x`, these sets being pairwise disjoint), and finally announces its
answer by a measurement in the computational basis, outputting `x` when the outcome
lies in `Ans x` (again pairwise disjoint sets).  If the algorithm is correct with
probability at least `2/3` for every marked element, then `T ≥ √N / 25`.

Since Grover's algorithm achieves `O(√N)` queries, this shows it is optimal up to a
constant factor. -/
