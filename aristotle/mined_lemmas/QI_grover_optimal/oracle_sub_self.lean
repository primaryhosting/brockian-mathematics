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

lemma oracle_sub_self (S : Finset ι) (v : St ι) : ‖oracle S v - v‖ = 2 * ‖restrict S v‖ := by
  have h : oracle S v - v = (-2 : ℂ) • restrict S v := by
    ext i; by_cases hi : i ∈ S <;> simp [oracle, restrict, hi] <;> ring
  rw [h, norm_smul]
  norm_num

