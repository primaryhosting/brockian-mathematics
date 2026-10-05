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

lemma hybrid (U : ℕ → (St ι ≃ₗᵢ[ℂ] St ι)) (S : Finset ι) (psi0 : St ι) (T : ℕ) :
    ‖run U S psi0 T - run U ∅ psi0 T‖
      ≤ 2 * ∑ t ∈ Finset.range T, ‖restrict S (run U ∅ psi0 t)‖ := by
  induction T with
  | zero => simp [run]
  | succ T ih =>
      have key : run U S psi0 (T + 1) - run U ∅ psi0 (T + 1)
          = U T (oracle S (run U S psi0 T)) - U T (oracle ∅ (run U ∅ psi0 T)) := rfl
      rw [key, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, oracle_empty]
      have h1 : ‖oracle S (run U S psi0 T) - run U ∅ psi0 T‖
          ≤ ‖oracle S (run U S psi0 T) - oracle S (run U ∅ psi0 T)‖
            + ‖oracle S (run U ∅ psi0 T) - run U ∅ psi0 T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [oracle_sub, oracle_norm, oracle_sub_self] at h1
      rw [Finset.sum_range_succ]
      linarith

/-- Total weight carried by a pairwise disjoint family of coordinate sets. -/
