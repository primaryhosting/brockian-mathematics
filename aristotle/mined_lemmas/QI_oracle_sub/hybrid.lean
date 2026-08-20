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

namespace QI

variable {N M : ℕ}

/-- The state space of a quantum query algorithm searching a database of size `N`:
an index register `Fin N` together with an arbitrary finite workspace `Fin M`. -/
abbrev State (N M : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin M)

/-- The standard phase oracle marking the index `i`: it flips the sign of every
amplitude whose index register holds `i`, and does nothing otherwise. -/

lemma hybrid (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M) (i : Fin N)
    (T : ℕ) :
    ‖run U psi0 (oracle i) T - run U psi0 id T‖
      ≤ ∑ t ∈ Finset.range T, ‖oracle i (run U psi0 id t) - run U psi0 id t‖ := by
  induction T with
  | zero => simp
  | succ T ih =>
    set a := run U psi0 (oracle i) T with ha
    set b := run U psi0 id T with hb
    have hstep : run U psi0 (oracle i) (T + 1) - run U psi0 id (T + 1)
        = U T (oracle i a - b) := by
      simp [← ha, ← hb, map_sub]
    rw [hstep, LinearIsometryEquiv.norm_map, Finset.sum_range_succ]
    calc ‖oracle i a - b‖
        ≤ ‖oracle i a - oracle i b‖ + ‖oracle i b - b‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (oracle i a) (oracle i b) b
      _ = ‖a - b‖ + ‖oracle i b - b‖ := by rw [oracle_dist]
      _ ≤ (∑ t ∈ Finset.range T, ‖oracle i (run U psi0 id t) - run U psi0 id t‖)
            + ‖oracle i b - b‖ := by gcongr

/-- **Optimality of Grover search (BBBV lower bound).**

`U` is an arbitrary quantum query algorithm on an index register `Fin N` and a workspace
`Fin M`: it starts in the unit vector `psi0` and alternates a query to the oracle with an
arbitrary unitary, `T` times in total. `oracle i` is the phase oracle for the marked item
`i`, and `run U psi0 id T` is the final state of the same algorithm run with no marked
item at all.

If the algorithm can tell *every* marked item `i` apart from the unmarked database — i.e.
the two final states are at distance at least `c` for every `i`, which is what a bounded
error probability of success forces, with `c` a positive constant — then

  `T ≥ (c/2) * √N`,

so `Ω(√N)` queries are necessary and Grover's algorithm is optimal up to a constant. -/
