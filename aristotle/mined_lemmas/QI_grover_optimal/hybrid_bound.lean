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

namespace QI

/-- The Hilbert space of a quantum query algorithm searching a database of `N` items:
the index register `Fin N` together with an arbitrary workspace register `K`. -/
abbrev HSpace (N : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

variable {N : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The (phase) query operator for the database whose unique marked item is `x`:
it flips the sign of the component of the index register at `x`. -/

lemma hybrid_bound (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K) (x : Fin N)
    (t : ℕ) :
    ‖run U (phaseOracle x) psi0 t - run U id psi0 t‖ ≤
      2 * ∑ s ∈ Finset.range t, ‖(run U id psi0 s) x‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      set f := run U (phaseOracle x) psi0 t with hf
      set g := run U id psi0 t with hg
      have hstep : ‖run U (phaseOracle x) psi0 (t + 1) - run U id psi0 (t + 1)‖
          = ‖phaseOracle x f - g‖ := by
        rw [run_succ, run_succ]
        show ‖U t (phaseOracle x f) - U t (id g)‖ = _
        simp only [id_eq, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      have htri : ‖phaseOracle x f - g‖
          ≤ ‖phaseOracle x f - phaseOracle x g‖ + ‖phaseOracle x g - g‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h1 : ‖phaseOracle x f - phaseOracle x g‖ = ‖f - g‖ := by
        rw [phaseOracle_sub, phaseOracle_norm]
      have h2 : ‖phaseOracle x g - g‖ = 2 * ‖g x‖ := norm_phaseOracle_sub_self x g
      rw [Finset.sum_range_succ]
      rw [hstep]
      rw [h1, h2] at htri
      linarith [htri, ih]

/-- **Optimality of Grover search (BBBV lower bound).**

Any quantum query algorithm which, for every marked item `x` of a database of size `N`,
finds `x` with probability at least `2/3` (i.e. the index register of its final state has
squared amplitude at least `2/3` on `x`) must use at least `(√(2N/3) - 1)/2` queries.
In particular the number of queries is `Ω(√N)`, so Grover's `O(√N)` algorithm is optimal. -/
