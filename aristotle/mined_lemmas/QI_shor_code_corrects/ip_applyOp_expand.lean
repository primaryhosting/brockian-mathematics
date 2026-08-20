/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma ip_applyOp_expand (k l : Idx) (M N : Bool → Bool → ℂ) (φ χ : Bits → ℂ) :
    ip (applyOp k M φ) (applyOp l N χ)
      = ∑ p : Bool × Bool, ∑ q : Bool × Bool,
          (starRingEnd ℂ) (coefM M p) * coefM N q
            * ip (pauli (sel p.1 k) (sel p.2 k) φ) (pauli (sel q.1 l) (sel q.2 l) χ) := by
  have hφ : applyOp k M φ = fun v => ∑ p : Bool × Bool, coefM M p * pauli (sel p.1 k) (sel p.2 k) φ v :=
    funext (applyOp_eq k M φ)
  have hχ : applyOp l N χ = fun v => ∑ q : Bool × Bool, coefM N q * pauli (sel q.1 l) (sel q.2 l) χ v :=
    funext (applyOp_eq l N χ)
  rw [hφ, hχ, ip_sum_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  exact ip_smul_smul _ _ _ _

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

The two logical states `psi false`, `psi true` are orthonormal, and the Knill–Laflamme
error-correction conditions hold for the set of all errors acting on a single (arbitrary,
unknown) qubit: for any two qubits `k`, `l` and any two single-qubit operators `M`, `N`
there is a constant `w` with `⟨ ψ_a | M_k^† N_l | ψ_b ⟩ = w δ_{ab}`.  Since the Knill–Laflamme
conditions are necessary and sufficient for the existence of a recovery operation, this says
exactly that the code corrects an arbitrary error on one qubit. -/
