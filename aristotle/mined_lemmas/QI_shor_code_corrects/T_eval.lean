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

lemma T_eval (u : Bits) (a b : Bool) :
    (∑ c : Bits, chi u c * f a c * f b c)
      = ∏ m : Fin 3, (if xor (wpar u m) (xor a b) then (0 : ℤ) else 2) := by
  rw [sum_blocky _ (by intro c hc; simp [f_eq_zero_of_not_blocky _ hc])]
  have step : ∀ t : Fin 3 → Bool,
      chi u (expand t) * f a (expand t) * f b (expand t)
        = ∏ m : Fin 3, (if t m && (xor (wpar u m) (xor a b)) then (-1 : ℤ) else 1) := by
    intro t
    rw [chi_expand, f_expand, f_expand, prod_par, prod_par, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun m _ => sign_merge3 (t m) (wpar u m) a b)
  rw [Finset.sum_congr rfl (fun t _ => step t), sum_sign_prod]

