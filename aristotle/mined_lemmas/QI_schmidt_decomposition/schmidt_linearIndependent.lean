/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem schmidt_linearIndependent {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) (t : ℝ) :
    LinearIndependent ℂ (fun k : {k : Fin r // s k = t} => u k.val) := by
  have hu : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := h.2.1
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have hg' : ∀ i, ∑ k : {k : Fin r // s k = t}, g k * u k.val i = 0 := by
    intro i
    have := congrFun hg i
    simpa using this
  have key : ∑ k : {k : Fin r // s k = t}, g k * (if (l : Fin r) = (k : Fin r) then (1 : ℂ) else 0)
      = 0 := by
    have e1 : ∀ i : A, conj (u l.val i) * (∑ k : {k : Fin r // s k = t}, g k * u k.val i)
        = ∑ k : {k : Fin r // s k = t}, g k * (conj (u l.val i) * u k.val i) := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ k : {k : Fin r // s k = t}, g k * (if (l : Fin r) = (k : Fin r) then (1 : ℂ) else 0)
        = ∑ k : {k : Fin r // s k = t}, g k * ∑ i, conj (u l.val i) * u k.val i := by
          exact Finset.sum_congr rfl fun k _ => by rw [hu l.val k.val]
      _ = ∑ i, conj (u l.val i) * (∑ k : {k : Fin r // s k = t}, g k * u k.val i) := by
          simp only [e1]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ = 0 := by simp [hg']
  simpa [← Subtype.ext_iff, Finset.sum_ite_eq] using key

omit [DecidableEq B] in
