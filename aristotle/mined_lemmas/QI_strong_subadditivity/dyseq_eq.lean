import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


lemma dyseq_eq (m : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    dyseq m a b = a ^ (1 - (2 : ℝ)⁻¹ ^ m) * b ^ ((2 : ℝ)⁻¹ ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [dyseq_succ, ih]
      set t : ℝ := (2:ℝ)⁻¹ ^ m with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have h1 : a * (a ^ (1 - t) * b ^ t) = a ^ (2 - t) * b ^ t := by
        rw [show (2:ℝ) - t = 1 + (1 - t) by ring, Real.rpow_add ha, Real.rpow_one]
        ring
      have h2 : (2:ℝ)⁻¹ ^ (m+1) = t * (1/2) := by rw [ht, pow_succ]; ring
      rw [h1, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le, h2]
      congr 1
      congr 1
      ring

/-- `gpow` of diagonal matrices is diagonal, given by the scalar recursion. -/
