import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace QI

/-! ## Setup

Nine qubits, indexed by `Idx = Fin 3 × Fin 3`: the first component is the block
(one of the three "outer" repetition-code slots), the second is the position of the
qubit inside its block.  A computational basis state is a bit string `Idx → Bool`,
and the state space is the corresponding `512`-dimensional complex Hilbert space. -/

/-- Index of a qubit: `(block, position within block)`. -/
abbrev Idx := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev BasisIdx := Idx → Bool

/-- The nine-qubit state space. -/
abbrev QState := EuclideanSpace ℂ BasisIdx

/-- The operator acting as the `2 × 2` matrix `M` on qubit `q` and as the identity
on the remaining eight qubits.  Every single-qubit error on qubit `q` is of this form. -/

lemma inner_codeword_errors (q r : Idx) (M N : Bool → Bool → ℂ) (a b : Bool) :
    ⟪qubitOp q M (codeword a), qubitOp r N (codeword b)⟫_ℂ =
      (8 : ℂ)⁻¹ * ∑ s : Bool × Bool × Bool,
        sgn a s * sgn b s * gmat q r M N (blockVal s q.1) (blockVal s r.1) := by
  have h8 : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  have hnorm : conj (((Real.sqrt 8 : ℝ) : ℂ)⁻¹) * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = (8 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.conj_ofReal, Complex.ofReal_inv, ← mul_inv, h8]
  simp only [codeword, map_smul, map_sum, inner_smul_left, inner_smul_right, sum_inner, inner_sum,
    conj_sgn, inner_qubitOp_bvec, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← hnorm]
  show _ = _ * (sgn a s * sgn b s * gmat q r M N (emb s q) (emb s r))
  ring

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

`codeword false` and `codeword true` are the two Shor codewords, and `qubitOp q M` is an
arbitrary operator acting on the single qubit `q` (an arbitrary `2 × 2` matrix `M` there,
the identity elsewhere).  The statement is the Knill–Laflamme error-correction condition
`⟪E ψ_a, F ψ_b⟫ = c_{E,F} δ_{a,b}` for any two such single-qubit errors `E`, `F`, which is
exactly the necessary and sufficient condition for the code to correct the error set of all
single-qubit operators. -/
