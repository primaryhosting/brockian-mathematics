/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/

private lemma stinespring_of_kraus [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R] (K : R → Matrix B A ℂ)
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hK : ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ s, K s * ρ * (K s)ᴴ)
    (hT : ∑ s, (K s)ᴴ * K s = 1) :
    ∃ (dA dB : ℕ) (e : Fin dA) (U : Matrix (B × Fin dB) (A × Fin dA) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ ρ : Matrix A A ℂ, Φ ρ = ptrace (U * (ρ ⊗ₖ single e e 1) * Uᴴ) := by
  classical
  set a₀ : A := Classical.arbitrary A with ha₀
  set dB := Fintype.card (R × A) with hdB
  set dA := Fintype.card (B × R) with hdA
  set εB : Fin dB ≃ R × A := (Fintype.equivFin (R × A)).symm with hεB
  set εA : Fin dA ≃ B × R := (Fintype.equivFin (B × R)).symm with hεA
  set e : Fin dA := εA.symm (Classical.arbitrary B, Classical.arbitrary R) with he
  set W : Matrix (B × Fin dB) A ℂ :=
    Matrix.of (fun p i => K (εB p.2).1 p.1 i * (if (εB p.2).2 = a₀ then 1 else 0)) with hWdef
  have hW : Wᴴ * W = 1 := by
    ext i j
    have h := congrFun (congrFun hT i) j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    rw [Matrix.mul_apply, Fintype.sum_prod_type, ← h]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hfg : ∀ t : Fin dB, Wᴴ i (b, t) * W (b, t) j =
        star (K (εB t).1 b i) * K (εB t).1 b j * (if (εB t).2 = a₀ then (1 : ℂ) else 0) := by
      intro t
      simp only [hWdef, Matrix.conjTranspose_apply, Matrix.of_apply]
      split_ifs <;> simp
    refine (Fintype.sum_equiv εB (fun t : Fin dB => Wᴴ i (b, t) * W (b, t) j)
      (fun r : R × A => star (K r.1 b i) * K r.1 b j * (if r.2 = a₀ then (1 : ℂ) else 0))
      hfg).trans ?_
    rw [Fintype.sum_prod_type]
    simp
  have hf : Function.Injective (fun i : A => (i, e)) := by
    intro x y h; simpa using h
  have hcard : Fintype.card (A × Fin dA) = Fintype.card (B × Fin dB) := by
    simp only [Fintype.card_prod, Fintype.card_fin, hdA, hdB]
    ring
  obtain ⟨U, hU1, hU2, hUW⟩ := exists_unitary_extension W hW hf hcard
  refine ⟨dA, dB, e, U, hU1, hU2, ?_⟩
  intro ρ
  have hconj : U * (ρ ⊗ₖ single e e 1) * Uᴴ = W * ρ * Wᴴ := by
    ext y y'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.single_apply, mul_ite, mul_zero,
      ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one, hUW]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e) ?_]
    · simp [hUW]
    · intro u _ hu
      simp [Ne.symm hu]
  rw [hconj, hK ρ]
  ext b b'
  simp only [ptrace, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hFG : ∀ t : Fin dB,
      (∑ j, (∑ i, W (b, t) i * ρ i j) * star (W (b', t) j)) =
        (if (εB t).2 = a₀ then (1 : ℂ) else 0) *
          ∑ j, (∑ i, K (εB t).1 b i * ρ i j) * star (K (εB t).1 b' j) := by
    intro t
    simp only [hWdef, Matrix.of_apply]
    split_ifs with h <;> simp [Finset.mul_sum, Finset.sum_mul]
  symm
  refine (Fintype.sum_equiv εB
    (fun t : Fin dB => ∑ j, (∑ i, W (b, t) i * ρ i j) * star (W (b', t) j))
    (fun r : R × A => (if r.2 = a₀ then (1 : ℂ) else 0) *
      ∑ j, (∑ i, K r.1 b i * ρ i j) * star (K r.1 b' j)) hFG).trans ?_
  rw [Fintype.sum_prod_type]
  simp

/-- **Stinespring dilation.** Every completely positive trace-preserving map
`Φ : Matrix A A ℂ → Matrix B B ℂ` is the compression of a unitary conjugation:
there are ancilla spaces `ℂ^dA`, `ℂ^dB`, a pure ancilla state `|e⟩⟨e|` and a unitary
`U : ℂ^A ⊗ ℂ^dA → ℂ^B ⊗ ℂ^dB` such that
`Φ ρ = Tr_{ℂ^dB} (U (ρ ⊗ |e⟩⟨e|) U†)` for every `ρ`. -/
