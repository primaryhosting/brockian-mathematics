import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped MatrixOrder ComplexOrder

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The ampliation `id_d ⊗ Φ` of a linear map `Φ` between matrix algebras, described
blockwise: the `(a, b)` block of the output is `Φ` applied to the `(a, b)` block of the input. -/

lemma exists_kraus_of_posSemidef_choi {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : (choiMatrix Φ).PosSemidef) :
    ∃ V : (n × m) → Matrix m n ℂ, ∀ A, Φ A = ∑ k, V k * A * (V k)ᴴ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun k => Matrix.of fun s i => star (B k (i, s)), fun A => ?_⟩
  ext s t
  rw [apply_eq_sum Φ A s t]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hc : ∀ i j : n, Φ (Matrix.single i j 1) s t
      = ∑ k : n × m, star (B k (i, s)) * B k (j, t) := by
    intro i j
    have := congrFun (congrFun hB (i, s)) (j, t)
    simpa [choiMatrix, Matrix.mul_apply, Matrix.star_apply] using this
  have triple : ∀ f : n → n → (n × m) → ℂ,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
    intro f
    have step1 : ∀ j : n, (∑ i, ∑ k, f i j k) = ∑ k, ∑ i, f i j k := fun _ => Finset.sum_comm
    rw [Finset.sum_comm]
    simp_rw [step1]
    rw [Finset.sum_comm]
  simp only [hc, Finset.mul_sum, star_star, Finset.sum_mul]
  rw [triple]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
