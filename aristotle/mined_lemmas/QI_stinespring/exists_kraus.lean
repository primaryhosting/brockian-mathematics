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

lemma exists_kraus [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ} (hCP : IsCompletelyPositive Φ) :
    ∃ K : (A × B) → Matrix B A ℂ, ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ s, K s * ρ * (K s)ᴴ := by
  classical
  obtain ⟨M, hM⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp (choi_posSemidef hCP)
  refine ⟨fun s => Matrix.of fun a i => star (M s (i, a)), ?_⟩
  intro ρ
  have hchoi : ∀ (i j : A) (a b : B),
      choi Φ (i, a) (j, b) = ∑ s, star (M s (i, a)) * M s (j, b) := by
    intro i j a b
    rw [hM]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hsingle : ∀ (i j : A) (a b : B),
      (Φ (single i j (ρ i j))) a b = ρ i j * choi Φ (i, a) (j, b) := by
    intro i j a b
    have h1 : single i j (ρ i j) = ρ i j • single i j (1 : ℂ) := by
      ext x y; simp [Matrix.single_apply]
    rw [h1, map_smul]
    simp [choi]
  ext a b
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  rw [map_sum]
  simp only [Matrix.sum_apply, map_sum, hsingle, hchoi]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_star,
    Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm₃ (fun i j s => ρ i j * (star (M s (i, a)) * M s (j, b)))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The Kraus operators of a trace-preserving map satisfy the completeness relation. -/
