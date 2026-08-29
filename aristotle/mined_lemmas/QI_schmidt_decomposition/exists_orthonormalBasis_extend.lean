import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/

lemma exists_orthonormalBasis_extend {r : ℕ} (e : Fin r → EuclideanSpace ℂ (Fin m))
    (he : Orthonormal ℂ e) (hr : r ≤ m) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      ∀ k : Fin r, b (Fin.castLE hr k) = e k := by
  classical
  set v : Fin m → EuclideanSpace ℂ (Fin m) := fun i => if h : (i:ℕ) < r then e ⟨i, h⟩ else 0
    with hv
  set s : Set (Fin m) := {i | (i:ℕ) < r} with hs
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  have hon : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨i', hi'⟩
    have hi2 : (i:ℕ) < r := hi
    have hi2' : (i':ℕ) < r := hi'
    simp only [Set.restrict_apply, hv, dif_pos hi2, dif_pos hi2']
    rw [orthonormal_iff_ite] at he
    rw [he]
    congr 1
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨b, fun k => ?_⟩
  have hmem : (Fin.castLE hr k) ∈ s := by simp [hs]
  rw [hb _ hmem]
  simp only [hv]
  rw [dif_pos (show ((Fin.castLE hr k : Fin m) : ℕ) < r by simp [k.isLt])]
  congr 1

