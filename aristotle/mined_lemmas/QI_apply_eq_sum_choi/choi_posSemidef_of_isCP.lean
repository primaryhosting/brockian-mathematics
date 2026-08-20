/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The Choi–Jamiołkowski isomorphism

For a linear map `Φ` between finite-dimensional matrix algebras we prove that the following
are equivalent:

* `Φ` is completely positive (`QI.IsCP`), i.e. all amplifications `id ⊗ Φ` preserve positive
  semidefiniteness;
* the Choi matrix of `Φ` (`QI.choiMatrix`) is positive semidefinite;
* `Φ` admits a Kraus decomposition (`QI.HasKraus`).

The main statement is `QI.choi_jamiolkowski`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The amplification `id_{Fin k} ⊗ Φ` of a linear map `Φ` on matrices: it applies `Φ` to each
`m × m` block of a `(Fin k × m) × (Fin k × m)` matrix. -/

theorem choi_posSemidef_of_isCP {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (h : IsCP Φ) :
    (choiMatrix Φ).PosSemidef := by
  set K := Fintype.card m
  set e : m ≃ Fin K := Fintype.equivFin m
  -- the (unnormalised) maximally entangled state `|Ω⟩⟨Ω|`
  set v : Matrix (Fin K × m) Unit ℂ := Matrix.of fun x _ => if x.1 = e x.2 then 1 else 0 with hv
  set om : Matrix (Fin K × m) (Fin K × m) ℂ := v * vᴴ with hom
  have hamp := h K om (Matrix.posSemidef_self_mul_conjTranspose v)
  set E : m × n ≃ Fin K × n := e.prodCongr (Equiv.refl n) with hE
  have hblock : ∀ a b : Fin K,
      (Matrix.of fun i j => om (a, i) (b, j)) = Matrix.single (e.symm a) (e.symm b) (1 : ℂ) := by
    intro a b
    ext i j
    have h1 : (i = e.symm a) ↔ (a = e i) := by constructor <;> intro hx <;> simp [hx]
    have h2 : (j = e.symm b) ↔ (b = e j) := by constructor <;> intro hx <;> simp [hx]
    simp only [hom, hv, Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, Finset.univ_unique, Finset.sum_const, Finset.card_singleton,
      one_smul, ite_and]
    split_ifs <;> simp_all
  have hsub : choiMatrix Φ = (amp Φ K om).submatrix ⇑E ⇑E := by
    ext ⟨i, p⟩ ⟨j, q⟩
    simp [choiMatrix, amp, Matrix.submatrix_apply, hE, hblock]
  rw [hsub]
  exact (Matrix.posSemidef_submatrix_equiv E).mpr hamp

/-- **Choi–Jamiołkowski isomorphism** (Choi's theorem on completely positive maps):
for a linear map `Φ` between (finite-dimensional) matrix algebras, the following are equivalent:
`Φ` is completely positive; the Choi matrix of `Φ` is positive semidefinite; `Φ` admits a Kraus
decomposition. -/
