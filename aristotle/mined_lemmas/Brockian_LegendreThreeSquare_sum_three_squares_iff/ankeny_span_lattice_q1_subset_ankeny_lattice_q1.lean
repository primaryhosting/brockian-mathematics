import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_span_lattice_q1_subset_ankeny_lattice_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    (ankeny_span_lattice_q1 n q b hn hq : Set E3) ⊆ ankeny_lattice_q1 n q b := by
  classical
  intro p hp
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis_q1 n q b hn hq
  have hp' : p ∈ (Submodule.span ℤ (Set.range B) : Set E3) := by
    simpa [ankeny_span_lattice_q1, B] using hp
  have hle :
      (Submodule.span ℤ (Set.range B)) ≤ (ankeny_lattice_q1 n q b).toIntSubmodule := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · -- i = 0: vector `(n, 0, 0)`
      have hx0 : (B 0) 0 = (n : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (0 : Fin 3) 0)
      have hx1 : (B 0) 1 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (0 : Fin 3) 1)
      have hx2 : (B 0) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (0 : Fin 3) 2)
      have hxy : (n : ℤ) ≡ (0 : ℤ) [ZMOD n] := by
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have hybz : (0 : ℤ) ≡ b * (0 : ℤ) [ZMOD q] := by
        simpa using (Int.ModEq.refl (0 : ℤ))
      have : (B 0) ∈ ankeny_lattice_q1 n q b := by
        refine ⟨(n : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 1: vector `(q, q, 0)`
      have hx0 : (B 1) 0 = (q : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (1 : Fin 3) 0)
      have hx1 : (B 1) 1 = (q : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (1 : Fin 3) 1)
      have hx2 : (B 1) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (1 : Fin 3) 2)
      have hxy : (q : ℤ) ≡ (q : ℤ) [ZMOD n] := by
        simpa using (Int.ModEq.refl (q : ℤ))
      have hybz : (q : ℤ) ≡ b * (0 : ℤ) [ZMOD q] := by
        -- `q ≡ 0 (mod q)`
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have : (B 1) ∈ ankeny_lattice_q1 n q b := by
        refine ⟨(q : ℤ), (q : ℤ), 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 2: vector `(b, b, 1)`
      have hx0 : (B 2) 0 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (2 : Fin 3) 0)
      have hx1 : (B 2) 1 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (2 : Fin 3) 1)
      have hx2 : (B 2) 2 = (1 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (2 : Fin 3) 2)
      have hxy : b ≡ b [ZMOD n] := by
        simpa using (Int.ModEq.refl b)
      have hybz : b ≡ b * (1 : ℤ) [ZMOD q] := by
        simpa using (Int.ModEq.refl b)
      have : (B 2) ∈ ankeny_lattice_q1 n q b := by
        refine ⟨b, b, 1, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
  have : p ∈ (ankeny_lattice_q1 n q b).toIntSubmodule := hle hp'
  simpa [AddSubgroup.coe_toIntSubmodule] using this

/-- A convenient full-rank ℤ-lattice for Ankeny has covolume `2nq`. -/
