import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

lemma zeta_prim : IsPrimitiveRoot zeta 15 := by
  have := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_fifteen : zeta ^ 15 = 1 := zeta_prim.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := by
  simp [zeta, Complex.exp_ne_zero]

lemma zeta_pow_modEq_of_le {a b : ℕ} (hab : a ≤ b) (h : a ≡ b [MOD 15]) :
    zeta ^ a = zeta ^ b := by
  obtain ⟨t, ht⟩ : 15 ∣ (b - a) := (Nat.modEq_iff_dvd' hab).mp h
  have hb : b = a + 15 * t := by omega
  subst hb
  rw [pow_add, pow_mul, zeta_pow_fifteen, one_pow, mul_one]

lemma zeta_pow_modEq {a b : ℕ} (h : a ≡ b [MOD 15]) : zeta ^ a = zeta ^ b := by
  rcases le_total a b with hab | hab
  · exact zeta_pow_modEq_of_le hab h
  · exact (zeta_pow_modEq_of_le hab h.symm).symm

lemma zeta_pow_inj {a b : ℕ} (ha : a < 15) (hb : b < 15) (h : zeta ^ a = zeta ^ b) : a = b := by
  have key : ∀ a b : ℕ, a ≤ b → b < 15 → zeta ^ a = zeta ^ b → a = b := by
    intro a b hab hb h
    have h1 : zeta ^ a * zeta ^ (b - a) = zeta ^ a * 1 := by
      rw [mul_one, ← pow_add, show a + (b - a) = b by omega]
      exact h.symm
    have h2 : zeta ^ (b - a) = 1 := mul_left_cancel₀ (pow_ne_zero _ zeta_ne_zero) h1
    have h3 := (zeta_prim.pow_eq_one_iff_dvd _).mp h2
    omega
  rcases le_total a b with hab | hab
  · exact key a b hab hb h
  · exact (key b a hab ha h.symm).symm

/-- The character values `ζ ^ i` for `i : Fin 15`. -/
noncomputable def g (i : Fin 15) : ℂ := zeta ^ i.val

lemma g_ne_zero (i : Fin 15) : g i ≠ 0 := pow_ne_zero _ zeta_ne_zero

lemma g_add (x y : Fin 15) : g (x + y) = g x * g y := by
  unfold g
  rw [Fin.val_add, zeta_pow_modEq (Nat.mod_modEq _ _), pow_add]

lemma g_pow_fifteen (i : Fin 15) : (g i) ^ 15 = 1 := by
  unfold g
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_fifteen, one_pow]

lemma g_injective {i l : Fin 15} (h : g i = g l) : i = l :=
  Fin.ext (zeta_pow_inj i.isLt l.isLt h)

lemma g_one : g 1 = zeta := by
  simp [g]

/-- The DFT matrix. -/
noncomputable def Pm : Matrix (Fin 15) (Fin 15) ℂ := Matrix.of fun i l => (g i) ^ (l.val)

/-- The inverse DFT matrix. -/
noncomputable def Qm : Matrix (Fin 15) (Fin 15) ℂ :=
  Matrix.of fun j l => (15 : ℂ)⁻¹ * ((g l) ^ (j.val))⁻¹

/-- The diagonal matrix of eigenvalues. -/
noncomputable def Dm : Matrix (Fin 15) (Fin 15) ℂ := Matrix.diagonal fun l => g l + (g l)⁻¹

lemma Pm_mul_Qm : Pm * Qm = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 15, Pm i j * Qm j l = (15 : ℂ)⁻¹ * (g i * (g l)⁻¹) ^ (j.val) := by
    intro j
    simp only [Pm, Qm, Matrix.of_apply]
    rw [mul_pow, inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (g i * (g l)⁻¹) ^ j) 15, Matrix.one_apply]
  by_cases h : i = l
  · subst h
    rw [mul_inv_cancel₀ (g_ne_zero i)]
    simp
  · have hx : g i * (g l)⁻¹ ≠ 1 := by
      intro hx
      exact h (g_injective (mul_inv_eq_one₀ (g_ne_zero l) |>.mp hx))
    have hx15 : (g i * (g l)⁻¹) ^ 15 = 1 := by
      rw [mul_pow, inv_pow, g_pow_fifteen, g_pow_fifteen, inv_one, mul_one]
    rw [geom_sum_eq hx, hx15]
    simp [h]

lemma Qm_mul_Pm : Qm * Pm = 1 := mul_eq_one_comm.mp Pm_mul_Qm

lemma g_sub_one (i : Fin 15) : g (i - 1) = g i * zeta⁻¹ := by
  have h := g_add (i - 1) 1
  rw [sub_add_cancel, g_one] at h
  rw [h, mul_assoc, mul_inv_cancel₀ zeta_ne_zero, mul_one]

lemma adj_mul_Pm : ((cycleGraph 15).adjMatrix ℂ) * Pm = Pm * Dm := by
  ext i l
  have hne : i - 1 ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  have h1 : (((cycleGraph 15).adjMatrix ℂ) * Pm) i l
      = ∑ j ∈ (cycleGraph 15).neighborFinset i, Pm j l := by
    have : (((cycleGraph 15).adjMatrix ℂ) * Pm) i l
        = (((cycleGraph 15).adjMatrix ℂ) *ᵥ (fun j => Pm j l)) i := rfl
    rw [this, SimpleGraph.adjMatrix_mulVec_apply]
  rw [h1, show (cycleGraph 15).neighborFinset i = {i - 1, i + 1} from
      SimpleGraph.cycleGraph_neighborFinset (n := 13), Finset.sum_pair hne,
    Dm, Matrix.mul_diagonal]
  have e1 : Pm (i + 1) l = Pm i l * g l := by
    simp only [Pm, Matrix.of_apply, g_add, g_one, mul_pow]
    rfl
  have e2 : Pm (i - 1) l = Pm i l * (g l)⁻¹ := by
    simp only [Pm, Matrix.of_apply, g_sub_one, mul_pow, inv_pow]
    rfl
  rw [e1, e2]
  ring

lemma diag_eq_cos (l : Fin 15) :
    g l + (g l)⁻¹ = ((2 * Real.cos (2 * Real.pi * l.val / 15) : ℝ) : ℂ) := by
  have h1 : g l = Complex.exp ((2 * Real.pi * l.val / 15 : ℝ) * Complex.I) := by
    rw [g, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- **Hückel theory for the cycle `C₁₅`.**  The eigenvalues (spectrum) of the adjacency matrix
of the cycle graph on 15 vertices are exactly the numbers `2 * cos (2 * π * k / 15)`,
`k = 0, 1, …, 14`. -/
theorem huckel_C15 :
    spectrum ℂ ((cycleGraph 15).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 15 ∧ z = ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ)} := by
  have hA : ((cycleGraph 15).adjMatrix ℂ) = Pm * Dm * Qm := by
    rw [← adj_mul_Pm, Matrix.mul_assoc, Pm_mul_Qm, Matrix.mul_one]
  let u : (Matrix (Fin 15) (Fin 15) ℂ)ˣ := ⟨Pm, Qm, Pm_mul_Qm, Qm_mul_Pm⟩
  have h2 : spectrum ℂ ((cycleGraph 15).adjMatrix ℂ) = spectrum ℂ Dm := by
    rw [hA, show Pm * Dm * Qm = (↑u * Dm * ↑u⁻¹ : Matrix (Fin 15) (Fin 15) ℂ) from rfl,
      spectrum.units_conjugate]
  rw [h2, Dm, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.val, l.isLt, diag_eq_cos l⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, diag_eq_cos ⟨k, hk⟩⟩

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

