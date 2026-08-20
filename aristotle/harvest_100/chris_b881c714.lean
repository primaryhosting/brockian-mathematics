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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- The character `x ↦ ζ^x` of `ZMod 12`. -/
noncomputable def xi (x : ZMod 12) : ℂ := zeta ^ x.val

/-- The Hückel eigenvalue `2 cos(2πk/12)`. -/
noncomputable def lam (k : ZMod 12) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 12)

/-- The adjacency matrix of the cycle `C₁₂`, described on `ZMod 12`. -/
def C12adj : Matrix (ZMod 12) (ZMod 12) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The discrete Fourier matrix. -/
noncomputable def Fm : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.of fun i j => xi (i * j)

/-- The inverse (up to the factor 12) discrete Fourier matrix. -/
noncomputable def Gm : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.of fun i j => xi (-(i * j))

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def Dm : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.diagonal lam

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 12 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 12 (by norm_num)

lemma zeta_pow_twelve : zeta ^ 12 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_ne_one {m : ℕ} (hm : m ≠ 0) (hlt : m < 12) : zeta ^ m ≠ 1 :=
  zeta_isPrimitiveRoot.pow_ne_one_of_pos_of_lt hm hlt

lemma xi_zero : xi 0 = 1 := by simp [xi]

lemma xi_add (x y : ZMod 12) : xi (x + y) = xi x * xi y := by
  have h : zeta ^ ((x.val + y.val) % 12) = zeta ^ (x.val + y.val) := by
    conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) 12]
    rw [pow_add, pow_mul, zeta_pow_twelve, one_pow, one_mul]
  simp only [xi, ZMod.val_add, h, pow_add]

lemma xi_natCast_mul (n : ℕ) (y : ZMod 12) : xi ((n : ZMod 12) * y) = xi y ^ n := by
  induction n with
  | zero => simp [xi_zero]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ZMod 12) * y = (n : ZMod 12) * y + y := by push_cast; ring
      rw [this, xi_add, ih, pow_succ]

lemma xi_mul (x y : ZMod 12) : xi (x * y) = xi y ^ x.val := by
  conv_lhs => rw [show x = ((x.val : ℕ) : ZMod 12) from (ZMod.natCast_zmod_val x).symm]
  exact xi_natCast_mul x.val y

lemma xi_neg_mul_self (x : ZMod 12) : xi x * xi (-x) = 1 := by
  rw [← xi_add, add_neg_cancel, xi_zero]

lemma xi_ne_zero (x : ZMod 12) : xi x ≠ 0 := by
  intro h
  have := xi_neg_mul_self x
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma xi_pow_twelve (x : ZMod 12) : xi x ^ 12 = 1 := by
  rw [xi, ← pow_mul, mul_comm, pow_mul, zeta_pow_twelve, one_pow]

lemma xi_eq_one_iff (d : ZMod 12) : xi d = 1 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    have hv : d.val ≠ 0 := fun hv => hd ((ZMod.val_eq_zero d).mp hv)
    exact zeta_pow_ne_one hv (ZMod.val_lt d) h
  · rintro rfl; exact xi_zero

/-- Orthogonality of characters. -/
lemma sum_xi (d : ZMod 12) : ∑ j : ZMod 12, xi (j * d) = if d = 0 then 12 else 0 := by
  have hstep : ∀ j : ZMod 12, xi (j * d) = xi d ^ j.val := fun j => xi_mul j d
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  have hrange : ∑ j : ZMod 12, xi d ^ j.val = ∑ n ∈ Finset.range 12, xi d ^ n :=
    Fin.sum_univ_eq_sum_range (fun n => xi d ^ n) 12
  rw [hrange]
  by_cases hd : d = 0
  · subst hd; simp [xi_zero]
  · rw [if_neg hd]
    have h1 : xi d ≠ 1 := fun h => hd ((xi_eq_one_iff d).mp h)
    rw [geom_sum_eq h1, xi_pow_twelve, sub_self, zero_div]

lemma xi_eq_exp (k : ZMod 12) :
    xi k = Complex.exp ((2 * Real.pi * (k.val : ℝ) / 12 : ℝ) * Complex.I) := by
  rw [xi, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma lam_eq (k : ZMod 12) : xi k + xi (-k) = lam k := by
  have h1 : xi (-k) = (xi k)⁻¹ :=
    (DivisionMonoid.inv_eq_of_mul (xi k) (xi (-k)) (xi_neg_mul_self k)).symm
  rw [h1, xi_eq_exp k, lam]
  rw [Complex.ofReal_cos]
  rw [Complex.cos]
  push_cast
  rw [← Complex.exp_neg]
  ring_nf

lemma cond_iff (j l : ZMod 12) : (l = j + 1 ∨ l = j - 1) ↔ (j = l - 1 ∨ j = l + 1) := by
  constructor
  · rintro (rfl | rfl)
    · left; ring
    · right; ring
  · rintro (rfl | rfl)
    · left; ring
    · right; ring

lemma ne_add_one_sub_one (i : ZMod 12) : i + 1 ≠ i - 1 := by
  intro h
  have h2 : (2 : ZMod 12) = 0 := by linear_combination h
  exact absurd h2 (by decide)

lemma sum_indicator_left (i : ZMod 12) (u : ZMod 12 → ℂ) :
    ∑ j : ZMod 12, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * u j
      = u (i + 1) + u (i - 1) := by
  have h1 : ∀ j : ZMod 12, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * u j
      = if j = i + 1 ∨ j = i - 1 then u j else 0 := by
    intro j; split <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_filter]
  have h2 : Finset.univ.filter (fun j : ZMod 12 => j = i + 1 ∨ j = i - 1) = {i + 1, i - 1} := by
    ext j; simp
  rw [h2, Finset.sum_pair (ne_add_one_sub_one i)]

lemma sum_indicator_right (l : ZMod 12) (u : ZMod 12 → ℂ) :
    ∑ j : ZMod 12, u j * (if l = j + 1 ∨ l = j - 1 then (1 : ℂ) else 0)
      = u (l - 1) + u (l + 1) := by
  have h1 : ∀ j : ZMod 12, u j * (if l = j + 1 ∨ l = j - 1 then (1 : ℂ) else 0)
      = if j = l - 1 ∨ j = l + 1 then u j else 0 := by
    intro j
    rw [if_congr (cond_iff j l) rfl rfl]
    split <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_filter]
  have h2 : Finset.univ.filter (fun j : ZMod 12 => j = l - 1 ∨ j = l + 1) = {l - 1, l + 1} := by
    ext j; simp
  have h3 : (l : ZMod 12) - 1 ≠ l + 1 := fun h => (ne_add_one_sub_one l) h.symm
  rw [h2, Finset.sum_pair h3]

/-- The Fourier matrices are inverse to each other up to the factor 12. -/
lemma Fm_mul_Gm : Fm * Gm = (12 : ℂ) • (1 : Matrix (ZMod 12) (ZMod 12) ℂ) := by
  ext k l
  rw [Matrix.mul_apply]
  have h : ∀ j : ZMod 12, Fm k j * Gm j l = xi (j * (k - l)) := by
    intro j
    show xi (k * j) * xi (-(j * l)) = xi (j * (k - l))
    rw [← xi_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => h j), sum_xi]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [if_neg (fun h => hkl (by linear_combination h))]
    simp [hkl]

/-- `Gm` intertwines the adjacency matrix with the diagonal matrix of eigenvalues. -/
lemma Gm_mul_C12adj : Gm * C12adj = Dm * Gm := by
  ext k l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have h : ∀ j : ZMod 12, Gm k j * C12adj j l
      = (fun j : ZMod 12 => xi (-(k * j))) j * (if l = j + 1 ∨ l = j - 1 then (1 : ℂ) else 0) :=
    fun j => rfl
  rw [Finset.sum_congr rfl (fun j _ => h j), sum_indicator_right]
  have e1 : xi (-(k * (l - 1))) = xi (-(k * l)) * xi k := by
    rw [← xi_add]; congr 1; ring
  have e2 : xi (-(k * (l + 1))) = xi (-(k * l)) * xi (-k) := by
    rw [← xi_add]; congr 1; ring
  rw [e1, e2]
  have hD : ∀ j : ZMod 12, Dm k j * Gm j l = if j = k then lam k * xi (-(k * l)) else 0 := by
    intro j
    show (Matrix.diagonal lam) k j * xi (-(j * l)) = _
    rw [Matrix.diagonal_apply]
    split_ifs with h1 h2 h2
    · subst h2; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  rw [Finset.sum_congr rfl (fun j _ => hD j), Finset.sum_ite_eq' Finset.univ k
    (fun _ => lam k * xi (-(k * l)))]
  simp only [Finset.mem_univ, if_true]
  rw [← lam_eq k]
  ring

/-- Each `2 cos(2πk/12)` is an eigenvalue, with the Fourier vector as eigenvector. -/
lemma exists_eigenvector (k : ZMod 12) :
    ∃ v : ZMod 12 → ℂ, v ≠ 0 ∧ C12adj *ᵥ v = lam k • v := by
  refine ⟨fun j => xi (j * k), ?_, ?_⟩
  · intro h
    have h0 : xi ((0 : ZMod 12) * k) = 0 := congrFun h 0
    exact xi_ne_zero _ h0
  · funext i
    show ∑ j : ZMod 12, C12adj i j * xi (j * k) = lam k * xi (i * k)
    have h : ∀ j : ZMod 12, C12adj i j * xi (j * k)
        = (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * (fun j : ZMod 12 => xi (j * k)) j :=
      fun j => rfl
    rw [Finset.sum_congr rfl (fun j _ => h j), sum_indicator_left]
    have e1 : xi ((i + 1) * k) = xi (i * k) * xi k := by rw [← xi_add]; congr 1; ring
    have e2 : xi ((i - 1) * k) = xi (i * k) * xi (-k) := by rw [← xi_add]; congr 1; ring
    rw [e1, e2, ← lam_eq k]
    ring

/-- Every eigenvalue of the adjacency matrix is one of the `2 cos(2πk/12)`. -/
lemma eigenvalue_mem (μ : ℂ) (v : ZMod 12 → ℂ) (hv : v ≠ 0) (h : C12adj *ᵥ v = μ • v) :
    ∃ k : ZMod 12, μ = lam k := by
  set w : ZMod 12 → ℂ := Gm *ᵥ v with hw
  have hwne : w ≠ 0 := by
    intro h0
    have : Fm *ᵥ w = 0 := by rw [h0, Matrix.mulVec_zero]
    rw [hw, Matrix.mulVec_mulVec, Fm_mul_Gm] at this
    have h12 : ((12 : ℂ) • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)) *ᵥ v = (12 : ℂ) • v := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h12] at this
    exact hv (by simpa using this)
  have hDw : Dm *ᵥ w = μ • w := by
    rw [hw, Matrix.mulVec_mulVec, ← Gm_mul_C12adj, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_smul]
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hwne (funext hc)
  refine ⟨k, ?_⟩
  have := congrFun hDw k
  have hd : (Dm *ᵥ w) k = lam k * w k := by
    show ∑ j : ZMod 12, (Matrix.diagonal lam) k j * w j = lam k * w k
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Matrix.diagonal_apply] : ∀ j ∈ Finset.univ,
        (Matrix.diagonal lam) k j * w j = (if k = j then lam k else 0) * w j)]
    simp [Finset.sum_ite_eq]
  rw [hd] at this
  exact (mul_right_cancel₀ hk this).symm

lemma adjMatrix_eq : ((SimpleGraph.cycleGraph 12).adjMatrix ℂ) = C12adj := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  show (if (SimpleGraph.cycleGraph 12).Adj i j then (1 : ℂ) else 0) = _
  congr 1
  simp only [eq_iff_iff, SimpleGraph.cycleGraph_adj]
  revert i j
  decide

/-- **Hückel theory for C₁₂.** A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₁₂` if and only if `μ = 2 cos(2πk/12)` for some `k ∈ {0,…,11}`. -/
theorem huckel_C12 (μ : ℂ) :
    (∃ v : Fin 12 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : Fin 12, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 12) := by
  rw [adjMatrix_eq]
  constructor
  · rintro ⟨v, hv, hAv⟩
    obtain ⟨k, hk⟩ := eigenvalue_mem μ v hv hAv
    exact ⟨⟨k.val, ZMod.val_lt k⟩, hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv, hAv⟩ := exists_eigenvector (k : ZMod 12)
    refine ⟨v, hv, ?_⟩
    rw [hAv, hk]
    rfl

end Chem

