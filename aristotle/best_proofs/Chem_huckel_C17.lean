import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/
noncomputable def zeta17 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma isPrimitiveRoot_zeta17 : IsPrimitiveRoot zeta17 17 := by
  simpa [zeta17] using Complex.isPrimitiveRoot_exp 17 (by norm_num)

/-- The additive character `x ↦ ζ¹⁷ ^ x` on `ZMod 17`. -/
noncomputable def ee (x : ZMod 17) : ℂ := zeta17 ^ x.val

lemma zeta17_pow_eq_of_modEq {a b : ℕ} (h : a % 17 = b % 17) :
    zeta17 ^ a = zeta17 ^ b := by
  have h17 : zeta17 ^ (17 : ℕ) = 1 := isPrimitiveRoot_zeta17.pow_eq_one
  have key : ∀ n : ℕ, zeta17 ^ n = zeta17 ^ (n % 17) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 17]
    rw [pow_add, pow_mul, h17, one_pow, one_mul]
  rw [key a, key b, h]

lemma ee_add (x y : ZMod 17) : ee (x + y) = ee x * ee y := by
  have hval : (x + y).val = (x.val + y.val) % 17 := by
    simp [ZMod.val_add]
  rw [ee, ee, ee, hval, ← pow_add]
  exact zeta17_pow_eq_of_modEq (by simp)

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_mul_ee_neg (x : ZMod 17) : ee x * ee (-x) = 1 := by
  rw [← ee_add]; simp [ee_zero]

lemma ee_natCast_mul (n : ℕ) (x : ZMod 17) : ee ((n : ZMod 17) * x) = (ee x) ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih =>
      have h : ((n + 1 : ℕ) : ZMod 17) * x = (n : ZMod 17) * x + x := by push_cast; ring
      rw [h, ee_add, ih, pow_succ]

lemma ee_pow_val (k m : ZMod 17) : ee (k * m) = (ee m) ^ k.val := by
  have h : ((k.val : ℕ) : ZMod 17) = k := by simp
  calc ee (k * m) = ee (((k.val : ℕ) : ZMod 17) * m) := by rw [h]
    _ = (ee m) ^ k.val := ee_natCast_mul _ _

lemma ee_pow_seventeen (m : ZMod 17) : (ee m) ^ (17 : ℕ) = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, isPrimitiveRoot_zeta17.pow_eq_one, one_pow]

lemma ee_ne_one {m : ZMod 17} (hm : m ≠ 0) : ee m ≠ 1 := by
  intro h
  have hdvd : (17 : ℕ) ∣ m.val := (isPrimitiveRoot_zeta17.pow_eq_one_iff_dvd m.val).1 h
  have hlt : m.val < 17 := ZMod.val_lt m
  have hz : m.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  exact hm (by simpa [ZMod.val_eq_zero] using hz)

/-- Character sum: `∑_{k} ζ^{k m} = 17` if `m = 0`, and `0` otherwise. -/
lemma sum_ee_mul (m : ZMod 17) :
    (∑ k : ZMod 17, ee (k * m)) = if m = 0 then (17 : ℂ) else 0 := by
  have hrw : (∑ k : ZMod 17, ee (k * m)) = ∑ i ∈ Finset.range 17, (ee m) ^ i := by
    rw [Finset.sum_congr rfl (fun k _ => ee_pow_val k m)]
    exact Fin.sum_univ_eq_sum_range (fun i => (ee m) ^ i) 17
  rw [hrw]
  by_cases hm : m = 0
  · simp [hm, ee_zero]
  · rw [if_neg hm, geom_sum_eq (ee_ne_one hm), ee_pow_seventeen]
    simp

/-- The adjacency matrix of the cycle graph `C₁₇`, with vertices indexed by `ZMod 17`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/
def C17adj : Matrix (ZMod 17) (ZMod 17) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- Discrete Fourier transform matrix. -/
noncomputable def U17 : Matrix (ZMod 17) (ZMod 17) ℂ := fun j k => ee (j * k)

/-- Inverse discrete Fourier transform matrix. -/
noncomputable def V17 : Matrix (ZMod 17) (ZMod 17) ℂ := fun k j => (17 : ℂ)⁻¹ * ee (-(j * k))

/-- The diagonal matrix of eigenvalues. -/
noncomputable def D17 : Matrix (ZMod 17) (ZMod 17) ℂ :=
  Matrix.diagonal (fun k => ee k + ee (-k))

lemma U17_mul_V17 : U17 * V17 = 1 := by
  ext j l
  have hentry : ∀ k : ZMod 17, U17 j k * V17 k l = (17 : ℂ)⁻¹ * ee (k * (j - l)) := by
    intro k
    have : ee (j * k) * ee (-(l * k)) = ee (k * (j - l)) := by
      rw [← ee_add]; ring_nf
    simp only [U17, V17]
    rw [← this]; ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => hentry k), ← Finset.mul_sum,
    sum_ee_mul]
  by_cases h : j = l
  · subst h; simp [Matrix.one_apply_eq]
  · have hne : j - l ≠ 0 := sub_ne_zero_of_ne h
    simp [hne, h]

lemma V17_mul_U17 : V17 * U17 = 1 := mul_eq_one_comm.1 U17_mul_V17

lemma succ_ne_pred (i : ZMod 17) : i + 1 ≠ i - 1 := by
  revert i; decide

lemma C17adj_mul_U17 : C17adj * U17 = U17 * D17 := by
  ext i k
  have hleft : (C17adj * U17) i k = U17 (i + 1) k + U17 (i - 1) k := by
    rw [Matrix.mul_apply]
    have hterm : ∀ j : ZMod 17, C17adj i j * U17 j k =
        if j ∈ ({i + 1, i - 1} : Finset (ZMod 17)) then U17 j k else 0 := by
      intro j
      by_cases h : j = i + 1 ∨ j = i - 1
      · simp [C17adj, h, Finset.mem_insert, Finset.mem_singleton]
      · simp only [C17adj, if_neg h]
        rw [if_neg (by simpa [Finset.mem_insert, Finset.mem_singleton] using h)]
        ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_pair (succ_ne_pred i)]
  have hright : (U17 * D17) i k = U17 i k * (ee k + ee (-k)) := by
    rw [Matrix.mul_apply]
    simp [D17, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [hleft, hright]
  simp only [U17]
  rw [mul_add, ← ee_add, ← ee_add]
  congr 2 <;> ring

/-- The diagonal entries are the Hückel eigenvalues `2 cos (2πk/17)`. -/
lemma ee_add_ee_neg (k : ZMod 17) :
    ee k + ee (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * k.val / 17 with ht
  have h1 : ee k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ee, zeta17, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h2 : ee (-k) = Complex.exp (-(t : ℂ) * Complex.I) := by
    have hmul : ee k * ee (-k) = 1 := ee_mul_ee_neg k
    have hexp : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have hz : (t : ℂ) * Complex.I + -(t : ℂ) * Complex.I = 0 := by ring
      rw [hz, Complex.exp_zero]
    rw [h1] at hmul
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (hmul.trans hexp.symm)
  rw [h1, h2, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

theorem charpoly_C17adj :
    C17adj.charpoly =
      ∏ k : ZMod 17, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ) : ℂ)) := by
  have hA : C17adj = U17 * (D17 * V17) := by
    have := congrArg (fun M => M * V17) C17adj_mul_U17
    simp only [mul_assoc] at this
    rw [U17_mul_V17, mul_one] at this
    simpa [mul_assoc] using this
  have : C17adj.charpoly = D17.charpoly := by
    rw [hA, Matrix.charpoly_mul_comm, mul_assoc, V17_mul_U17, mul_one]
  rw [this, D17, Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl (fun k _ => by rw [ee_add_ee_neg k])

/-- **Hückel theory for `C₁₇`.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₇` factors as `∏_{k=0}^{16} (X - 2cos(2πk/17))`; i.e. the eigenvalues of `C₁₇` are
exactly `2 cos (2πk/17)`, `k = 0, …, 16`. -/
theorem huckel_C17 :
    C17adj.charpoly =
      ∏ k : Fin 17, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)) :=
  charpoly_C17adj

/-- The eigenvalues of `C₁₇`: `z` is a root of the characteristic polynomial iff
`z = 2 cos (2πk/17)` for some `k = 0, …, 16`. -/
theorem huckel_C17_roots (z : ℂ) :
    C17adj.charpoly.IsRoot z ↔
      ∃ k : Fin 17, z = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ) := by
  rw [huckel_C17, Polynomial.IsRoot.def, Polynomial.eval_prod]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, by simpa [sub_eq_zero] using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by simp [hk]⟩

/-- Explicit eigenvectors: the `k`-th Fourier mode `j ↦ ζ^{jk}` is a nonzero eigenvector of the
adjacency matrix with eigenvalue `2 cos (2πk/17)`. -/
theorem huckel_C17_hasEigenvector (k : ZMod 17) :
    (fun j => ee (j * k)) ≠ (0 : ZMod 17 → ℂ) ∧
      C17adj.mulVec (fun j => ee (j * k))
        = ((2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ) : ℂ) • (fun j => ee (j * k)) := by
  constructor
  · intro h
    have h0 : ee (0 * k) = 0 := congrFun h 0
    rw [zero_mul, ee_zero] at h0
    exact one_ne_zero h0
  · funext i
    have hcol := congrFun (congrFun C17adj_mul_U17 i) k
    rw [Matrix.mul_apply, Matrix.mul_apply] at hcol
    have hright : ∑ j : ZMod 17, U17 i j * D17 j k = ee (i * k) * (ee k + ee (-k)) := by
      simp [D17, U17, Matrix.diagonal_apply, Finset.sum_ite_eq', mul_comm]
    rw [hright] at hcol
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [← ee_add_ee_neg k, mul_comm (ee k + ee (-k)) (ee (i * k)), ← hcol]
    exact Finset.sum_congr rfl (fun j _ => by simp [U17])

end Chem

#print axioms Chem.huckel_C17
#print axioms Chem.huckel_C17_roots
#print axioms Chem.huckel_C17_hasEigenvector

