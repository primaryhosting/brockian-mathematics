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

namespace Chem

open Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₄`, viewed with vertex set `ZMod 14`
(which is definitionally `Fin 14`). -/
noncomputable def C14 : Matrix (ZMod 14) (ZMod 14) ℂ :=
  SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)

/-- A primitive 14-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

lemma zeta_primitive : IsPrimitiveRoot zeta 14 := by
  have := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [zeta] using this

/-- The character `x ↦ ζ^x` of `ZMod 14`. -/
noncomputable def ch (x : ZMod 14) : ℂ := zeta ^ x.val

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 14) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 14]
  rw [pow_add, pow_mul, zeta_primitive.pow_eq_one, one_pow, one_mul]

lemma ch_add (x y : ZMod 14) : ch (x + y) = ch x * ch y := by
  simp only [ch, ZMod.val_add, ← pow_add]
  exact zeta_pow_mod _

lemma ch_zero : ch 0 = 1 := by simp [ch]

lemma ch_eq_one_iff (x : ZMod 14) : ch x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hd : (14 : ℕ) ∣ x.val := (zeta_primitive.pow_eq_one_iff_dvd x.val).1 h
    have hlt : x.val < 14 := ZMod.val_lt x
    have hv : x.val = 0 := by
      rcases Nat.eq_zero_or_pos x.val with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 hd) (by omega)
    exact (ZMod.val_eq_zero x).1 hv
  · rintro rfl; exact ch_zero

lemma ch_ne_zero (x : ZMod 14) : ch x ≠ 0 := by
  simp [ch, zeta, Complex.exp_ne_zero]

lemma ch_neg_mul_self (x : ZMod 14) : ch x * ch (-x) = 1 := by
  rw [← ch_add]; simp [ch_zero]

/-- Orthogonality / geometric-sum relation for the character. -/
lemma sum_ch (c : ZMod 14) : (∑ j : ZMod 14, ch (j * c)) = if c = 0 then 14 else 0 := by
  by_cases hc : c = 0
  · subst hc; simp [ch_zero]
  · simp only [hc, if_false]
    set S : ℂ := ∑ j : ZMod 14, ch (j * c) with hS
    have hshift : ch c * S = S := by
      rw [hS, Finset.mul_sum]
      have : ∀ j : ZMod 14, ch c * ch (j * c) = ch ((j + 1) * c) := by
        intro j
        rw [← ch_add]
        ring_nf
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 14)) _ _ (fun j => rfl)
    have hne : ch c ≠ 1 := fun h => hc ((ch_eq_one_iff c).1 h)
    have : (ch c - 1) * S = 0 := by linear_combination hshift
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

/-- The (unnormalised) discrete Fourier matrix. -/
noncomputable def P : Matrix (ZMod 14) (ZMod 14) ℂ := fun i k => ch (i * k)

/-- Its inverse. -/
noncomputable def Q : Matrix (ZMod 14) (ZMod 14) ℂ := fun k j => (14 : ℂ)⁻¹ * ch (-(k * j))

/-- The eigenvalue attached to the frequency `k`. -/
noncomputable def lam (k : ZMod 14) : ℂ := ch k + ch (-k)

lemma P_mul_Q : P * Q = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : ZMod 14, P a j * Q j b = (14 : ℂ)⁻¹ * ch (j * (a - b)) := by
    intro j
    simp only [P, Q]
    rw [← mul_assoc, mul_comm (ch (a * j)) ((14:ℂ)⁻¹), mul_assoc, ← ch_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_ch]
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0 := sub_ne_zero.mpr h
    simp [this, h]

lemma Q_mul_P : Q * P = 1 := mul_eq_one_comm.1 P_mul_Q

lemma C14_mul_P : C14 * P = P * Matrix.diagonal lam := by
  ext i k
  have hne : (i - 1 : ZMod 14) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 14) = 0 := by linear_combination -h
    revert this
    decide
  have hL : (C14 * P) i k = ch ((i - 1) * k) + ch ((i + 1) * k) := by
    rw [Matrix.mul_apply]
    have : (∑ j : ZMod 14, C14 i j * P j k)
        = (C14.mulVec (fun j => P j k)) i := rfl
    rw [this, C14, SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (SimpleGraph.cycleGraph 14).neighborFinset i = {i - 1, i + 1} from
      SimpleGraph.cycleGraph_neighborFinset (n := 12)]
    rw [Finset.sum_pair hne]
    rfl
  have hR : (P * Matrix.diagonal lam) i k = ch (i * k) * lam k := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · simp [Matrix.diagonal_apply_eq, P]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hL, hR, lam, mul_add, ← ch_add, ← ch_add,
    show i * k + k = (i + 1) * k by ring, show i * k + -k = (i - 1) * k by ring]
  exact add_comm _ _

lemma lam_eq (k : ZMod 14) :
    lam k = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k.val : ℝ) / 14 with ht
  have hchk : ch k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ch, zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h2 : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show (t : ℂ) * Complex.I + -(t : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero]
  have hinv : ch (-k) = Complex.exp (-(t : ℂ) * Complex.I) := by
    have h1 : ch k * ch (-k) = 1 := ch_neg_mul_self k
    rw [hchk] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  rw [lam, hchk, hinv, ← Complex.two_cos, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

/-- **Hückel spectrum of `C₁₄`.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₄` are exactly the numbers `2 * cos (2 * π * k / 14)` for `k = 0, 1, …, 13`. -/
theorem huckel_C14 :
    {μ : ℂ | ∃ v : ZMod 14 → ℂ, v ≠ 0 ∧ C14.mulVec v = μ • v}
      = {μ : ℂ | ∃ k : ℕ, k < 14 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)} := by
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hAv⟩
    -- transport to the diagonal basis
    set w : ZMod 14 → ℂ := Q.mulVec v with hw
    have hPw : P.mulVec w = v := by
      rw [hw, Matrix.mulVec_mulVec, P_mul_Q, Matrix.one_mulVec]
    have hwne : w ≠ 0 := by
      intro h
      apply hv
      rw [← hPw, h, Matrix.mulVec_zero]
    have hDw : (Matrix.diagonal lam).mulVec w = μ • w := by
      have h1 : P.mulVec ((Matrix.diagonal lam).mulVec w) = P.mulVec (μ • w) := by
        rw [Matrix.mulVec_mulVec, ← C14_mul_P, ← Matrix.mulVec_mulVec, hPw, hAv,
          Matrix.mulVec_smul, hPw]
      have hinj : Function.Injective P.mulVec := by
        intro x y hxy
        have : Q.mulVec (P.mulVec x) = Q.mulVec (P.mulVec y) := by rw [hxy]
        rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Q_mul_P, Matrix.one_mulVec,
          Matrix.one_mulVec] at this
      exact hinj h1
    obtain ⟨k, hk⟩ : ∃ k : ZMod 14, w k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hwne (funext h)
    have : lam k * w k = μ * w k := by
      have := congrFun hDw k
      rwa [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    have hlam : lam k = μ := mul_right_cancel₀ hk this
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    rw [← hlam, lam_eq]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun j => P j (k : ZMod 14), ?_, ?_⟩
    · intro h
      have : P 0 (k : ZMod 14) = 0 := congrFun h 0
      rw [P] at this
      simp only [zero_mul] at this
      exact ch_ne_zero 0 (by simpa using this)
    · funext i
      have h1 : (C14.mulVec (fun j => P j (k : ZMod 14))) i = (C14 * P) i (k : ZMod 14) := rfl
      have h2 : (C14 * P) i (k : ZMod 14) = ch (i * k) * lam (k : ZMod 14) := by
        rw [C14_mul_P, Matrix.mul_apply, Finset.sum_eq_single (k : ZMod 14)]
        · simp [Matrix.diagonal_apply_eq, P]
        · intro b _ hb; simp [Matrix.diagonal_apply_ne _ hb]
        · intro h; exact absurd (Finset.mem_univ (k : ZMod 14)) h
      rw [h1, h2, lam_eq, ZMod.val_natCast_of_lt hk]
      simp [P, Pi.smul_apply, smul_eq_mul, mul_comm]

end Chem

