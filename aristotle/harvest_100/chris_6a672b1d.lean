/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/
def cycleAdj (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0)

lemma cycleAdj_mulVec (n : ℕ) [NeZero n] (v : ZMod n → ℂ) (i : ZMod n) :
    (cycleAdj n).mulVec v i = v (i + 1) + v (i - 1) := by
  simp [cycleAdj, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

/-- A primitive `n`-th root of unity. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zeta_isPrimitiveRoot (n : ℕ) [NeZero n] : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zeta_pow_card (n : ℕ) [NeZero n] : zeta n ^ n = 1 :=
  (zeta_isPrimitiveRoot n).pow_eq_one

lemma zeta_pow_mod (n : ℕ) [NeZero n] (m : ℕ) : zeta n ^ (m % n) = zeta n ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, zeta_pow_card, one_pow, one_mul]

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

/-- The additive character `a ↦ ζ^a` of `ZMod n`. -/
noncomputable def chi (n : ℕ) [NeZero n] (a : ZMod n) : ℂ := zeta n ^ a.val

lemma chi_zero (n : ℕ) [NeZero n] : chi n 0 = 1 := by simp [chi]

lemma chi_add (n : ℕ) [NeZero n] (a b : ZMod n) : chi n (a + b) = chi n a * chi n b := by
  simp [chi, ZMod.val_add, zeta_pow_mod, pow_add]

lemma chi_ne_zero (n : ℕ) [NeZero n] (a : ZMod n) : chi n a ≠ 0 :=
  pow_ne_zero _ (zeta_ne_zero n)

lemma chi_neg (n : ℕ) [NeZero n] (a : ZMod n) : chi n (-a) = (chi n a)⁻¹ := by
  have h : chi n a * chi n (-a) = 1 := by rw [← chi_add]; simp [chi_zero]
  have ha := chi_ne_zero n a
  field_simp
  linear_combination h

lemma chi_mul (n : ℕ) [NeZero n] (a b : ZMod n) : chi n (a * b) = (chi n a) ^ b.val := by
  simp [chi, ZMod.val_mul, zeta_pow_mod, pow_mul]

lemma chi_eq_one_iff (n : ℕ) [NeZero n] (a : ZMod n) : chi n a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hd : n ∣ a.val := ((zeta_isPrimitiveRoot n).pow_eq_one_iff_dvd a.val).1 h
    have hv : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a)
    have hcast : ((a.val : ℕ) : ZMod n) = a := ZMod.natCast_rightInverse.leftInverse a
    rw [hv] at hcast
    simpa using hcast.symm
  · rintro rfl; exact chi_zero n

lemma sum_zmod_eq_sum_range (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    ∑ a : ZMod n, f a = ∑ m ∈ Finset.range n, f (m : ZMod n) := by
  refine Finset.sum_nbij' (fun a => ZMod.val a) (fun m => (m : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp [ZMod.val_lt]
  · intro m _; simp
  · intro a _; simp
  · intro m hm; simp only [Finset.mem_range] at hm; exact ZMod.val_cast_of_lt hm
  · intro a _; rw [ZMod.natCast_rightInverse.leftInverse]

/-- Orthogonality relation for the character `chi`. -/
lemma chi_orthogonality (n : ℕ) [NeZero n] (s : ZMod n) :
    ∑ t : ZMod n, chi n (t * s) = if s = 0 then (n : ℂ) else 0 := by
  have hcomm : ∀ t : ZMod n, chi n (t * s) = (chi n s) ^ t.val := by
    intro t; rw [mul_comm, chi_mul]
  simp only [hcomm]
  rw [sum_zmod_eq_sum_range]
  have hval : ∀ m ∈ Finset.range n, ((m : ZMod n)).val = m := by
    intro m hm; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hm)
  rw [Finset.sum_congr rfl (fun m hm => by rw [hval m hm])]
  by_cases hs : s = 0
  · subst hs; simp [chi_zero]
  · rw [if_neg hs]
    have hne : chi n s ≠ 1 := fun h => hs ((chi_eq_one_iff n s).1 h)
    have hpow : (chi n s) ^ n = 1 := by
      rw [chi, ← pow_mul, mul_comm, pow_mul, zeta_pow_card, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

lemma chi_add_chi_neg (n : ℕ) [NeZero n] (k : ZMod n) :
    chi n k + chi n (-k) = 2 * (Real.cos (2 * Real.pi * k.val / n) : ℂ) := by
  have hz : chi n k = Complex.exp (((2 * Real.pi * k.val / n : ℝ) : ℂ) * Complex.I) := by
    rw [chi, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [chi_neg, hz, Complex.ofReal_cos, Complex.two_cos, ← Complex.exp_neg]
  ring_nf

/-- **Hückel spectrum of the cycle `C n`.**  A complex number `lam` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph on `n` vertices if and only if it is of the form
`2 * cos (2 π k / n)` for some `k = 0, …, n - 1`. -/
theorem huckel_cycle_spectrum (n : ℕ) [NeZero n] (lam : ℂ) :
    (∃ v : ZMod n → ℂ, v ≠ 0 ∧ (cycleAdj n).mulVec v = lam • v) ↔
      ∃ k < n, lam = 2 * (Real.cos (2 * Real.pi * k / n) : ℂ) := by
  constructor
  · intro ⟨v, hv0, hv⟩
    by_contra hcon
    push_neg at hcon
    -- Fourier coefficients vanish
    have hcoef : ∀ t : ZMod n, ∑ j : ZMod n, v j * chi n (-(t * j)) = 0 := by
      intro t
      set c := ∑ j : ZMod n, v j * chi n (-(t * j)) with hc
      have key : lam * c = (chi n t + chi n (-t)) * c := by
        have h1 : lam * c = ∑ j : ZMod n, (v (j + 1) + v (j - 1)) * chi n (-(t * j)) := by
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have := congrFun hv j
          rw [cycleAdj_mulVec] at this
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [this]
          ring
        have h2 : ∑ j : ZMod n, v (j + 1) * chi n (-(t * j)) = chi n t * c := by
          have : ∀ j : ZMod n, v (j + 1) * chi n (-(t * j))
              = (fun j : ZMod n => v j * chi n (-(t * (j - 1)))) (j + 1) := by
            intro j; simp
          rw [Finset.sum_congr rfl (fun j _ => this j)]
          rw [Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
            (fun j => (fun j : ZMod n => v j * chi n (-(t * (j - 1)))) (j + 1))
            (fun j : ZMod n => v j * chi n (-(t * (j - 1)))) (fun j => rfl)]
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have : -(t * (j - 1)) = t + -(t * j) := by ring
          rw [this, chi_add]
          ring
        have h3 : ∑ j : ZMod n, v (j - 1) * chi n (-(t * j)) = chi n (-t) * c := by
          have : ∀ j : ZMod n, v (j - 1) * chi n (-(t * j))
              = (fun j : ZMod n => v j * chi n (-(t * (j + 1)))) (j - 1) := by
            intro j; simp
          rw [Finset.sum_congr rfl (fun j _ => this j)]
          rw [Fintype.sum_equiv (Equiv.subRight (1 : ZMod n))
            (fun j => (fun j : ZMod n => v j * chi n (-(t * (j + 1)))) (j - 1))
            (fun j : ZMod n => v j * chi n (-(t * (j + 1)))) (fun j => rfl)]
          rw [hc, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have : -(t * (j + 1)) = -t + -(t * j) := by ring
          rw [this, chi_add]
          ring
        rw [h1]
        simp only [add_mul]
        rw [Finset.sum_add_distrib, h2, h3]
      have hne : lam ≠ chi n t + chi n (-t) := by
        rw [chi_add_chi_neg]
        exact hcon t.val (ZMod.val_lt t)
      have := sub_eq_zero.2 key
      rw [← sub_mul] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · exact h
    -- Fourier inversion
    apply hv0
    funext j
    have hsum : (n : ℂ) * v j = 0 := by
      have expand : ∑ t : ZMod n, (∑ i : ZMod n, v i * chi n (-(t * i))) * chi n (t * j)
          = (n : ℂ) * v j := by
        have step1 : ∀ t : ZMod n, (∑ i : ZMod n, v i * chi n (-(t * i))) * chi n (t * j)
            = ∑ i : ZMod n, v i * chi n (t * (j - i)) := by
          intro t
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have : t * (j - i) = -(t * i) + t * j := by ring
          rw [this, chi_add]
          ring
        rw [Finset.sum_congr rfl (fun t _ => step1 t), Finset.sum_comm]
        have step2 : ∀ i : ZMod n, ∑ t : ZMod n, v i * chi n (t * (j - i))
            = v i * (if j - i = 0 then (n : ℂ) else 0) := by
          intro i; rw [← Finset.mul_sum, chi_orthogonality]
        rw [Finset.sum_congr rfl (fun i _ => step2 i)]
        rw [Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro i _ hij
          have : j - i ≠ 0 := sub_ne_zero.2 (Ne.symm hij)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [← expand]
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hcoef t, zero_mul]
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    simpa [hn] using hsum
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun a => chi n ((k : ZMod n) * a), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp only [mul_zero, chi_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    · funext i
      rw [cycleAdj_mulVec]
      have e1 : (k : ZMod n) * (i + 1) = (k : ZMod n) * i + (k : ZMod n) := by ring
      have e2 : (k : ZMod n) * (i - 1) = (k : ZMod n) * i + (-(k : ZMod n)) := by ring
      rw [e1, e2, chi_add, chi_add]
      have hval : ((k : ZMod n)).val = k := ZMod.val_cast_of_lt hk
      have := chi_add_chi_neg n (k : ZMod n)
      rw [hval] at this
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_add, this]
      ring

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

