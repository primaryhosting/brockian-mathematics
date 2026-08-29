/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/
noncomputable def C8adj : Matrix (ZMod 8) (ZMod 8) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The same adjacency matrix with integer entries (used for a decidable computation). -/
def C8adjInt : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma C8adj_eq_map : C8adj = ((Int.castRingHom ℂ).mapMatrix C8adjInt) := by
  ext i j
  simp only [C8adj, C8adjInt, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  split <;> simp

/-- The adjacency matrix of `C₈` satisfies `A⁵ = 6A³ - 8A`, i.e. it is annihilated by
the polynomial `x(x² - 2)(x² - 4)`. -/
lemma C8adj_pow_five : C8adj ^ 5 = 6 * C8adj ^ 3 - 8 * C8adj := by
  have h : C8adjInt ^ 5 = 6 * C8adjInt ^ 3 - 8 * C8adjInt := by decide
  rw [C8adj_eq_map, ← map_pow, ← map_pow, h, map_sub, map_mul, map_mul, map_ofNat, map_ofNat]

lemma succ_ne_pred (j : ZMod 8) : j + 1 ≠ j - 1 := by
  intro h
  have h2 : (2 : ZMod 8) = 0 := by linear_combination h
  exact absurd h2 (by decide)

/-- Applying the adjacency matrix of `C₈` to a vector sums the two neighbouring values. -/
lemma C8adj_mulVec (v : ZMod 8 → ℂ) (j : ZMod 8) :
    C8adj.mulVec v j = v (j + 1) + v (j - 1) := by
  have hrw : ∀ i : ZMod 8, (if i = j + 1 ∨ i = j - 1 then (1 : ℂ) else 0) * v i
      = if i ∈ ({j + 1, j - 1} : Finset (ZMod 8)) then v i else 0 := by
    intro i
    by_cases h : i = j + 1 ∨ i = j - 1 <;> simp [h, Finset.mem_insert]
  simp only [Matrix.mulVec, dotProduct, C8adj, hrw]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair (succ_ne_pred j)]

/-- A primitive 8th root of unity. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

lemma zeta8_pow_eight : zeta8 ^ 8 = 1 := by
  rw [zeta8, ← Complex.exp_nat_mul]
  have h : (8 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 8) = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.exp_two_pi_mul_I

lemma zeta8_pow_mod (m : ℕ) : zeta8 ^ (m % 8) = zeta8 ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

/-- The additive character `x ↦ ζ₈ˣ` on `ZMod 8`. -/
noncomputable def om (x : ZMod 8) : ℂ := zeta8 ^ x.val

lemma om_add (a b : ZMod 8) : om (a + b) = om a * om b := by
  simp only [om, ZMod.val_add, zeta8_pow_mod, pow_add]

lemma om_zero : om 0 = 1 := by simp [om]

lemma om_eq_exp (x : ZMod 8) :
    om x = Complex.exp ((((2 * Real.pi * (x.val : ℝ) / 8 : ℝ)) : ℂ) * Complex.I) := by
  rw [om, zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The character values combine into the Hückel eigenvalue `2 cos (2πk/8)`. -/
lemma om_add_om_neg (k : ZMod 8) :
    om k + om (-k) = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 8) : ℝ) : ℂ) := by
  have hk : om k * om (-k) = 1 := by rw [← om_add, add_neg_cancel, om_zero]
  have h1 : om k ≠ 0 := by
    intro h; rw [h, zero_mul] at hk; exact zero_ne_one hk
  have h2 : om (-k) = (om k)⁻¹ := by
    field_simp
    linear_combination hk
  rw [h2, om_eq_exp, ← Complex.exp_neg]
  set t : ℝ := 2 * Real.pi * (k.val : ℝ) / 8
  have h3 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h3, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Every Hückel eigenvalue `2 cos (2πk/8)` of `C₈` is realized by an explicit eigenvector. -/
lemma huckel_C8_eigenvector (k : ℕ) (hk : k < 8) :
    C8adj.mulVec (fun j => om ((k : ZMod 8) * j))
      = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) : ℝ) : ℂ) • fun j => om ((k : ZMod 8) * j) := by
  have hval : ((k : ZMod 8)).val = k := ZMod.val_natCast_of_lt hk
  have hlam : ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) : ℝ) : ℂ)
      = om (k : ZMod 8) + om (-(k : ZMod 8)) := by
    rw [om_add_om_neg, hval]
  funext j
  rw [C8adj_mulVec]
  have e1 : (k : ZMod 8) * (j + 1) = (k : ZMod 8) * j + (k : ZMod 8) := by ring
  have e2 : (k : ZMod 8) * (j - 1) = (k : ZMod 8) * j + (-(k : ZMod 8)) := by ring
  simp only [e1, e2, om_add, Pi.smul_apply, smul_eq_mul, hlam]
  ring

/-- Any eigenvalue of the adjacency matrix of `C₈` is a root of `x(x² - 2)(x² - 4)`. -/
lemma huckel_C8_root (μ : ℂ) (v : ZMod 8 → ℂ) (hv0 : v ≠ 0) (hv : C8adj.mulVec v = μ • v) :
    μ * (μ ^ 2 - 2) * (μ ^ 2 - 4) = 0 := by
  have hpow : ∀ n : ℕ, (C8adj ^ n).mulVec v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm (μ ^ n) μ]
  have e6 : ((6 : Matrix (ZMod 8) (ZMod 8) ℂ) * C8adj ^ 3).mulVec v
      = (6 : ℂ) • (C8adj ^ 3).mulVec v := by
    rw [← Matrix.mulVec_mulVec]; simp
  have e8 : ((8 : Matrix (ZMod 8) (ZMod 8) ℂ) * C8adj).mulVec v = (8 : ℂ) • C8adj.mulVec v := by
    rw [← Matrix.mulVec_mulVec]; simp
  have hmain : μ ^ 5 • v = (6 : ℂ) • (μ ^ 3 • v) - (8 : ℂ) • (μ • v) := by
    have := congrArg (fun M : Matrix (ZMod 8) (ZMod 8) ℂ => M.mulVec v) C8adj_pow_five
    simp only [Matrix.sub_mulVec, e6, e8, hpow, hv] at this
    simpa using this
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  have hj' := congrFun hmain j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hj'
  have : (μ * (μ ^ 2 - 2) * (μ ^ 2 - 4)) * v j = 0 := by linear_combination hj'
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hj

/-- **Hückel theory for the cyclic polyene C₈.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₈` (i.e. it admits a nonzero eigenvector) if and only if
`μ = 2 cos (2πk/8)` for some `k ∈ {0, …, 7}`. -/
theorem huckel_C8 (μ : ℂ) :
    (∃ v : ZMod 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 8 ∧ μ = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hroot := huckel_C8_root μ v hv0 hv
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    rcases mul_eq_zero.mp hroot with h | h4
    · rcases mul_eq_zero.mp h with h0 | h2
      · -- μ = 0, k = 2
        refine ⟨2, by norm_num, ?_⟩
        rw [h0]
        have : (2 * Real.pi * ((2 : ℕ) : ℝ) / 8 : ℝ) = Real.pi / 2 := by push_cast; ring
        rw [this, Real.cos_pi_div_two]
        norm_num
      · -- μ² = 2
        have : (μ - ((Real.sqrt 2 : ℝ) : ℂ)) * (μ + ((Real.sqrt 2 : ℝ) : ℂ)) = 0 := by
          linear_combination h2 - hs2
        rcases mul_eq_zero.mp this with hp | hm
        · refine ⟨1, by norm_num, ?_⟩
          have hμ : μ = ((Real.sqrt 2 : ℝ) : ℂ) := by linear_combination hp
          rw [hμ]
          norm_cast
          have hpi : (2 * Real.pi * 1 / 8 : ℝ) = Real.pi / 4 := by ring
          rw [hpi, Real.cos_pi_div_four]
          ring
        · refine ⟨3, by norm_num, ?_⟩
          have hμ : μ = -((Real.sqrt 2 : ℝ) : ℂ) := by linear_combination hm
          rw [hμ]
          norm_cast
          have hpi : (2 * Real.pi * 3 / 8 : ℝ) = Real.pi - Real.pi / 4 := by ring
          rw [hpi, Real.cos_pi_sub, Real.cos_pi_div_four]
          ring
    · -- μ² = 4
      have : (μ - 2) * (μ + 2) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with hp | hm
      · refine ⟨0, by norm_num, ?_⟩
        have hμ : μ = 2 := by linear_combination hp
        rw [hμ]
        norm_num
      · refine ⟨4, by norm_num, ?_⟩
        have hμ : μ = -2 := by linear_combination hm
        rw [hμ]
        have : (2 * Real.pi * ((4 : ℕ) : ℝ) / 8 : ℝ) = Real.pi := by push_cast; ring
        rw [this, Real.cos_pi]
        norm_num
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun j => om ((k : ZMod 8) * j), ?_, huckel_C8_eigenvector k hk⟩
    intro h
    have h0 := congrFun h 0
    simp [om_zero] at h0

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

