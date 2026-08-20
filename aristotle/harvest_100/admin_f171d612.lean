/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/
lemma card_cube (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp

/-- The `i`-th standard basis bit string. -/
def bit {k : ℕ} (i : Fin k) : Cube k := Pi.single i 1

lemma bit_add_bit {k : ℕ} (i : Fin k) : bit i + bit i = (0 : Cube k) := by
  ext j
  simp [bit, CharTwo.add_self_eq_zero]

lemma bit_ne_zero {k : ℕ} (i : Fin k) : bit i ≠ (0 : Cube k) := by
  intro h
  have : (bit i) i = (0 : Cube k) i := by rw [h]
  simp [bit] at this

/-- The hypercube graph `Q_k`: two bit strings are adjacent iff they differ in
exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i : Fin k, y = x + bit i
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by rw [add_assoc, bit_add_bit, add_zero]⟩
  loopless := by
    constructor
    rintro x ⟨i, hi⟩
    exact bit_ne_zero i (by simpa using hi.symm)

instance (k : ℕ) : DecidableRel (hypercube k).Adj := fun x y =>
  inferInstanceAs (Decidable (∃ i : Fin k, y = x + bit i))

/-- The sign character `ZMod 2 → ℝ`. -/
def sgn : ZMod 2 → ℝ := fun t => if t = 0 then 1 else -1

/-- The Fourier character indexed by `y`, evaluated at `x`. -/
def chi {k : ℕ} (y x : Cube k) : ℝ := ∏ i : Fin k, sgn (y i * x i)

/-- The Laplacian eigenvalue attached to the character `chi y`, namely twice the
Hamming weight of `y`. -/
def eig {k : ℕ} (y : Cube k) : ℝ := (k : ℝ) - ∑ i : Fin k, sgn (y i)

lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  have hb : b = 0 ∨ b = 1 := by revert b; decide
  have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · norm_num [sgn]
  · norm_num [sgn]
  · norm_num [sgn]
  · rw [h11]; norm_num [sgn]

lemma bit_injective {k : ℕ} : Function.Injective (bit : Fin k → Cube k) := by
  intro i j h
  by_contra hij
  have h2 : (bit i) i = (bit j) i := by rw [h]
  simp [bit, Ne.symm hij] at h2

lemma neighborFinset_eq {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.image (fun i => x + bit i) Finset.univ := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

lemma degree_hypercube {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_eq,
    Finset.card_image_of_injective _ (fun i j h => bit_injective (by simpa using h))]
  simp

lemma lap_mulVec_apply {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ *ᵥ v) x = (k : ℝ) * v x - ∑ i : Fin k, v (x + bit i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, degree_hypercube, neighborFinset_eq,
    Finset.sum_image (by intro i _ j _ h; exact bit_injective (by simpa using h))]

lemma cube_add_eq_zero_iff {k : ℕ} (a b : Cube k) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext j
    have h2 := congrFun h j
    simp only [Pi.add_apply, Pi.zero_apply] at h2
    revert h2
    generalize a j = p
    generalize b j = q
    revert p q
    decide
  · rintro rfl
    funext j
    simpa using CharTwo.add_self_eq_zero (a j)

lemma chi_shift {k : ℕ} (y x : Cube k) (i : Fin k) :
    chi y (x + bit i) = sgn (y i) * chi y x := by
  have h1 : ∀ j : Fin k, sgn (y j * ((x + bit i) j)) = sgn (y j * x j) * sgn (y j * bit i j) := by
    intro j
    rw [← sgn_add]
    congr 1
    simp [mul_add]
  have h3 : ∏ j : Fin k, sgn (y j * bit i j) = sgn (y i) := by
    have h4 := Finset.prod_eq_single (f := fun j : Fin k => sgn (y j * bit i j))
      (s := Finset.univ) i
      (fun j _ hj => by simp only [bit, Pi.single_eq_of_ne hj, mul_zero, sgn_zero])
      (fun h => absurd (Finset.mem_univ i) h)
    rw [h4]
    simp only [bit, Pi.single_eq_same, mul_one]
  calc chi y (x + bit i) = ∏ j : Fin k, (sgn (y j * x j) * sgn (y j * bit i j)) :=
        Finset.prod_congr rfl (fun j _ => h1 j)
    _ = chi y x * ∏ j : Fin k, sgn (y j * bit i j) := by
        rw [Finset.prod_mul_distrib]; rfl
    _ = sgn (y i) * chi y x := by rw [h3, mul_comm]

lemma chi_add_left {k : ℕ} (a b y : Cube k) : chi (a + b) y = chi a y * chi b y := by
  rw [chi, chi, chi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← sgn_add]
  congr 1
  simp [add_mul]

lemma chi_symm {k : ℕ} (y x : Cube k) : chi y x = chi x y := by
  simp only [chi, mul_comm]

lemma chi_apply_zero {k : ℕ} (y : Cube k) : chi y 0 = 1 := by
  simp [chi, sgn]

lemma chi_ne_zero {k : ℕ} (y : Cube k) : chi y ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [chi_apply_zero] at this
  norm_num at this

lemma lap_mulVec_chi {k : ℕ} (y : Cube k) :
    (hypercube k).lapMatrix ℝ *ᵥ chi y = eig y • chi y := by
  funext x
  rw [lap_mulVec_apply, Pi.smul_apply, smul_eq_mul, eig]
  have : ∑ i : Fin k, chi y (x + bit i) = (∑ i : Fin k, sgn (y i)) * chi y x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => chi_shift y x i)
  rw [this, sub_mul]

lemma sum_sgn_mul (a : ZMod 2) : ∑ t : ZMod 2, sgn (a * t) = if a = 0 then 2 else 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  fin_cases a <;> norm_num [sgn]

lemma sum_chi {k : ℕ} (y : Cube k) :
    ∑ x : Cube k, chi y x = if y = 0 then (2 : ℝ) ^ k else 0 := by
  have h : ∑ x : Cube k, chi y x = ∏ i : Fin k, (if y i = 0 then (2 : ℝ) else 0) :=
    calc ∑ x : Cube k, chi y x = ∑ x : Cube k, ∏ i : Fin k, sgn (y i * x i) := rfl
      _ = ∏ i : Fin k, ∑ t : ZMod 2, sgn (y i * t) :=
          (Fintype.prod_sum (fun (i : Fin k) (t : ZMod 2) => sgn (y i * t))).symm
      _ = ∏ i : Fin k, (if y i = 0 then (2 : ℝ) else 0) :=
          Finset.prod_congr rfl (fun i _ => sum_sgn_mul (y i))
  rw [h]
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [if_neg hy]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hy (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Completeness of the character system: a vector orthogonal to every character is zero. -/
lemma exists_chi_dotProduct_ne_zero {k : ℕ} {v : Cube k → ℝ} (hv : v ≠ 0) :
    ∃ y : Cube k, (∑ x : Cube k, chi y x * v x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  refine hv (funext fun x₀ => ?_)
  have key : ∑ x : Cube k, v x * (if x = x₀ then (2 : ℝ) ^ k else 0) = 0 := by
    have h1 : ∀ x : Cube k, (∑ y : Cube k, chi y x₀ * chi y x)
        = if x = x₀ then (2 : ℝ) ^ k else 0 := by
      intro x
      have h2 : ∀ y : Cube k, chi y x₀ * chi y x = chi (x₀ + x) y := by
        intro y
        rw [chi_add_left, chi_symm x₀ y, chi_symm x y]
      rw [Finset.sum_congr rfl (fun y _ => h2 y), sum_chi]
      by_cases h : x = x₀
      · subst h
        rw [if_pos rfl, if_pos ((cube_add_eq_zero_iff x x).mpr rfl)]
      · rw [if_neg h, if_neg (fun hh => h ((cube_add_eq_zero_iff x₀ x).mp hh).symm)]
    calc ∑ x : Cube k, v x * (if x = x₀ then (2 : ℝ) ^ k else 0)
        = ∑ x : Cube k, ∑ y : Cube k, chi y x₀ * (chi y x * v x) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← h1 x, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by ring)
      _ = ∑ y : Cube k, chi y x₀ * ∑ x : Cube k, chi y x * v x := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => (Finset.mul_sum _ _ _).symm)
      _ = 0 := by
          refine Finset.sum_eq_zero (fun y _ => ?_)
          rw [hc y, mul_zero]
  rw [Finset.sum_eq_single x₀ (fun b _ hb => by rw [if_neg hb, mul_zero])
    (fun h => absurd (Finset.mem_univ x₀) h), if_pos rfl] at key
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  simpa [h2] using key

lemma sum_sgn_eq_of_ne {k : ℕ} {y : Cube k} {i₀ : Fin k} (hi₀ : y i₀ ≠ 0)
    (hrest : ∀ j, j ≠ i₀ → y j = 0) : ∑ i : Fin k, sgn (y i) = (k : ℝ) - 2 := by
  have hk : 1 ≤ k := i₀.pos
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have h1 : sgn (y i₀) = -1 := by rw [sgn, if_neg hi₀]
  have h2 : ∑ i ∈ Finset.univ.erase i₀, sgn (y i) = ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) :=
    Finset.sum_congr rfl (fun j hj => by
      rw [hrest j (Finset.mem_erase.mp hj).1, sgn, if_pos rfl])
  rw [h1, h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hk]
  push_cast
  ring

lemma eig_bit {k : ℕ} (i : Fin k) : eig (bit i) = 2 := by
  have h : ∑ j : Fin k, sgn (bit i j) = (k : ℝ) - 2 := by
    refine sum_sgn_eq_of_ne (i₀ := i) ?_ ?_
    · rw [bit, Pi.single_eq_same]; decide
    · intro j hj; rw [bit, Pi.single_eq_of_ne hj]
  rw [eig, h]
  ring

lemma two_le_eig {k : ℕ} {y : Cube k} (hy : y ≠ 0) : 2 ≤ eig y := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  have hk : 1 ≤ k := i₀.pos
  have hsum : ∑ i : Fin k, sgn (y i) ≤ (k : ℝ) - 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h1 : sgn (y i₀) = -1 := by rw [sgn, if_neg hi₀]
    have h2 : ∑ i ∈ Finset.univ.erase i₀, sgn (y i) ≤ ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => by rw [sgn]; split <;> norm_num)
    have h3 : ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) = (k : ℝ) - 1 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub hk]
      push_cast
      ring
    rw [h1]
    linarith [h2, h3.le, h3.ge]
  rw [eig]
  linarith

lemma eig_eq_zero_iff {k : ℕ} (y : Cube k) : eig y = 0 ↔ y = 0 := by
  constructor
  · intro h
    by_contra hy
    have := two_le_eig hy
    rw [h] at this
    norm_num at this
  · rintro rfl
    simp [eig, sgn]

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the Laplacian of the hypercube graph `Q_k` on `2 ^ k` vertices has
`2` as an eigenvalue, and every nonzero eigenvalue is at least `2`; i.e. the smallest
nonzero Laplacian eigenvalue of `Q_k` equals `2`, uniformly in `k`. -/
theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k →
      (∃ v : Cube k → ℝ, v ≠ 0 ∧
          (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v) ∧
      (∀ (μ : ℝ) (v : Cube k → ℝ), v ≠ 0 →
          (hypercube k).lapMatrix ℝ *ᵥ v = μ • v → μ ≠ 0 → 2 ≤ μ) := by
  intro k hk
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨⟨chi (bit ⟨0, hk0⟩), chi_ne_zero _, ?_⟩, ?_⟩
  · rw [lap_mulVec_chi, eig_bit]
  · intro μ v hv hlap hμ
    obtain ⟨y, hy⟩ := exists_chi_dotProduct_ne_zero hv
    have hsymm : ((hypercube k).lapMatrix ℝ).IsSymm := SimpleGraph.isSymm_lapMatrix _
    have key : chi y ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ v)
        = ((hypercube k).lapMatrix ℝ *ᵥ chi y) ⬝ᵥ v := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm]
    rw [hlap, lap_mulVec_chi] at key
    have hL : chi y ⬝ᵥ (μ • v) = μ * (chi y ⬝ᵥ v) := by
      rw [dotProduct_smul, smul_eq_mul]
    have hR : (eig y • chi y) ⬝ᵥ v = eig y * (chi y ⬝ᵥ v) := by
      rw [smul_dotProduct, smul_eq_mul]
    rw [hL, hR] at key
    have hd : chi y ⬝ᵥ v ≠ 0 := hy
    have hμeq : μ = eig y := mul_right_cancel₀ hd key
    have hy0 : y ≠ 0 := fun h => hμ (hμeq.trans ((eig_eq_zero_iff y).mpr h))
    rw [hμeq]
    exact two_le_eig hy0

end Frontier.Spectral

#print axioms Frontier.Spectral.expander_uniform_gap_witness

