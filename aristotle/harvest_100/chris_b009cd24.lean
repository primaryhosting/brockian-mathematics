/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1`, at `i`). -/
def basisVec {k : ℕ} (i : Fin k) : Cube k := fun j => if j = i then 1 else 0

lemma zmod_two_add_self (z : ZMod 2) : z + z = 0 := by revert z; decide

lemma cube_add_self {k : ℕ} (x : Cube k) : x + x = 0 := by
  funext j; exact zmod_two_add_self (x j)

lemma basisVec_apply_self {k : ℕ} (i : Fin k) : basisVec i i = 1 := by
  simp [basisVec]

lemma basisVec_ne_zero {k : ℕ} (i : Fin k) : basisVec i ≠ 0 := by
  intro h
  have := congrFun h i
  rw [basisVec_apply_self] at this
  exact one_ne_zero this

lemma basisVec_injective {k : ℕ} : Function.Injective (basisVec (k := k)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  rw [basisVec_apply_self] at this
  simp [basisVec, hij] at this

/-- The hypercube graph `Q k`: two binary strings are adjacent iff they differ in
exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i, y = x + basisVec i
  symm := by
    rintro x y ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    rw [add_assoc, cube_add_self, add_zero]
  loopless := ⟨by
    rintro x ⟨i, hi⟩
    have : basisVec i = 0 := by
      have := hi.symm
      simpa using add_left_cancel (a := x) (by simpa using this : x + basisVec i = x + 0)
    exact basisVec_ne_zero i this⟩

instance (k : ℕ) : DecidableRel (hypercube k).Adj := fun x y =>
  inferInstanceAs (Decidable (∃ i, y = x + basisVec i))

lemma hypercube_adj_iff {k : ℕ} (x y : Cube k) :
    (hypercube k).Adj x y ↔ ∃ i, y = x + basisVec i := Iff.rfl

lemma neighborFinset_hypercube {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.univ.image (fun i => x + basisVec i) := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube_adj_iff, eq_comm]

lemma shift_injective {k : ℕ} (x : Cube k) :
    Function.Injective (fun i : Fin k => x + basisVec i) := by
  intro i j h
  exact basisVec_injective (add_left_cancel h)

lemma degree_hypercube {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_hypercube,
    Finset.card_image_of_injective _ (shift_injective x), Finset.card_univ, Fintype.card_fin]

lemma sum_neighbors {k : ℕ} (x : Cube k) (v : Cube k → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, v u = ∑ i, v (x + basisVec i) := by
  rw [neighborFinset_hypercube, Finset.sum_image]
  intro i _ j _ h
  exact shift_injective x h

lemma lap_mulVec_apply {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ *ᵥ v) x = k * v x - ∑ i, v (x + basisVec i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_neighbors, degree_hypercube]

/-! ### Characters of the cube -/

/-- The sign character of `ZMod 2`. -/
def sgn (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;>
    simp [sgn, show (1 + 1 : ZMod 2) = 0 from rfl]

lemma sgn_zero : sgn 0 = 1 := rfl

/-- The Walsh character `chi S` of the cube, indexed by `S : Cube k`. -/
def chi {k : ℕ} (S x : Cube k) : ℝ := ∏ i, sgn (S i * x i)

lemma chi_add {k : ℕ} (S x y : Cube k) : chi S (x + y) = chi S x * chi S y := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [← sgn_add]
  congr 1
  simp [mul_add]

lemma chi_basisVec {k : ℕ} (S : Cube k) (i : Fin k) : chi S (basisVec i) = sgn (S i) := by
  unfold chi
  rw [Finset.prod_eq_single i]
  · rw [basisVec_apply_self, mul_one]
  · intro j _ hj
    simp [basisVec, hj, sgn_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma chi_shift {k : ℕ} (S x : Cube k) (i : Fin k) :
    chi S (x + basisVec i) = sgn (S i) * chi S x := by
  rw [chi_add, chi_basisVec, mul_comm]

/-- The Hamming weight of `S`, i.e. the number of coordinates where `S` is `1`. -/
def wt {k : ℕ} (S : Cube k) : ℕ := (Finset.univ.filter (fun i => S i ≠ 0)).card

lemma sum_sgn {k : ℕ} (S : Cube k) : ∑ i, sgn (S i) = (k : ℝ) - 2 * wt S := by
  classical
  have h1 : ∀ i, sgn (S i) = 1 - 2 * (if S i ≠ 0 then (1 : ℝ) else 0) := by
    intro i
    by_cases h : S i = 0
    · simp [sgn, h]
    · simp only [sgn, h, if_false, ne_eq, not_false_eq_true, if_true]
      norm_num
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [wt]

lemma lap_mulVec_chi {k : ℕ} (S : Cube k) :
    (hypercube k).lapMatrix ℝ *ᵥ chi S = (2 * wt S : ℝ) • chi S := by
  funext x
  rw [lap_mulVec_apply]
  have : ∑ i, chi S (x + basisVec i) = (∑ i, sgn (S i)) * chi S x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => chi_shift S x i
  rw [this, sum_sgn]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Fourier inversion -/

lemma chi_mul_chi {k : ℕ} (S x y : Cube k) : chi S x * chi S y = chi S (x + y) :=
  (chi_add S x y).symm

lemma sum_chi {k : ℕ} (z : Cube k) :
    ∑ S : Cube k, chi S z = if z = 0 then (2 : ℝ) ^ k else 0 := by
  classical
  have key : ∑ S : Cube k, chi S z = ∏ i, ∑ s : ZMod 2, sgn (s * z i) := by
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    rfl
  rw [key]
  by_cases hz : z = 0
  · subst hz
    simp [sgn_zero]
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have hzi : z i = 1 := by
      revert hi
      generalize z i = w
      revert w
      decide
    rw [hzi, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
    simp [sgn]

lemma fourier_inversion {k : ℕ} (v : Cube k → ℝ)
    (h : ∀ S : Cube k, ∑ x, chi S x * v x = 0) : v = 0 := by
  funext y
  have key : ∑ S : Cube k, chi S y * (∑ x, chi S x * v x) = 0 := by
    simp [h]
  have expand : ∑ S : Cube k, chi S y * (∑ x, chi S x * v x)
      = ∑ x : Cube k, (∑ S : Cube k, chi S (y + x)) * v x := by
    have step : ∀ S : Cube k, chi S y * (∑ x, chi S x * v x)
        = ∑ x : Cube k, chi S (y + x) * v x := by
      intro S
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, chi_mul_chi]
    simp_rw [step]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
  rw [expand] at key
  have : ∑ x : Cube k, (∑ S : Cube k, chi S (y + x)) * v x = (2 : ℝ) ^ k * v y := by
    rw [Finset.sum_eq_single y]
    · rw [sum_chi]
      simp [cube_add_self]
    · intro x _ hx
      rw [sum_chi, if_neg, zero_mul]
      intro hc
      exact hx (by
        have : y + x + x = 0 + x := by rw [hc]
        rw [add_assoc, cube_add_self, add_zero, zero_add] at this
        exact this.symm)
    · intro h; exact absurd (Finset.mem_univ y) h
  rw [this] at key
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have := mul_eq_zero.mp key
  rcases this with h' | h'
  · exact absurd h' h2
  · simpa using h'

/-! ### The adjoint relation -/

lemma sum_chi_mul_lap {k : ℕ} (S : Cube k) (v : Cube k → ℝ) :
    ∑ x, chi S x * ((hypercube k).lapMatrix ℝ *ᵥ v) x
      = (2 * wt S : ℝ) * ∑ x, chi S x * v x := by
  have step : ∀ i : Fin k, ∑ x : Cube k, chi S x * v (x + basisVec i)
      = sgn (S i) * ∑ x, chi S x * v x := by
    intro i
    have e : ∑ x : Cube k, chi S x * v (x + basisVec i)
        = ∑ y : Cube k, chi S (y + basisVec i) * v y := by
      refine Fintype.sum_equiv (Equiv.addRight (basisVec i)) _ _ ?_
      intro y
      simp only [Equiv.coe_addRight]
      congr 1
      rw [add_assoc, cube_add_self, add_zero]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [chi_shift]
    ring
  calc ∑ x, chi S x * ((hypercube k).lapMatrix ℝ *ᵥ v) x
      = ∑ x : Cube k, (k * (chi S x * v x) - ∑ i, chi S x * v (x + basisVec i)) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [lap_mulVec_apply, mul_sub, Finset.mul_sum]
        ring
    _ = (k : ℝ) * (∑ x, chi S x * v x) - ∑ i : Fin k, ∑ x : Cube k, chi S x * v (x + basisVec i) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_comm]
    _ = (k : ℝ) * (∑ x, chi S x * v x) - (∑ i, sgn (S i)) * ∑ x, chi S x * v x := by
        rw [Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => step i
    _ = (2 * wt S : ℝ) * ∑ x, chi S x * v x := by
        rw [sum_sgn]; ring

/-! ### Main results -/

lemma wt_basisVec {k : ℕ} (i : Fin k) : wt (basisVec i) = 1 := by
  classical
  unfold wt
  rw [show (Finset.univ.filter (fun j => basisVec i j ≠ 0)) = {i} by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hj
      exact h (by simp [basisVec, hj])
    · rintro rfl
      rw [basisVec_apply_self]
      exact one_ne_zero]
  simp

lemma chi_ne_zero_fun {k : ℕ} (S : Cube k) : chi S ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [Pi.zero_apply] at this
  have hpos : chi S (0 : Cube k) = 1 := by
    unfold chi
    simp [sgn_zero]
  rw [hpos] at this
  exact one_ne_zero this

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian matrix of the
hypercube graph `Q k` (on `2 ^ k` vertices) equals `2`.  In particular the family
`(Q k)` has a spectral gap of at least `2`, uniformly in `k`. -/
theorem expander_uniform_gap_witness (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | (∃ v : Cube k → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) ∧ μ ≠ 0} 2 := by
  have i0 : Fin k := ⟨0, hk⟩
  constructor
  · refine ⟨⟨chi (basisVec i0), chi_ne_zero_fun _, ?_⟩, two_ne_zero⟩
    rw [lap_mulVec_chi, wt_basisVec]
    norm_num
  · rintro μ ⟨⟨v, hv, hlap⟩, hμ⟩
    by_contra hlt
    push_neg at hlt
    apply hv
    refine fourier_inversion v ?_
    intro S
    have h1 : ∑ x, chi S x * ((hypercube k).lapMatrix ℝ *ᵥ v) x
        = μ * ∑ x, chi S x * v x := by
      rw [hlap, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [sum_chi_mul_lap] at h1
    have hne : (2 * wt S : ℝ) ≠ μ := by
      rcases Nat.eq_zero_or_pos (wt S) with h | h
      · rw [h]; simpa using (Ne.symm hμ)
      · have : (1 : ℝ) ≤ wt S := by exact_mod_cast h
        nlinarith
    have := sub_eq_zero.mpr h1
    have h2 : ((2 * wt S : ℝ) - μ) * ∑ x, chi S x * v x = 0 := by linarith [this]
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd (by linarith [sub_eq_zero.mp h'] : (2 * wt S : ℝ) = μ) hne
    · exact h'

/-- The hypercube `Q k` has `2 ^ k` vertices. -/
theorem card_cube (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp [Cube]

/-- The hypercube `Q k` is `k`-regular. -/
theorem hypercube_regular (k : ℕ) (x : Cube k) : (hypercube k).degree x = k :=
  degree_hypercube x

/-- **Uniform spectral gap**: every nonzero Laplacian eigenvalue of every hypercube
`Q k` with `k ≥ 1` is at least `2`, with the bound `2` independent of `k`. -/
theorem hypercube_uniform_gap (k : ℕ) (hk : 1 ≤ k) (μ : ℝ) (hμ : μ ≠ 0)
    (v : Cube k → ℝ) (hv : v ≠ 0) (hlap : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) :
    2 ≤ μ :=
  (expander_uniform_gap_witness k hk).2 ⟨⟨v, hv, hlap⟩, hμ⟩

end Frontier.Spectral

