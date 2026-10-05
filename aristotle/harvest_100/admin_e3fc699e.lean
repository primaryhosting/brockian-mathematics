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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → Bool

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/
def cflip {k : ℕ} (x : Cube k) (i : Fin k) : Cube k := Function.update x i (!x i)

@[simp] lemma cflip_self {k : ℕ} (x : Cube k) (i : Fin k) : cflip x i i = !x i := by
  simp [cflip]

lemma cflip_of_ne {k : ℕ} (x : Cube k) {i j : Fin k} (h : j ≠ i) : cflip x i j = x j := by
  simp [cflip, Function.update_of_ne h]

@[simp] lemma cflip_cflip {k : ℕ} (x : Cube k) (i : Fin k) : cflip (cflip x i) i = x := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [cflip_of_ne _ h]

/-- The `k`-dimensional hypercube graph `Q k`: two bit strings are adjacent iff they
differ in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃! i : Fin k, x i ≠ y i
  symm := by
    rintro x y ⟨i, hi, hu⟩
    exact ⟨i, fun h => hi h.symm, fun j hj => hu j fun h => hj h.symm⟩
  loopless := ⟨by rintro x ⟨i, hi, -⟩; exact hi rfl⟩

lemma hypercube_adj_iff {k : ℕ} (x y : Cube k) :
    (hypercube k).Adj x y ↔ ∃ i, y = cflip x i := by
  constructor
  · rintro ⟨i, hi, hu⟩
    refine ⟨i, funext fun j => ?_⟩
    rcases eq_or_ne j i with rfl | h
    · simp only [cflip_self]
      cases hx : x j <;> cases hy : y j <;> simp_all
    · have : ¬ (x j ≠ y j) := fun hxy => h (hu j hxy)
      simp [cflip_of_ne x h, not_not.mp this]
  · rintro ⟨i, rfl⟩
    refine ⟨i, by simp, fun j hj => ?_⟩
    by_contra h
    exact hj (by rw [cflip_of_ne x h])

instance {k : ℕ} : DecidableRel (hypercube k).Adj := fun x y =>
  decidable_of_iff _ (hypercube_adj_iff x y).symm

/-- The neighbours of `x` are exactly the `cflip x i`. -/
lemma neighborFinset_eq_image {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.image (cflip x) Finset.univ := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
  rw [hypercube_adj_iff]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩

lemma cflip_injective {k : ℕ} (x : Cube k) : Function.Injective (cflip x) := by
  intro i j h
  by_contra hij
  have h1 : cflip x i i = cflip x j i := by rw [h]
  rw [cflip_self, cflip_of_ne x hij] at h1
  simp at h1

lemma sum_over_neighbors {k : ℕ} (x : Cube k) (v : Cube k → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, v u = ∑ i : Fin k, v (cflip x i) := by
  rw [neighborFinset_eq_image, Finset.sum_image]
  intro i _ j _ h
  exact cflip_injective x h

lemma hypercube_degree {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_eq_image,
    Finset.card_image_of_injective _ (cflip_injective x)]
  simp

/-- Explicit formula for the action of the Laplacian of the hypercube on a vector. -/
lemma lap_mulVec_apply {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ).mulVec v x = k * v x - ∑ i : Fin k, v (cflip x i) := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec]
  simp only [Pi.sub_apply, SimpleGraph.adjMatrix_mulVec_apply, sum_over_neighbors]
  congr 1
  rw [SimpleGraph.degMatrix, Matrix.mulVec_diagonal, hypercube_degree]

/-- The `cflip` map along a fixed coordinate is a bijection of the cube. -/
lemma sum_cflip {k : ℕ} (i : Fin k) (F : Cube k → ℝ) :
    ∑ x : Cube k, F (cflip x i) = ∑ x : Cube k, F x :=
  Fintype.sum_bijective (fun x => cflip x i)
    (Function.bijective_iff_has_inverse.mpr ⟨fun x => cflip x i, fun x => by simp, fun x => by simp⟩)
    _ _ (fun _ => rfl)

/-- The Dirichlet energy (twice the Laplacian quadratic form) of the hypercube. -/
noncomputable def energy (k : ℕ) (f : Cube k → ℝ) : ℝ :=
  ∑ x : Cube k, ∑ i : Fin k, (f x - f (cflip x i)) ^ 2

/-- The Laplacian quadratic form equals half the Dirichlet energy. -/
lemma sum_sq_cflip (k : ℕ) (v : Cube k → ℝ) :
    ∑ x : Cube k, ∑ i : Fin k, (v (cflip x i)) ^ 2 = k * ∑ x : Cube k, (v x) ^ 2 := by
  rw [Finset.sum_comm]
  have : ∀ i : Fin k, ∑ x : Cube k, (v (cflip x i)) ^ 2 = ∑ x : Cube k, (v x) ^ 2 :=
    fun i => sum_cflip i (fun x => (v x) ^ 2)
  simp [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma quadratic_form_eq (k : ℕ) (v : Cube k → ℝ) :
    ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec v x = energy k v / 2 := by
  have hexp : ∀ x : Cube k, ∑ i : Fin k, (v x - v (cflip x i)) ^ 2
      = k * (v x) ^ 2 - 2 * (v x * ∑ i : Fin k, v (cflip x i))
        + ∑ i : Fin k, (v (cflip x i)) ^ 2 := by
    intro x
    rw [Finset.sum_congr rfl fun (i : Fin k) _ =>
      (by ring : (v x - v (cflip x i)) ^ 2
        = (v x) ^ 2 - 2 * (v x * v (cflip x i)) + (v (cflip x i)) ^ 2)]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hL : ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec v x
      = k * (∑ x : Cube k, (v x) ^ 2) - ∑ x : Cube k, v x * ∑ i : Fin k, v (cflip x i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [lap_mulVec_apply]; ring
  have henergy : energy k v
      = 2 * (k * (∑ x : Cube k, (v x) ^ 2))
        - 2 * ∑ x : Cube k, v x * ∑ i : Fin k, v (cflip x i) := by
    unfold energy
    rw [Finset.sum_congr rfl fun x _ => hexp x]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_sq_cflip, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  rw [hL, henergy]
  ring

/-- Every column of the Laplacian sums to zero. -/
lemma sum_lap_mulVec (k : ℕ) (v : Cube k → ℝ) :
    ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x = 0 := by
  have h1 : ∑ x : Cube k, ∑ i : Fin k, v (cflip x i) = k * ∑ x : Cube k, v x := by
    rw [Finset.sum_comm]
    have : ∀ i : Fin k, ∑ x : Cube k, v (cflip x i) = ∑ x : Cube k, v x :=
      fun i => sum_cflip i v
    simp [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x
      = k * (∑ x : Cube k, v x) - ∑ x : Cube k, ∑ i : Fin k, v (cflip x i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [lap_mulVec_apply]
  rw [h2, h1]
  ring

/-- Splitting the cube `Cube (k+1)` along the first coordinate. -/
def consEquiv (k : ℕ) : Cube k × Bool ≃ Cube (k + 1) where
  toFun p := Fin.cons p.2 p.1
  invFun x := (Fin.tail x, x 0)
  left_inv := by rintro ⟨y, b⟩; simp [Fin.tail_cons]
  right_inv := by intro x; simp [Fin.cons_self_tail]

lemma sum_cube_succ (k : ℕ) (F : Cube (k + 1) → ℝ) :
    ∑ x : Cube (k + 1), F x
      = ∑ y : Cube k, (F (Fin.cons false y) + F (Fin.cons true y)) := by
  rw [← Equiv.sum_comp (consEquiv k) F, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun y _ => by
    rw [Fintype.sum_bool]
    exact add_comm _ _

lemma cflip_cons_zero {k : ℕ} (b : Bool) (y : Cube k) :
    cflip (Fin.cons b y) 0 = Fin.cons (!b) y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [cflip]
  · intro i
    rw [cflip_of_ne _ (Fin.succ_ne_zero i)]
    simp

lemma cflip_cons_succ {k : ℕ} (b : Bool) (y : Cube k) (i : Fin k) :
    cflip (Fin.cons b y) i.succ = Fin.cons b (cflip y i) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [cflip_of_ne _ (Fin.succ_ne_zero i).symm]
    simp
  · intro j'
    rcases eq_or_ne j' i with rfl | hne
    · rw [cflip_self]
      simp
    · rw [cflip_of_ne _ (fun hc => hne (Fin.succ_injective _ hc))]
      simp [cflip_of_ne y hne]

/-- The Dirichlet energy of the `(k+1)`-cube splits along the first coordinate. -/
lemma energy_succ (k : ℕ) (f : Cube (k + 1) → ℝ) :
    energy (k + 1) f
      = energy k (fun y => f (Fin.cons false y)) + energy k (fun y => f (Fin.cons true y))
        + 2 * ∑ y : Cube k, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
  have key : ∀ (b : Bool) (y : Cube k),
      ∑ i : Fin (k + 1), (f (Fin.cons b y) - f (cflip (Fin.cons b y) i)) ^ 2
        = (f (Fin.cons b y) - f (Fin.cons (!b) y)) ^ 2
          + ∑ i : Fin k, (f (Fin.cons b y) - f (Fin.cons b (cflip y i))) ^ 2 := by
    intro b y
    rw [Fin.sum_univ_succ, cflip_cons_zero]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [cflip_cons_succ])
  unfold energy
  rw [sum_cube_succ]
  simp only [key, Bool.not_false, Bool.not_true]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

lemma card_cube (k : ℕ) : (Finset.univ : Finset (Cube k)).card = 2 ^ k := by
  simp [Finset.card_univ]

/-- Poincaré inequality on the hypercube (the spectral gap in quadratic-form shape). -/
lemma poincare (k : ℕ) (f : Cube k → ℝ) :
    4 * ((2 ^ k : ℝ) * (∑ x : Cube k, (f x) ^ 2) - (∑ x : Cube k, f x) ^ 2)
      ≤ (2 ^ k : ℝ) * energy k f := by
  induction k with
  | zero => simp [energy]
  | succ k ih =>
    set g : Cube k → ℝ := fun y => f (Fin.cons false y) with hgdef
    set h : Cube k → ℝ := fun y => f (Fin.cons true y) with hhdef
    have hsq : ∑ x : Cube (k + 1), (f x) ^ 2
        = (∑ y : Cube k, (g y) ^ 2) + ∑ y : Cube k, (h y) ^ 2 := by
      rw [sum_cube_succ (F := fun x => (f x) ^ 2), Finset.sum_add_distrib]
    have hlin : ∑ x : Cube (k + 1), f x = (∑ y : Cube k, g y) + ∑ y : Cube k, h y := by
      rw [sum_cube_succ (F := f), Finset.sum_add_distrib]
    have hCS : (∑ y : Cube k, (g y - h y)) ^ 2
        ≤ (2 ^ k : ℝ) * ∑ y : Cube k, (g y - h y) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Cube k)))
        (f := fun y => g y - h y)
      rwa [card_cube k, Nat.cast_pow, Nat.cast_ofNat] at this
    have hCS' : (∑ y : Cube k, g y - ∑ y : Cube k, h y) ^ 2
        ≤ (2 ^ k : ℝ) * ∑ y : Cube k, (g y - h y) ^ 2 := by
      rwa [Finset.sum_sub_distrib] at hCS
    have hexp : ∑ y : Cube k, (g y - h y) ^ 2
        = ∑ y : Cube k, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := rfl
    have hA := ih g
    have hB := ih h
    rw [hsq, hlin, energy_succ k f, ← hgdef, ← hhdef, ← hexp, pow_succ]
    nlinarith [hA, hB, hCS', pow_pos (show (0:ℝ) < 2 by norm_num) k]

/-- The set of eigenvalues of the Laplacian of the hypercube `Q k`. -/
noncomputable def lapSpectrum (k : ℕ) : Set ℝ :=
  {μ : ℝ | ∃ v : Cube k → ℝ, v ≠ 0 ∧ ((hypercube k).lapMatrix ℝ).mulVec v = μ • v}

/-- The eigenvector `(-1)^(x 0)` witnessing the eigenvalue `2`. -/
noncomputable def gapVector (k : ℕ) (hk : 1 ≤ k) : Cube k → ℝ :=
  fun x => if x ⟨0, hk⟩ then -1 else 1

lemma gapVector_ne_zero (k : ℕ) (hk : 1 ≤ k) : gapVector k hk ≠ 0 := by
  intro h
  have := congrFun h (fun _ => false)
  simp [gapVector] at this

lemma lap_mulVec_gapVector (k : ℕ) (hk : 1 ≤ k) :
    ((hypercube k).lapMatrix ℝ).mulVec (gapVector k hk) = (2 : ℝ) • gapVector k hk := by
  funext x
  have hstep : ∀ i : Fin k, gapVector k hk (cflip x i)
      = gapVector k hk x + (if i = (⟨0, hk⟩ : Fin k) then -(2 * gapVector k hk x) else 0) := by
    intro i
    by_cases h : i = (⟨0, hk⟩ : Fin k)
    · subst h
      rw [if_pos rfl]
      simp only [gapVector, cflip_self]
      cases hx : x (⟨0, hk⟩ : Fin k) <;> norm_num [hx]
    · rw [if_neg h]
      have hc : cflip x i (⟨0, hk⟩ : Fin k) = x (⟨0, hk⟩ : Fin k) := cflip_of_ne x (Ne.symm h)
      simp only [gapVector, hc]
      ring
  have hsum : ∑ i : Fin k, gapVector k hk (cflip x i)
      = k * gapVector k hk x - 2 * gapVector k hk x := by
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (⟨0, hk⟩ : Fin k) (fun _ => -(2 * gapVector k hk x))]
    simp only [Finset.mem_univ, if_pos, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [lap_mulVec_apply, hsum]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` (on `2 ^ k` vertices) is exactly `2`; in particular the bound `2` is independent of `k`. -/
theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k → IsLeast {μ : ℝ | μ ≠ 0 ∧ μ ∈ lapSpectrum k} 2 := by
  intro k hk
  constructor
  · exact ⟨two_ne_zero, gapVector k hk, gapVector_ne_zero k hk, lap_mulVec_gapVector k hk⟩
  · rintro μ ⟨hμ0, v, hv, hLv⟩
    have hsum0 : ∑ x : Cube k, v x = 0 := by
      have h := sum_lap_mulVec k v
      rw [hLv] at h
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
      exact (mul_eq_zero.mp h).resolve_left hμ0
    have hq : energy k v = 2 * (μ * ∑ x : Cube k, (v x) ^ 2) := by
      have h := quadratic_form_eq k v
      rw [hLv] at h
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [show ∑ x : Cube k, v x * (μ * v x) = μ * ∑ x : Cube k, (v x) ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring] at h
      linarith
    have hpos : 0 < ∑ x : Cube k, (v x) ^ 2 := by
      obtain ⟨x0, hx0⟩ : ∃ x, v x ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (funext fun x => h x)
      refine Finset.sum_pos' (fun x _ => sq_nonneg (v x)) ⟨x0, Finset.mem_univ x0, ?_⟩
      positivity
    have hp := poincare k v
    rw [hsum0, hq] at hp
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith [mul_pos h2k hpos]

/-- **Uniform spectral gap, explicit form.** Every nonzero Laplacian eigenvalue of every
hypercube `Q k` with `k ≥ 1` is at least `2`, a bound independent of `k`, and the bound is
attained for each `k`. -/
theorem hypercube_uniform_gap (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ∈ lapSpectrum k ∧ ∀ μ ∈ lapSpectrum k, μ ≠ 0 → 2 ≤ μ := by
  obtain ⟨⟨-, hmem⟩, hlb⟩ := expander_uniform_gap_witness k hk
  exact ⟨hmem, fun μ hμ hμ0 => hlb ⟨hμ0, hμ⟩⟩

end Frontier.Spectral

