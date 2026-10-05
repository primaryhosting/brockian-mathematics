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

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

def flipAt {k : ℕ} (i : Fin k) (x : Fin k → Bool) : Fin k → Bool :=
  Function.update x i (!x i)

@[simp] lemma flipAt_apply_self {k : ℕ} (i : Fin k) (x : Fin k → Bool) :
    flipAt i x i = !x i := by
  simp [flipAt]

lemma flipAt_apply_of_ne {k : ℕ} {i j : Fin k} (h : j ≠ i) (x : Fin k → Bool) :
    flipAt i x j = x j := by
  simp [flipAt, Function.update_of_ne h]

@[simp] lemma flipAt_flipAt {k : ℕ} (i : Fin k) (x : Fin k → Bool) :
    flipAt i (flipAt i x) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [flipAt_apply_of_ne h]

lemma flipAt_ne_self {k : ℕ} (i : Fin k) (x : Fin k → Bool) : flipAt i x ≠ x := by
  intro h
  have := congrFun h i
  simp at this

lemma flipAt_left_injective {k : ℕ} (x : Fin k → Bool) :
    Function.Injective (fun i : Fin k => flipAt i x) := by
  intro i j h
  by_contra hij
  have h1 := congrFun h i
  simp only [flipAt_apply_self, flipAt_apply_of_ne hij] at h1
  simp at h1

/-- The `k`-dimensional hypercube graph `Q_k`: vertices are points of `Fin k → Bool`
and two vertices are adjacent when they differ in exactly one coordinate. -/

def hypercube (k : ℕ) : SimpleGraph (Fin k → Bool) where
  Adj x y := ∃ i, y = flipAt i x
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, (flipAt_flipAt i x).symm⟩
  loopless := ⟨by rintro x ⟨i, h⟩; exact flipAt_ne_self i x h.symm⟩

lemma hypercube_adj_iff {k : ℕ} (x y : Fin k → Bool) :
    (hypercube k).Adj x y ↔ ∃ i, y = flipAt i x := Iff.rfl

instance {k : ℕ} : DecidableRel (hypercube k).Adj := fun x y =>
  decidable_of_iff _ (hypercube_adj_iff x y).symm

lemma neighborFinset_hypercube {k : ℕ} (x : Fin k → Bool) :
    (hypercube k).neighborFinset x = Finset.image (fun i : Fin k => flipAt i x) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube_adj_iff, eq_comm]

lemma sum_over_neighbors {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ∑ y ∈ (hypercube k).neighborFinset x, f y = ∑ i : Fin k, f (flipAt i x) := by
  rw [neighborFinset_hypercube, Finset.sum_image (fun i _ j _ h => flipAt_left_injective x h)]

lemma sum_ite_adj {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ∑ y : Fin k → Bool, (if (hypercube k).Adj x y then f y else 0)
      = ∑ i : Fin k, f (flipAt i x) := by
  rw [← Finset.sum_filter]
  have h : Finset.univ.filter (fun y => (hypercube k).Adj x y)
      = (hypercube k).neighborFinset x := by
    ext y; simp [SimpleGraph.mem_neighborFinset]
  rw [h, sum_over_neighbors]

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/

lemma hypercube_degree {k : ℕ} (x : Fin k → Bool) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_hypercube,
    Finset.card_image_of_injective _ (flipAt_left_injective x)]
  simp

/-! ## The Dirichlet form -/

/-- The Dirichlet form of the hypercube, `∑ₓ ∑ᵢ (f x - f (flipAt i x))²`.
It equals twice the Laplacian quadratic form. -/

noncomputable def dirichlet (k : ℕ) (f : (Fin k → Bool) → ℝ) : ℝ :=
  ∑ x : Fin k → Bool, ∑ i : Fin k, (f x - f (flipAt i x)) ^ 2

lemma dotProduct_lapMatrix_hypercube {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) = dirichlet k f / 2 := by
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂', dirichlet]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_ite_adj (fun y => (f x - f y) ^ 2) x]

/-! ## Splitting the cube along the first coordinate -/

lemma sum_cube_succ {k : ℕ} (F : (Fin (k + 1) → Bool) → ℝ) :
    ∑ x : Fin (k + 1) → Bool, F x
      = (∑ y : Fin k → Bool, F (Fin.cons false y)) + ∑ y : Fin k → Bool, F (Fin.cons true y) := by
  have h1 : ∑ x : Fin (k + 1) → Bool, F x
      = ∑ p : Bool × (Fin k → Bool), F (Fin.cons p.1 p.2) :=
    (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ (by intro p; simp [Fin.consEquiv])).symm
  rw [h1, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

lemma flipAt_zero_cons {k : ℕ} (b : Bool) (y : Fin k → Bool) :
    flipAt 0 (Fin.cons b y) = Fin.cons (!b) y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp
  · intro i
    rw [flipAt_apply_of_ne (Fin.succ_ne_zero i)]
    simp

lemma flipAt_succ_cons {k : ℕ} (i : Fin k) (b : Bool) (y : Fin k → Bool) :
    flipAt i.succ (Fin.cons b y) = Fin.cons b (flipAt i y) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [flipAt_apply_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    simp
  · intro j
    by_cases h : j = i
    · subst h; simp
    · rw [flipAt_apply_of_ne (fun hc => h (Fin.succ_injective _ hc)), Fin.cons_succ,
        Fin.cons_succ, flipAt_apply_of_ne h]

lemma dirichlet_succ {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) :
    dirichlet (k + 1) f
      = dirichlet k (fun y => f (Fin.cons false y)) + dirichlet k (fun y => f (Fin.cons true y))
        + 2 * ∑ y : Fin k → Bool,
            (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
  have key : ∀ (b : Bool) (y : Fin k → Bool),
      (∑ i : Fin (k + 1), (f (Fin.cons b y) - f (flipAt i (Fin.cons b y))) ^ 2)
        = (f (Fin.cons b y) - f (Fin.cons (!b) y)) ^ 2
          + ∑ i : Fin k, (f (Fin.cons b y) - f (Fin.cons b (flipAt i y))) ^ 2 := by
    intro b y
    rw [Fin.sum_univ_succ, flipAt_zero_cons]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [flipAt_succ_cons]
  have hswap : ∑ y : Fin k → Bool, (f (Fin.cons true y) - f (Fin.cons false y)) ^ 2
      = ∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 :=
    Finset.sum_congr rfl fun y _ => by ring
  rw [dirichlet, sum_cube_succ (fun x => ∑ i : Fin (k + 1), (f x - f (flipAt i x)) ^ 2)]
  simp only [key, Bool.not_false, Bool.not_true]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hswap, dirichlet, dirichlet]
  ring

/-! ## The Poincaré inequality for the hypercube -/

lemma poincare (k : ℕ) (f : (Fin k → Bool) → ℝ) :
    4 * ((2 : ℝ) ^ k * ∑ x : Fin k → Bool, f x ^ 2 - (∑ x : Fin k → Bool, f x) ^ 2)
      ≤ (2 : ℝ) ^ k * dirichlet k f := by
  induction k with
  | zero => simp [dirichlet]
  | succ k ih =>
    have hg := ih (fun y => f (Fin.cons false y))
    have hh := ih (fun y => f (Fin.cons true y))
    have hsum : ∑ x : Fin (k + 1) → Bool, f x
        = (∑ y : Fin k → Bool, f (Fin.cons false y))
          + ∑ y : Fin k → Bool, f (Fin.cons true y) := sum_cube_succ f
    have hsq : ∑ x : Fin (k + 1) → Bool, f x ^ 2
        = (∑ y : Fin k → Bool, f (Fin.cons false y) ^ 2)
          + ∑ y : Fin k → Bool, f (Fin.cons true y) ^ 2 := sum_cube_succ (fun x => f x ^ 2)
    have hd := dirichlet_succ f
    have hcs : (∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y))) ^ 2
        ≤ (2 : ℝ) ^ k * ∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k → Bool)))
        (f := fun y => f (Fin.cons false y) - f (Fin.cons true y))
      simpa [Finset.card_univ] using this
    rw [Finset.sum_sub_distrib] at hcs
    have hexp : 4 * ((∑ y : Fin k → Bool, f (Fin.cons false y))
          + ∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2
        = 8 * (∑ y : Fin k → Bool, f (Fin.cons false y)) ^ 2
          + 8 * (∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2
          - 4 * ((∑ y : Fin k → Bool, f (Fin.cons false y))
              - ∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2 := by ring
    have hn : (0 : ℝ) < 2 ^ k := by positivity
    rw [hsum, hsq, hd, pow_succ]
    nlinarith [hg, hh, hcs, hn]

/-! ## The eigenvalue `2` is attained -/

lemma lapMatrix_mulVec_hypercube {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ((hypercube k).lapMatrix ℝ *ᵥ f) x = k * f x - ∑ i : Fin k, f (flipAt i x) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_over_neighbors, hypercube_degree]

/-- The parity function in the first coordinate is an eigenvector for the eigenvalue `2`. -/

lemma eigenvector_two {k : ℕ} (i0 : Fin k) :
    ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  refine ⟨fun x => if x i0 then (1 : ℝ) else -1, ?_, ?_⟩
  · intro hcon
    have hval := congrFun hcon (fun _ => true)
    simp at hval
  · funext x
    rw [lapMatrix_mulVec_hypercube]
    have hterm : ∀ i : Fin k,
        (if flipAt i x i0 then (1 : ℝ) else -1)
          = (if x i0 then (1 : ℝ) else -1)
            - (if i = i0 then 2 * (if x i0 then (1 : ℝ) else -1) else 0) := by
      intro i
      by_cases h : i = i0
      · subst h
        rw [flipAt_apply_self]
        cases hx : x i <;> simp <;> ring
      · rw [flipAt_apply_of_ne (Ne.symm h)]
        simp [h]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    ring

/-! ## Every nonzero eigenvalue is at least `2` -/

lemma sum_eq_zero_of_eigenvector {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) {v : (Fin k → Bool) → ℝ}
    (hv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) : ∑ x : Fin k → Bool, v x = 0 := by
  have hflip : ∀ i : Fin k, ∑ x : Fin k → Bool, v (flipAt i x) = ∑ x : Fin k → Bool, v x :=
    fun i => Fintype.sum_equiv (Function.Involutive.toPerm (flipAt i) (flipAt_flipAt i)) _ _
      (fun _ => rfl)
  have key : ∑ x : Fin k → Bool, ((hypercube k).lapMatrix ℝ *ᵥ v) x = 0 := by
    simp only [lapMatrix_mulVec_hypercube]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
    simp only [hflip, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hv] at key
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at key
  exact (mul_eq_zero.mp key).resolve_left hμ

lemma two_le_of_nonzero_eigenvalue {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) {v : (Fin k → Bool) → ℝ}
    (hv0 : v ≠ 0) (hv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) : 2 ≤ μ := by
  have hsum := sum_eq_zero_of_eigenvector hμ hv
  have hq : dirichlet k v / 2 = μ * ∑ x : Fin k → Bool, v x ^ 2 := by
    rw [← dotProduct_lapMatrix_hypercube, hv]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hpos : 0 < ∑ x : Fin k → Bool, v x ^ 2 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv0
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨x, Finset.mem_univ x, ?_⟩
    have : v x ≠ 0 := hx
    positivity
  have hp := poincare k v
  rw [hsum] at hp
  have hn : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [hp, hq, hpos, hn, mul_pos hn hpos]

/-- For every `k ≥ 1`, the smallest nonzero Laplacian eigenvalue of the hypercube `Q_k`
is exactly `2`. -/

theorem hypercube_isLeast_nonzero_eigenvalue (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} 2 := by
  constructor
  · obtain ⟨v, hv0, hv⟩ := eigenvector_two (⟨0, hk⟩ : Fin k)
    exact ⟨two_ne_zero, v, hv0, hv⟩
  · rintro μ ⟨hμ, v, hv0, hv⟩
    exact two_le_of_nonzero_eigenvalue hμ hv0 hv

/-- **Uniform spectral gap for the hypercube family.**
There is a constant `c > 0` (namely `c = 2`, independent of `k`) such that for every `k ≥ 1`
the smallest nonzero eigenvalue of the Laplacian of the hypercube graph `Q_k`
(on `2 ^ k` vertices) is exactly `c`. In particular the family `(Q_k)` of graphs
has a uniform spectral gap. -/

theorem expander_uniform_gap_witness :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} c :=
  ⟨2, two_pos, hypercube_isLeast_nonzero_eigenvalue⟩

end Frontier.Spectral
