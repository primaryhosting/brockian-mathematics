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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

variable {k : ℕ}

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `(ZMod 2)^k`. -/
def flipAt (x : Fin k → ZMod 2) (i : Fin k) : Fin k → ZMod 2 :=
  Function.update x i (x i + 1)

@[simp] lemma flipAt_self (x : Fin k → ZMod 2) (i : Fin k) :
    flipAt x i i = x i + 1 := by
  simp [flipAt]

lemma flipAt_of_ne (x : Fin k → ZMod 2) {i j : Fin k} (h : j ≠ i) :
    flipAt x i j = x j := by
  simp [flipAt, Function.update_of_ne h]

@[simp] lemma flipAt_flipAt (x : Fin k → ZMod 2) (i : Fin k) :
    flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h
    rw [flipAt_self, flipAt_self, add_assoc]
    norm_num
    decide +kernel
  · rw [flipAt_of_ne _ h, flipAt_of_ne _ h]

lemma flipAt_ne (x : Fin k → ZMod 2) (i : Fin k) : flipAt x i ≠ x := by
  intro h
  have h2 : flipAt x i i = x i := by rw [h]
  rw [flipAt_self] at h2
  exact absurd (by linear_combination h2 : (1 : ZMod 2) = 0) (by decide)

lemma flipAt_comm (x : Fin k → ZMod 2) (i j : Fin k) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext l
  by_cases hi : l = i <;> by_cases hj : l = j
  · subst hi; subst hj; rfl
  · subst hi; rw [flipAt_of_ne _ hj, flipAt_self, flipAt_self, flipAt_of_ne _ hj]
  · subst hj; rw [flipAt_self, flipAt_of_ne _ hi, flipAt_of_ne _ hi, flipAt_self]
  · rw [flipAt_of_ne _ hj, flipAt_of_ne _ hi, flipAt_of_ne _ hi, flipAt_of_ne _ hj]

lemma flipAt_injective (x : Fin k → ZMod 2) : Function.Injective (flipAt x) := by
  intro i j h
  by_contra hij
  have h2 := congrFun h i
  rw [flipAt_self, flipAt_of_ne x hij] at h2
  exact absurd (by linear_combination h2 : (1 : ZMod 2) = 0) (by decide)

/-- The `k`-dimensional hypercube graph `Q_k`, on the `2^k` points of `(ZMod 2)^k`:
two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Fin k → ZMod 2) where
  Adj x y := ∃ i, y = flipAt x i
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by rw [flipAt_flipAt]⟩
  loopless := ⟨fun x ⟨i, h⟩ => flipAt_ne x i h.symm⟩

instance instDecidableRelHypercubeAdj (k : ℕ) : DecidableRel (hypercube k).Adj := by
  intro x y
  unfold hypercube
  infer_instance

lemma neighborFinset_hypercube (x : Fin k → ZMod 2) :
    (hypercube k).neighborFinset x = Finset.univ.image (flipAt x) := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube, eq_comm]

/-- Every vertex of `Q_k` has degree `k`. -/
lemma degree_hypercube (x : Fin k → ZMod 2) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_hypercube,
    Finset.card_image_of_injective _ (flipAt_injective x)]
  simp

lemma sum_neighbors (v : (Fin k → ZMod 2) → ℝ) (x : Fin k → ZMod 2) :
    ∑ y ∈ (hypercube k).neighborFinset x, v y = ∑ i, v (flipAt x i) := by
  rw [neighborFinset_hypercube, Finset.sum_image]
  intro i _ j _ h
  exact flipAt_injective x h

/-! ## The Laplacian as an operator on functions -/

/-- The Laplacian operator of the hypercube, acting on real functions on the cube. -/
noncomputable def lapOp (k : ℕ) (v : (Fin k → ZMod 2) → ℝ) : (Fin k → ZMod 2) → ℝ :=
  fun x => ∑ i, (v x - v (flipAt x i))

/-- The Laplacian matrix of the hypercube acts on vectors as `lapOp`. -/
lemma lapMatrix_mulVec_eq (k : ℕ) (v : (Fin k → ZMod 2) → ℝ) :
    (SimpleGraph.lapMatrix ℝ (hypercube k)) *ᵥ v = lapOp k v := by
  funext x
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec]
  simp only [Pi.sub_apply, SimpleGraph.degMatrix, Matrix.mulVec_diagonal,
    SimpleGraph.adjMatrix_mulVec_apply, sum_neighbors, lapOp, Finset.sum_sub_distrib,
    degree_hypercube]
  simp [Finset.sum_const, Finset.card_univ]

/-- The one-dimensional difference operator in direction `i`. -/
noncomputable def diffOp (i : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    (Fin k → ZMod 2) → ℝ := fun x => v x - v (flipAt x i)

lemma lapOp_eq_sum_diffOp (v : (Fin k → ZMod 2) → ℝ) :
    lapOp k v = fun x => ∑ i, diffOp i v x := rfl

lemma diffOp_const_mul (c : ℝ) (i : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    diffOp i (fun x => c * v x) = fun x => c * diffOp i v x := by
  funext x
  simp only [diffOp]
  ring

lemma diffOp_sum {ι : Type*} (s : Finset ι) (i : Fin k)
    (f : ι → (Fin k → ZMod 2) → ℝ) :
    diffOp i (fun x => ∑ j ∈ s, f j x) = fun x => ∑ j ∈ s, diffOp i (f j) x := by
  funext x
  simp only [diffOp, Finset.sum_sub_distrib]

lemma lapOp_const_mul (c : ℝ) (v : (Fin k → ZMod 2) → ℝ) :
    lapOp k (fun x => c * v x) = fun x => c * lapOp k v x := by
  funext x
  simp only [lapOp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma diffOp_diffOp_self (i : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    diffOp i (diffOp i v) = fun x => 2 * diffOp i v x := by
  funext x
  simp only [diffOp, flipAt_flipAt]
  ring

lemma diffOp_comm (i j : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    diffOp i (diffOp j v) = diffOp j (diffOp i v) := by
  funext x
  simp only [diffOp, flipAt_comm x i j]
  ring

/-- The composite `D_i ∘ D_j` is four times an idempotent: `T ∘ T = 4 • T`. -/
lemma diffOp_pair_sq (i j : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    diffOp i (diffOp j (diffOp i (diffOp j v))) =
      fun x => 4 * diffOp i (diffOp j v) x := by
  have h1 : diffOp j (diffOp i (diffOp j v)) = diffOp i (diffOp j (diffOp j v)) := by
    rw [diffOp_comm j i (diffOp j v)]
  rw [h1, diffOp_diffOp_self j v, diffOp_const_mul, diffOp_const_mul,
    diffOp_diffOp_self i (diffOp j v)]
  funext x
  ring

/-! ## The inner product and the spectral gap inequality -/

/-- Inner product of real functions on the cube. -/
noncomputable def ip (u v : (Fin k → ZMod 2) → ℝ) : ℝ := ∑ x, u x * v x

lemma ip_self_nonneg (v : (Fin k → ZMod 2) → ℝ) : 0 ≤ ip v v :=
  Finset.sum_nonneg fun x _ => mul_self_nonneg (v x)

lemma ip_self_pos {v : (Fin k → ZMod 2) → ℝ} (hv : v ≠ 0) : 0 < ip v v := by
  rcases Function.ne_iff.mp hv with ⟨x, hx⟩
  exact Finset.sum_pos' (fun y _ => mul_self_nonneg (v y))
    ⟨x, Finset.mem_univ x, mul_self_pos.mpr (by simpa using hx)⟩

lemma ip_const_mul_right (c : ℝ) (u v : (Fin k → ZMod 2) → ℝ) :
    ip u (fun x => c * v x) = c * ip u v := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Reindexing a sum along the involution `flipAt · i`. -/
lemma sum_flipAt (i : Fin k) (f : (Fin k → ZMod 2) → ℝ) :
    ∑ x, f (flipAt x i) = ∑ x, f x := by
  refine Finset.sum_nbij' (fun x => flipAt x i) (fun x => flipAt x i) ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> simp

/-- `diffOp i` is self-adjoint for the inner product `ip`. -/
lemma ip_diffOp_left (i : Fin k) (u v : (Fin k → ZMod 2) → ℝ) :
    ip u (diffOp i v) = ip (diffOp i u) v := by
  have h1 : ∑ x, u x * v (flipAt x i) = ∑ x, u (flipAt x i) * v x := by
    have h := sum_flipAt i (fun x => u (flipAt x i) * v x)
    simp only [flipAt_flipAt] at h
    exact h
  simp only [ip, diffOp, mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1]

/-- Every quadratic form `⟪v, D_i D_j v⟫` is nonnegative. -/
lemma ip_diffOp_pair_nonneg (i j : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    0 ≤ ip v (diffOp i (diffOp j v)) := by
  set T : (Fin k → ZMod 2) → ℝ := diffOp i (diffOp j v) with hT
  have h4 : 4 * ip v T = ip T T := by
    have e1 : ip v (fun x => 4 * T x) = 4 * ip v T := ip_const_mul_right 4 v T
    have e2 : ip v (diffOp i (diffOp j T)) = ip (diffOp j (diffOp i v)) T := by
      rw [ip_diffOp_left i v (diffOp j T), ip_diffOp_left j (diffOp i v) T]
    have e3 : diffOp i (diffOp j T) = fun x => 4 * T x := by
      rw [hT]; exact diffOp_pair_sq i j v
    rw [← e1, ← e3, e2, diffOp_comm j i v]
  nlinarith [ip_self_nonneg T, h4]

lemma ip_lapOp (v : (Fin k → ZMod 2) → ℝ) :
    ip v (lapOp k v) = ∑ i, ip v (diffOp i v) := by
  simp only [ip, lapOp, diffOp, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma ip_lapOp_lapOp (v : (Fin k → ZMod 2) → ℝ) :
    ip v (lapOp k (lapOp k v)) = ∑ i, ∑ j, ip v (diffOp i (diffOp j v)) := by
  have h : lapOp k (lapOp k v) = fun x => ∑ i, ∑ j, diffOp i (diffOp j v) x := by
    funext x
    rw [lapOp_eq_sum_diffOp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := diffOp_sum (Finset.univ : Finset (Fin k)) i (fun j => diffOp j v)
    exact congrFun this x
  rw [h]
  simp only [ip, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma ip_diffOp_self_nonneg (i : Fin k) (v : (Fin k → ZMod 2) → ℝ) :
    0 ≤ ip v (diffOp i v) := by
  have h : 2 * ip v (diffOp i v) = ip (diffOp i v) (diffOp i v) := by
    have e1 : ip v (diffOp i (diffOp i v)) = ip (diffOp i v) (diffOp i v) :=
      ip_diffOp_left i v (diffOp i v)
    rw [diffOp_diffOp_self i v, ip_const_mul_right] at e1
    exact e1
  nlinarith [ip_self_nonneg (diffOp i v), h]

lemma ip_lapOp_nonneg (v : (Fin k → ZMod 2) → ℝ) : 0 ≤ ip v (lapOp k v) := by
  rw [ip_lapOp]
  exact Finset.sum_nonneg fun i _ => ip_diffOp_self_nonneg i v

/-- The key operator inequality `L² ⪰ 2 L`, which forces every nonzero eigenvalue
of the hypercube Laplacian to be at least `2`. -/
lemma two_ip_lapOp_le (v : (Fin k → ZMod 2) → ℝ) :
    2 * ip v (lapOp k v) ≤ ip v (lapOp k (lapOp k v)) := by
  rw [ip_lapOp, ip_lapOp_lapOp, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hdiag : 2 * ip v (diffOp i v) = ip v (diffOp i (diffOp i v)) := by
    rw [diffOp_diffOp_self i v, ip_const_mul_right]
  rw [hdiag]
  exact Finset.single_le_sum (f := fun j => ip v (diffOp i (diffOp j v)))
    (fun j _ => ip_diffOp_pair_nonneg i j v) (Finset.mem_univ i)

/-! ## An eigenvector for the eigenvalue 2 -/

/-- The parity character in the first coordinate: an eigenvector of the Laplacian
of `Q_k` with eigenvalue `2`. -/
noncomputable def chi (k : ℕ) (hk : 1 ≤ k) : (Fin k → ZMod 2) → ℝ :=
  fun x => if x ⟨0, hk⟩ = 0 then 1 else -1

lemma chi_ne_zero (k : ℕ) (hk : 1 ≤ k) : chi k hk ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [chi] at this

lemma chi_flipAt_first (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ZMod 2) :
    chi k hk (flipAt x ⟨0, hk⟩) = - chi k hk x := by
  have hx : x ⟨0, hk⟩ = 0 ∨ x ⟨0, hk⟩ = 1 := by
    revert hk
    intro hk
    generalize x ⟨0, hk⟩ = a
    revert a
    decide +kernel
  simp only [chi, flipAt_self]
  rcases hx with h | h <;> rw [h] <;> norm_num
  · decide +kernel

lemma chi_flipAt_other (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ZMod 2) {i : Fin k}
    (hi : i ≠ ⟨0, hk⟩) : chi k hk (flipAt x i) = chi k hk x := by
  simp only [chi]
  rw [flipAt_of_ne x (Ne.symm hi)]

lemma lapOp_chi (k : ℕ) (hk : 1 ≤ k) : lapOp k (chi k hk) = (2 : ℝ) • chi k hk := by
  funext x
  simp only [lapOp, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · rw [chi_flipAt_first k hk x]; ring
  · intro i _ hi
    rw [chi_flipAt_other k hk x hi]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Main theorem -/

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian matrix of the
hypercube graph `Q_k` (on `2^k` vertices) is exactly `2`.  Since the bound `2` does not
depend on `k`, the family `(Q_k)` has a uniform spectral gap: uniform-gap graph families
exist. -/
theorem expander_uniform_gap_witness (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → ZMod 2) → ℝ, v ≠ 0 ∧
      (SimpleGraph.lapMatrix ℝ (hypercube k)) *ᵥ v = μ • v} 2 := by
  constructor
  · refine ⟨two_ne_zero, chi k hk, chi_ne_zero k hk, ?_⟩
    rw [lapMatrix_mulVec_eq]
    exact lapOp_chi k hk
  · rintro μ ⟨hμ, v, hv, hLv⟩
    rw [lapMatrix_mulVec_eq] at hLv
    have hsm : (μ • v) = fun x => μ * v x := rfl
    rw [hsm] at hLv
    have hvv : 0 < ip v v := ip_self_pos hv
    have h1 : ip v (lapOp k v) = μ * ip v v := by
      rw [hLv, ip_const_mul_right]
    have h2 : ip v (lapOp k (lapOp k v)) = μ ^ 2 * ip v v := by
      rw [hLv, lapOp_const_mul, hLv]
      have : (fun x => μ * (fun y => μ * v y) x) = fun x => μ ^ 2 * v x := by
        funext x; ring
      rw [this, ip_const_mul_right]
    have key := two_ip_lapOp_le v
    rw [h1, h2] at key
    have hμ0 : 0 ≤ μ := by
      have h0 := ip_lapOp_nonneg v
      rw [h1] at h0
      nlinarith
    have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
    have key' : (2 * μ) * ip v v ≤ μ ^ 2 * ip v v := by linarith
    have h3 : 2 * μ ≤ μ ^ 2 := le_of_mul_le_mul_right key' hvv
    nlinarith [h3, hμpos]

/-- `Q_k` has `2 ^ k` vertices. -/
lemma card_hypercube_vertices (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp

/-- **Uniform spectral gap, stated as a single bound valid for the whole family.**
Every nonzero Laplacian eigenvalue of every hypercube `Q_k` with `k ≥ 1` is at least `2`,
and the bound `2` is attained for each such `k`. -/
theorem hypercube_uniform_spectral_gap :
    ∃ gap : ℝ, 0 < gap ∧ ∀ k : ℕ, 1 ≤ k →
      (∀ μ : ℝ, μ ≠ 0 → (∃ v : (Fin k → ZMod 2) → ℝ, v ≠ 0 ∧
          (SimpleGraph.lapMatrix ℝ (hypercube k)) *ᵥ v = μ • v) → gap ≤ μ) ∧
      (∃ v : (Fin k → ZMod 2) → ℝ, v ≠ 0 ∧
          (SimpleGraph.lapMatrix ℝ (hypercube k)) *ᵥ v = gap • v) := by
  refine ⟨2, two_pos, fun k hk => ⟨fun μ hμ hv => ?_, ?_⟩⟩
  · exact (expander_uniform_gap_witness k hk).2 ⟨hμ, hv⟩
  · obtain ⟨-, v, hv0, hv⟩ := (expander_uniform_gap_witness k hk).1
    exact ⟨v, hv0, hv⟩

end Frontier.Spectral

