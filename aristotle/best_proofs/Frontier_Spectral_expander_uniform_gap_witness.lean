/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/
def cflip {k : ℕ} (i : Fin k) (x : Fin k → Bool) : Fin k → Bool :=
  Function.update x i (!x i)

@[simp] lemma cflip_self {k : ℕ} (i : Fin k) (x : Fin k → Bool) : cflip i x i = !x i := by
  simp [cflip]

lemma cflip_of_ne {k : ℕ} {i j : Fin k} (h : j ≠ i) (x : Fin k → Bool) :
    cflip i x j = x j := by
  simp [cflip, Function.update_of_ne h]

@[simp] lemma cflip_cflip {k : ℕ} (i : Fin k) (x : Fin k → Bool) : cflip i (cflip i x) = x := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [cflip_of_ne h]

lemma cflip_involutive {k : ℕ} (i : Fin k) : Function.Involutive (cflip i) := cflip_cflip i

lemma cflip_ne {k : ℕ} (i : Fin k) (x : Fin k → Bool) : cflip i x ≠ x := by
  intro h
  have := congrFun h i
  simp at this

lemma cflip_injective {k : ℕ} (x : Fin k → Bool) :
    Function.Injective (fun i : Fin k => cflip i x) := by
  intro i j h
  by_contra hij
  have h1 : cflip i x i = cflip j x i := congrFun h i
  rw [cflip_self, cflip_of_ne hij] at h1
  simp at h1

/-- Reindexing a sum along the involution `cflip i`. -/
lemma sum_cflip {k : ℕ} (i : Fin k) (g : (Fin k → Bool) → ℝ) :
    ∑ x : Fin k → Bool, g (cflip i x) = ∑ x : Fin k → Bool, g x :=
  Equiv.sum_comp ((cflip_involutive i).toPerm) g

/-- The `k`-dimensional hypercube graph `Q_k`: vertices are the `2^k` bit strings of length `k`,
two of which are adjacent iff they differ in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Fin k → Bool) where
  Adj x y := ∃ i, y = cflip i x
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, (cflip_cflip i x).symm⟩
  loopless := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨i, h⟩ := hx
    exact cflip_ne i x h.symm

instance instDecidableRelHypercubeAdj (k : ℕ) : DecidableRel (hypercube k).Adj :=
  fun x y => inferInstanceAs (Decidable (∃ i, y = cflip i x))

lemma hypercube_adj_iff {k : ℕ} (x y : Fin k → Bool) :
    (hypercube k).Adj x y ↔ ∃ i, y = cflip i x := Iff.rfl

/-- The adjacency relation of `hypercube k` is exactly "differ in precisely one coordinate". -/
lemma hypercube_adj_iff_card_eq_one {k : ℕ} (x y : Fin k → Bool) :
    (hypercube k).Adj x y ↔ (Finset.univ.filter (fun i : Fin k => x i ≠ y i)).card = 1 := by
  constructor
  · rintro ⟨i, rfl⟩
    have : Finset.univ.filter (fun i' : Fin k => x i' ≠ cflip i x i') = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj
        by_contra hji
        exact hj (by rw [cflip_of_ne hji])
      · rintro rfl
        simp
    rw [this, Finset.card_singleton]
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h
    refine ⟨i, funext fun j => ?_⟩
    rcases eq_or_ne j i with rfl | hji
    · have hj : j ∈ ({j} : Finset (Fin k)) := Finset.mem_singleton_self j
      rw [← hi] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [cflip_self]
      revert hj
      cases x j <;> cases y j <;> simp
    · have hj : j ∉ ({i} : Finset (Fin k)) := by simpa using hji
      rw [← hi] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      rw [cflip_of_ne hji, hj]

/-- `Q_k` has `2 ^ k` vertices. -/
lemma card_hypercube_vertices (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by simp

lemma neighborFinset_hypercube {k : ℕ} (x : Fin k → Bool) :
    (hypercube k).neighborFinset x = Finset.image (fun i => cflip i x) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube_adj_iff, eq_comm]

lemma sum_neighbors {k : ℕ} (x : Fin k → Bool) (g : (Fin k → Bool) → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, g u = ∑ i : Fin k, g (cflip i x) := by
  rw [neighborFinset_hypercube, Finset.sum_image]
  intro i _ j _ h
  exact cflip_injective x h

lemma degree_hypercube {k : ℕ} (x : Fin k → Bool) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_hypercube,
    Finset.card_image_of_injective _ (cflip_injective x)]
  simp

lemma lap_apply {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ((hypercube k).lapMatrix ℝ *ᵥ f) x = k * f x - ∑ i : Fin k, f (cflip i x) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_neighbors, degree_hypercube]

/-- The Dirichlet energy of `f` on the hypercube, summed over ordered pairs of adjacent
vertices. -/
def En {k : ℕ} (f : (Fin k → Bool) → ℝ) : ℝ :=
  ∑ x : Fin k → Bool, ∑ i : Fin k, (f x - f (cflip i x)) ^ 2

lemma dotProduct_lap {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) = En f / 2 := by
  have hsq : ∑ x : Fin k → Bool, ∑ i : Fin k, (f (cflip i x)) ^ 2
      = ∑ x : Fin k → Bool, ∑ i : Fin k, (f x) ^ 2 := by
    calc ∑ x : Fin k → Bool, ∑ i : Fin k, (f (cflip i x)) ^ 2
        = ∑ i : Fin k, ∑ x : Fin k → Bool, (f (cflip i x)) ^ 2 := Finset.sum_comm
      _ = ∑ _i : Fin k, ∑ x : Fin k → Bool, (f x) ^ 2 :=
          Finset.sum_congr rfl fun i _ => sum_cflip i (fun x => (f x) ^ 2)
      _ = ∑ x : Fin k → Bool, ∑ _i : Fin k, (f x) ^ 2 := Finset.sum_comm
  have hEn : En f = 2 * ∑ x : Fin k → Bool, ∑ i : Fin k, ((f x) ^ 2 - f x * f (cflip i x)) := by
    unfold En
    have h1 : ∑ x : Fin k → Bool, ∑ i : Fin k, (f x - f (cflip i x)) ^ 2
        = (∑ x : Fin k → Bool, ∑ i : Fin k, ((f x) ^ 2 - 2 * (f x * f (cflip i x))))
          + ∑ x : Fin k → Bool, ∑ i : Fin k, (f (cflip i x)) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hsq, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hEn]
  have : f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f)
      = ∑ x : Fin k → Bool, ∑ i : Fin k, ((f x) ^ 2 - f x * f (cflip i x)) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lap_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [this]
  ring

lemma sum_lap_eq_zero {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    ∑ x : Fin k → Bool, ((hypercube k).lapMatrix ℝ *ᵥ f) x = 0 := by
  have h : ∑ x : Fin k → Bool, ((hypercube k).lapMatrix ℝ *ᵥ f) x
      = (∑ x : Fin k → Bool, ∑ i : Fin k, f x)
        - ∑ x : Fin k → Bool, ∑ i : Fin k, f (cflip i x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lap_apply, ← Finset.sum_sub_distrib]
    simp
  rw [h, sub_eq_zero]
  calc ∑ _x : Fin k → Bool, ∑ _i : Fin k, f _x
      = ∑ _i : Fin k, ∑ _x : Fin k → Bool, f _x := Finset.sum_comm
    _ = ∑ i : Fin k, ∑ x : Fin k → Bool, f (cflip i x) :=
        Finset.sum_congr rfl fun i _ => (sum_cflip i f).symm
    _ = ∑ x : Fin k → Bool, ∑ i : Fin k, f (cflip i x) := Finset.sum_comm

/-! ### The Poincaré inequality for the hypercube -/

lemma cflip_zero_cons {k : ℕ} (b : Bool) (y : Fin k → Bool) :
    cflip 0 (Fin.cons b y) = Fin.cons (!b) y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [cflip]
  · intro j
    rw [cflip_of_ne (Fin.succ_ne_zero j)]
    simp

lemma cflip_succ_cons {k : ℕ} (i : Fin k) (b : Bool) (y : Fin k → Bool) :
    cflip i.succ (Fin.cons b y) = Fin.cons b (cflip i y) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [cflip_of_ne (Fin.succ_ne_zero i).symm]
    simp
  · intro j
    simp only [cflip, Function.update_apply, Fin.succ_inj, Fin.cons_succ]

lemma sum_cons_split {k : ℕ} (F : (Fin (k + 1) → Bool) → ℝ) :
    ∑ x : Fin (k + 1) → Bool, F x
      = ∑ y : Fin k → Bool, (F (Fin.cons false y) + F (Fin.cons true y)) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) => Bool) F]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [add_comm]
  rfl

/-- Poincaré inequality: `4 * (∑ f² - (∑ f)²/2^k) ≤ En f`. -/
theorem poincare (k : ℕ) (f : (Fin k → Bool) → ℝ) :
    4 * ((∑ x : Fin k → Bool, (f x) ^ 2) - (∑ x : Fin k → Bool, f x) ^ 2 / 2 ^ k) ≤ En f := by
  induction k with
  | zero =>
    have h1 : (Finset.univ : Finset (Fin 0 → Bool)) = {fun _ => false} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_univ _, fun x _ => ?_⟩
      funext i
      exact absurd i.2 (by omega)
    simp [En]
  | succ k ih =>
    have hN : (0:ℝ) < 2 ^ k := by positivity
    have ih0 := ih (fun y => f (Fin.cons false y))
    have ih1 := ih (fun y => f (Fin.cons true y))
    have hsq : ∑ x : Fin (k + 1) → Bool, (f x) ^ 2
        = (∑ y : Fin k → Bool, (f (Fin.cons false y)) ^ 2)
          + ∑ y : Fin k → Bool, (f (Fin.cons true y)) ^ 2 := by
      rw [sum_cons_split (fun x => (f x) ^ 2), Finset.sum_add_distrib]
    have hs : ∑ x : Fin (k + 1) → Bool, f x
        = (∑ y : Fin k → Bool, f (Fin.cons false y))
          + ∑ y : Fin k → Bool, f (Fin.cons true y) := by
      rw [sum_cons_split f, Finset.sum_add_distrib]
    have hEn : En f = En (fun y => f (Fin.cons false y)) + En (fun y => f (Fin.cons true y))
        + 2 * ∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
      simp only [En]
      rw [sum_cons_split (fun x => ∑ i : Fin (k + 1), (f x - f (cflip i x)) ^ 2)]
      simp only [Fin.sum_univ_succ, cflip_zero_cons, cflip_succ_cons, Bool.not_false,
        Bool.not_true]
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hCS : ((∑ y : Fin k → Bool, f (Fin.cons false y))
          - ∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2
        ≤ 2 ^ k * ∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k → Bool)))
        (f := fun y => f (Fin.cons false y) - f (Fin.cons true y))
      rw [Finset.sum_sub_distrib] at h
      simpa using h
    have hD : ((∑ y : Fin k → Bool, f (Fin.cons false y))
          - ∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2 / 2 ^ k
        ≤ ∑ y : Fin k → Bool, (f (Fin.cons false y) - f (Fin.cons true y)) ^ 2 := by
      rw [div_le_iff₀ hN]
      linarith [hCS]
    have hid : 4 * ((∑ y : Fin k → Bool, f (Fin.cons false y)) ^ 2 / 2 ^ k)
        + 4 * ((∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2 / 2 ^ k)
        - 4 * (((∑ y : Fin k → Bool, f (Fin.cons false y))
            + ∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2 / (2 ^ k * 2))
        = 2 * (((∑ y : Fin k → Bool, f (Fin.cons false y))
            - ∑ y : Fin k → Bool, f (Fin.cons true y)) ^ 2 / 2 ^ k) := by
      field_simp
      ring
    rw [hsq, hs, hEn, pow_succ (2:ℝ) k]
    linarith [ih0, ih1, hD, hid]

/-! ### The spectral gap -/

theorem energy_ge_of_sum_eq_zero {k : ℕ} (f : (Fin k → Bool) → ℝ)
    (hf : ∑ x : Fin k → Bool, f x = 0) :
    2 * ∑ x : Fin k → Bool, (f x) ^ 2 ≤ f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) := by
  have := poincare k f
  rw [dotProduct_lap]
  rw [hf] at this
  simp at this
  linarith

/-- **Uniform spectral gap for the hypercube family.** For every `k ≥ 1`, the smallest nonzero
eigenvalue of the Laplacian of the hypercube graph `Q_k` on `2^k` vertices equals `2`, a bound
independent of `k`. -/
theorem expander_uniform_gap_witness (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} 2 := by
  constructor
  · -- `2` is an eigenvalue: the character `x ↦ (-1)^(x i₀)` is an eigenvector.
    refine ⟨two_ne_zero, fun x => if x ⟨0, hk⟩ then (-1 : ℝ) else 1, ?_, ?_⟩
    · intro hcon
      have := congrFun hcon (fun _ => false)
      simp at this
    · funext x
      set i0 : Fin k := ⟨0, hk⟩ with hi0
      set v : (Fin k → Bool) → ℝ := fun x => if x i0 then (-1 : ℝ) else 1 with hv
      have hterm : ∀ i : Fin k, v (cflip i x) = v x - (if i = i0 then 2 * v x else 0) := by
        intro i
        rcases eq_or_ne i i0 with rfl | h
        · simp only [hv, cflip_self]
          cases hx : x i0 <;> norm_num
        · rw [if_neg h]
          simp [hv, cflip_of_ne (Ne.symm h)]
      have hsum : ∑ i : Fin k, v (cflip i x) = k * v x - 2 * v x := by
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq' Finset.univ i0]
        simp
      rw [lap_apply, hsum]
      simp [Pi.smul_apply]
  · -- every nonzero eigenvalue is at least `2`
    rintro μ ⟨hμ, v, hv0, hv⟩
    have hsum0 : ∑ x : Fin k → Bool, v x = 0 := by
      have h := sum_lap_eq_zero v
      rw [hv] at h
      have : μ * ∑ x : Fin k → Bool, v x = 0 := by
        rw [Finset.mul_sum]
        simpa [Pi.smul_apply, smul_eq_mul] using h
      exact (mul_eq_zero.1 this).resolve_left hμ
    have hquad : v ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ v) = μ * ∑ x : Fin k → Bool, (v x) ^ 2 := by
      rw [hv, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
    have hpos : 0 < ∑ x : Fin k → Bool, (v x) ^ 2 := by
      obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv0 (funext fun x => hcon x)
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨x, Finset.mem_univ x, ?_⟩
      positivity
    have hge := energy_ge_of_sum_eq_zero v hsum0
    rw [hquad] at hge
    exact le_of_mul_le_mul_right (by linarith) hpos

/-- **The hypercube family has a spectral gap bounded below uniformly in `k`.** There is a single
constant `c = 2 > 0` such that for every `k ≥ 1`, every nonzero eigenvalue of the Laplacian of
`Q_k` is at least `c`, and `c` is attained. -/
theorem hypercube_uniform_spectral_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} c :=
  ⟨2, two_pos, fun k hk => expander_uniform_gap_witness k hk⟩

end Frontier.Spectral

