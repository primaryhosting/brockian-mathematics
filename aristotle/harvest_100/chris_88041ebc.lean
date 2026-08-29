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

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1` in place `i`). -/
def cubeE {k : ℕ} (i : Fin k) : Cube k := Pi.single i 1

lemma cubeE_add_self {k : ℕ} (i : Fin k) : cubeE i + cubeE i = 0 := by
  funext j
  simp [cubeE, CharTwo.add_self_eq_zero]

lemma cubeE_ne_zero {k : ℕ} (i : Fin k) : cubeE i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [cubeE] at this

/-- The hypercube graph `Q k`: two bit strings are adjacent iff they differ
in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i, y = x + cubeE i
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by rw [add_assoc, cubeE_add_self, add_zero]⟩
  loopless := ⟨fun x ⟨i, h⟩ => cubeE_ne_zero i (by simpa using h.symm)⟩

instance (k : ℕ) : DecidableRel (hypercube k).Adj :=
  fun x y => inferInstanceAs (Decidable (∃ i, y = x + cubeE i))

lemma hypercube_adj_iff {k : ℕ} (x y : Cube k) :
    (hypercube k).Adj x y ↔ ∃ i, y = x + cubeE i := Iff.rfl

/-- Neighbours of `x` are exactly the `x + cubeE i`. -/
lemma neighborFinset_hypercube {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.univ.image (fun i : Fin k => x + cubeE i) := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube_adj_iff, eq_comm]

lemma cubeE_injective {k : ℕ} : Function.Injective (fun i : Fin k => cubeE i) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [cubeE, hij] at this

lemma cubeE_add_injective {k : ℕ} (x : Cube k) :
    Function.Injective (fun i : Fin k => x + cubeE i) := by
  intro i j h
  exact cubeE_injective (by simpa using h)

lemma sum_over_neighbors {k : ℕ} (x : Cube k) (g : Cube k → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, g u = ∑ i : Fin k, g (x + cubeE i) := by
  rw [neighborFinset_hypercube, Finset.sum_image]
  intro i _ j _ h
  exact cubeE_add_injective x h

lemma degree_hypercube {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_hypercube,
    Finset.card_image_of_injective _ (cubeE_add_injective x)]
  simp

/-- The Dirichlet energy of `f` on the hypercube. -/
noncomputable def energy (k : ℕ) (f : Cube k → ℝ) : ℝ :=
  ∑ x : Cube k, ∑ i : Fin k, (f x - f (x + cubeE i)) ^ 2

lemma card_cube (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by simp

/-- Splitting a sum over the `(k+1)`-cube according to the first coordinate. -/
lemma cube_sum_succ {k : ℕ} (F : Cube (k + 1) → ℝ) :
    ∑ x : Cube (k + 1), F x = ∑ y : Cube k, (F (Fin.cons 0 y) + F (Fin.cons 1 y)) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ => ZMod 2)) (fun p => F (Fin.cons p.1 p.2)) F
    (fun _ => rfl), Fintype.sum_prod_type]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => by simp

lemma cons_add_cubeE_zero {k : ℕ} (a : ZMod 2) (y : Cube k) :
    Fin.cons a y + cubeE 0 = Fin.cons (a + 1) y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cubeE]
  · intro j; simp [cubeE, Fin.succ_ne_zero]

lemma cons_add_cubeE_succ {k : ℕ} (a : ZMod 2) (y : Cube k) (j : Fin k) :
    Fin.cons a y + cubeE j.succ = Fin.cons a (y + cubeE j) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cubeE, (Fin.succ_ne_zero j).symm]
  · intro m; simp [cubeE, Pi.single_apply, Fin.succ_inj]

/-- Tensorization of the Dirichlet energy along the first coordinate. -/
lemma energy_succ {k : ℕ} (f : Cube (k + 1) → ℝ) :
    energy (k + 1) f
      = 2 * (∑ y : Cube k, (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2)
        + energy k (fun y => f (Fin.cons 0 y)) + energy k (fun y => f (Fin.cons 1 y)) := by
  have h01 : (0 : ZMod 2) + 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have key : ∀ y : Cube k,
      (∑ i : Fin (k + 1), (f (Fin.cons 0 y) - f (Fin.cons 0 y + cubeE i)) ^ 2)
        + (∑ i : Fin (k + 1), (f (Fin.cons 1 y) - f (Fin.cons 1 y + cubeE i)) ^ 2)
      = 2 * (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2
        + ((∑ j : Fin k, (f (Fin.cons 0 y) - f (Fin.cons 0 (y + cubeE j))) ^ 2)
          + (∑ j : Fin k, (f (Fin.cons 1 y) - f (Fin.cons 1 (y + cubeE j))) ^ 2)) := by
    intro y
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [cons_add_cubeE_zero, cons_add_cubeE_succ, h01, h11]
    ring
  unfold energy
  rw [cube_sum_succ (fun x => ∑ i : Fin (k + 1), (f x - f (x + cubeE i)) ^ 2)]
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- Poincaré inequality on the hypercube (spectral gap `2`, in quadratic form). -/
lemma hypercube_poincare (k : ℕ) (f : Cube k → ℝ) :
    4 * ((2 : ℝ) ^ k * ∑ x : Cube k, f x ^ 2 - (∑ x : Cube k, f x) ^ 2)
      ≤ (2 : ℝ) ^ k * energy k f := by
  revert f
  induction k with
  | zero =>
      intro f
      simp [energy, Finset.univ_unique]
  | succ k ih =>
      intro f
      set f0 : Cube k → ℝ := fun y => f (Fin.cons 0 y) with hf0
      set f1 : Cube k → ℝ := fun y => f (Fin.cons 1 y) with hf1
      have hsq : ∑ x : Cube (k + 1), f x ^ 2
          = (∑ y : Cube k, f0 y ^ 2) + ∑ y : Cube k, f1 y ^ 2 := by
        rw [cube_sum_succ (fun x => f x ^ 2), ← Finset.sum_add_distrib]
      have hsum : ∑ x : Cube (k + 1), f x
          = (∑ y : Cube k, f0 y) + ∑ y : Cube k, f1 y := by
        rw [cube_sum_succ f, ← Finset.sum_add_distrib]
      have hdiff : ∑ y : Cube k, (f0 y - f1 y)
          = (∑ y : Cube k, f0 y) - ∑ y : Cube k, f1 y := by
        rw [Finset.sum_sub_distrib]
      have hcs : ((∑ y : Cube k, f0 y) - ∑ y : Cube k, f1 y) ^ 2
          ≤ (2 : ℝ) ^ k * ∑ y : Cube k, (f0 y - f1 y) ^ 2 := by
        have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Cube k)))
          (f := fun y => f0 y - f1 y)
        rw [hdiff] at h
        simpa using h
      rw [hsq, hsum, energy_succ f, ← hf0, ← hf1]
      have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
      rw [hpow]
      nlinarith [ih f0, ih f1, hcs]

lemma sum_shift {k : ℕ} (i : Fin k) (g : Cube k → ℝ) :
    ∑ x : Cube k, g (x + cubeE i) = ∑ x : Cube k, g x :=
  Fintype.sum_equiv (Equiv.addRight (cubeE i)) _ _ (fun _ => rfl)

lemma sum_sum_shift {k : ℕ} (g : Cube k → ℝ) :
    ∑ x : Cube k, ∑ i : Fin k, g (x + cubeE i) = (k : ℝ) * ∑ x : Cube k, g x := by
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun i _ => sum_shift i g)]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma lapMatrix_hypercube_mulVec_apply {k : ℕ} (f : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ *ᵥ f) x = (k : ℝ) * f x - ∑ i : Fin k, f (x + cubeE i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_over_neighbors, degree_hypercube]

lemma energy_eq {k : ℕ} (f : Cube k → ℝ) :
    energy k f = 2 * ((k : ℝ) * (∑ x : Cube k, f x ^ 2)
      - ∑ x : Cube k, ∑ i : Fin k, f x * f (x + cubeE i)) := by
  have hpt : ∀ x : Cube k, ∑ i : Fin k, (f x - f (x + cubeE i)) ^ 2
      = ((k : ℝ) * f x ^ 2 + ∑ i : Fin k, f (x + cubeE i) ^ 2)
        - 2 * ∑ i : Fin k, f x * f (x + cubeE i) := by
    intro x
    have hexp : ∀ i : Fin k, (f x - f (x + cubeE i)) ^ 2
        = f x ^ 2 + f (x + cubeE i) ^ 2 - 2 * (f x * f (x + cubeE i)) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold energy
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_sum_shift (fun x => f x ^ 2)]
  ring

lemma quadForm_eq_energy {k : ℕ} (f : Cube k → ℝ) :
    f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) = energy k f / 2 := by
  have h2 : ∀ x : Cube k, f x * ((k : ℝ) * f x - ∑ i : Fin k, f (x + cubeE i))
      = (k : ℝ) * f x ^ 2 - ∑ i : Fin k, f x * f (x + cubeE i) := by
    intro x
    rw [mul_sub, Finset.mul_sum]
    ring
  rw [dotProduct]
  simp only [lapMatrix_hypercube_mulVec_apply]
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_sub_distrib, ← Finset.mul_sum, energy_eq]
  ring

/-- Eigenvectors for nonzero eigenvalues have zero mean. -/
lemma sum_eq_zero_of_eigen {k : ℕ} {μ : ℝ} {v : Cube k → ℝ}
    (hμ : μ ≠ 0) (hv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) :
    ∑ x : Cube k, v x = 0 := by
  have h1 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ v) x = 0 := by
    simp only [lapMatrix_hypercube_mulVec_apply]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sum_shift v, sub_self]
  rw [hv] at h1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h1
  exact (mul_eq_zero.mp h1).resolve_left hμ

/-- The parity function of the first coordinate is an eigenvector with eigenvalue `2`. -/
lemma two_is_eigenvalue {k : ℕ} (hk : 1 ≤ k) :
    ∃ v : Cube k → ℝ, v ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  have hk0 : 0 < k := hk
  set i0 : Fin k := ⟨0, hk0⟩ with hi0
  refine ⟨fun x => if x i0 = 0 then (1 : ℝ) else -1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Cube k)
    simp at h0
  · funext x
    set c : ℝ := if x i0 = 0 then (1 : ℝ) else -1 with hc
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have key : ∀ i : Fin k,
        (if (x + cubeE i) i0 = 0 then (1 : ℝ) else -1) = c - (if i = i0 then 2 * c else 0) := by
      intro i
      have h01 : (0 : ZMod 2) + 1 = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      by_cases hi : i = i0
      · have hx : (x + cubeE i) i0 = x i0 + 1 := by simp [cubeE, hi]
        rw [hx, if_pos hi, hc]
        rcases hcases (x i0) with h | h <;> rw [h] <;> simp only [h01, h11] <;> norm_num
      · have hx : (x + cubeE i) i0 = x i0 := by
          simp [cubeE, hi]
        simp [hx, hi, hc]
    rw [lapMatrix_hypercube_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ i0 (fun _ => 2 * c), if_pos (Finset.mem_univ i0),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube
graph `Q k` on `2 ^ k` vertices is exactly `2`, independently of `k`. -/
theorem expander_uniform_gap_witness (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : Cube k → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} 2 := by
  constructor
  · exact ⟨two_ne_zero, two_is_eigenvalue hk⟩
  · rintro μ ⟨hμ, v, hv, hLv⟩
    have hzero := sum_eq_zero_of_eigen hμ hLv
    have hSpos : 0 < ∑ x : Cube k, v x ^ 2 := by
      obtain ⟨x0, hx0⟩ : ∃ x : Cube k, v x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv (funext hcon)
      refine Finset.sum_pos' (fun x _ => sq_nonneg (v x)) ⟨x0, Finset.mem_univ x0, ?_⟩
      positivity
    have hq : v ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ v) = μ * ∑ x : Cube k, v x ^ 2 := by
      rw [hLv, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [Pi.smul_apply, smul_eq_mul]
      ring
    have henergy : energy k v = 2 * (μ * ∑ x : Cube k, v x ^ 2) := by
      have h := quadForm_eq_energy v
      rw [hq] at h
      linarith
    have hpo := hypercube_poincare k v
    rw [hzero, henergy] at hpo
    have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    norm_num at hpo
    nlinarith [hpo, mul_pos hpow hSpos]

/-- **Uniform spectral gap.** Every nonzero Laplacian eigenvalue of the hypercube `Q k`
(`k ≥ 1`) is at least `2`, a bound independent of the dimension `k`, while the graph
`Q k` has `2 ^ k` vertices. So the family `(Q k)` has a uniform spectral gap. -/
theorem hypercube_family_uniform_gap :
    (∀ k : ℕ, Fintype.card (Cube k) = 2 ^ k) ∧
    ∀ k : ℕ, 1 ≤ k → (∀ μ : ℝ, μ ≠ 0 → (∃ v : Cube k → ℝ, v ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) → 2 ≤ μ) ∧
      ∃ v : Cube k → ℝ, v ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  refine ⟨card_cube, fun k hk => ⟨fun μ hμ hv => ?_, two_is_eigenvalue hk⟩⟩
  exact (expander_uniform_gap_witness k hk).2 ⟨hμ, hv⟩

end Frontier.Spectral

