/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

lemma zmod_two_succ_ne (a : ZMod 2) : a + 1 ≠ a := by revert a; decide

lemma zmod_two_succ_succ (a : ZMod 2) : a + 1 + 1 = a := by revert a; decide

/-- Flip the `i`-th coordinate of a point of the cube. -/
def flipAt {k : ℕ} (i : Fin k) (x : Cube k) : Cube k := Function.update x i (x i + 1)

@[simp] lemma flipAt_apply_self {k : ℕ} (i : Fin k) (x : Cube k) :
    flipAt i x i = x i + 1 := by
  simp [flipAt]

lemma flipAt_apply_of_ne {k : ℕ} {i j : Fin k} (h : j ≠ i) (x : Cube k) :
    flipAt i x j = x j := by
  simp [flipAt, Function.update_of_ne h]

lemma flipAt_ne {k : ℕ} (i : Fin k) (x : Cube k) : flipAt i x ≠ x := by
  intro h
  have h1 := congrFun h i
  rw [flipAt_apply_self] at h1
  exact zmod_two_succ_ne (x i) h1

@[simp] lemma flipAt_flipAt {k : ℕ} (i : Fin k) (x : Cube k) :
    flipAt i (flipAt i x) = x := by
  funext j
  by_cases h : j = i
  · subst h
    rw [flipAt_apply_self, flipAt_apply_self, zmod_two_succ_succ]
  · rw [flipAt_apply_of_ne h, flipAt_apply_of_ne h]

lemma flipAt_injective {k : ℕ} (x : Cube k) :
    Function.Injective (fun i : Fin k => flipAt i x) := by
  intro i j h
  by_contra hij
  have h1 : flipAt i x j = flipAt j x j := congrFun h j
  rw [flipAt_apply_of_ne (Ne.symm hij), flipAt_apply_self] at h1
  exact zmod_two_succ_ne (x j) h1.symm

/-- The `k`-dimensional hypercube graph `Q_k`: two binary strings are adjacent iff they
differ in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i, y = flipAt i x
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by rw [flipAt_flipAt]⟩
  loopless := ⟨by
    rintro x ⟨i, h⟩
    exact flipAt_ne i x h.symm⟩

instance instDecidableAdj (k : ℕ) : DecidableRel (hypercube k).Adj :=
  fun x y => inferInstanceAs (Decidable (∃ i, y = flipAt i x))

@[simp] lemma hypercube_adj {k : ℕ} {x y : Cube k} :
    (hypercube k).Adj x y ↔ ∃ i, y = flipAt i x := Iff.rfl

lemma neighborFinset_eq {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.image (fun i : Fin k => flipAt i x) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, eq_comm]

lemma sum_neighbors {k : ℕ} (x : Cube k) (g : Cube k → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, g u = ∑ i : Fin k, g (flipAt i x) := by
  rw [neighborFinset_eq, Finset.sum_image]
  intro i _ j _ h
  exact flipAt_injective x h

@[simp] lemma degree_hypercube {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_eq,
    Finset.card_image_of_injective _ (flipAt_injective x), Finset.card_univ, Fintype.card_fin]

/-! ## The Dirichlet form and the Poincaré inequality -/

/-- The Dirichlet form of the hypercube: `∑_x ∑_i (f x - f (flip i x))^2`. -/
def Dir (k : ℕ) (f : Cube k → ℝ) : ℝ := ∑ x : Cube k, ∑ i : Fin k, (f x - f (flipAt i x)) ^ 2

lemma Dir_nonneg {k : ℕ} (f : Cube k → ℝ) : 0 ≤ Dir k f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma Dir_add_le {k : ℕ} (g h : Cube k → ℝ) :
    Dir k (g + h) / 2 ≤ Dir k g + Dir k h := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), Dir, Dir, Dir, ← Finset.sum_add_distrib,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg ((g x - g (flipAt i x)) - (h x - h (flipAt i x)))]

/-- Splitting a sum over the `(k+1)`-cube along the first coordinate. -/
lemma sum_cube_succ {k : ℕ} (F : Cube (k+1) → ℝ) :
    ∑ x : Cube (k+1), F x = ∑ y : Cube k, (F (Fin.cons 0 y) + F (Fin.cons 1 y)) := by
  have h1 : ∑ x : Cube (k+1), F x = ∑ p : ZMod 2 × Cube k, F (Fin.cons p.1 p.2) := by
    refine (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => ZMod 2)) _ _ ?_).symm
    intro p
    rfl
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

lemma flipAt_zero_cons {k : ℕ} (a : ZMod 2) (y : Cube k) :
    flipAt 0 (Fin.cons a y) = Fin.cons (a + 1) y := by
  funext j
  induction j using Fin.cases with
  | zero => simp [flipAt]
  | succ i =>
    rw [flipAt_apply_of_ne (Fin.succ_ne_zero i), Fin.cons_succ, Fin.cons_succ]

lemma flipAt_succ_cons {k : ℕ} (i : Fin k) (a : ZMod 2) (y : Cube k) :
    flipAt i.succ (Fin.cons a y) = Fin.cons a (flipAt i y) := by
  funext j
  induction j using Fin.cases with
  | zero =>
    rw [flipAt_apply_of_ne (Ne.symm (Fin.succ_ne_zero i)), Fin.cons_zero, Fin.cons_zero]
  | succ j =>
    by_cases hj : j = i
    · subst hj
      rw [flipAt_apply_self, Fin.cons_succ, Fin.cons_succ, flipAt_apply_self]
    · rw [flipAt_apply_of_ne (by simpa using hj), Fin.cons_succ, Fin.cons_succ,
        flipAt_apply_of_ne hj]

/-- The Dirichlet form on the `(k+1)`-cube decomposes along the first coordinate. -/
lemma Dir_succ {k : ℕ} (f : Cube (k+1) → ℝ) :
    Dir (k+1) f
      = Dir k (fun y => f (Fin.cons 0 y)) + Dir k (fun y => f (Fin.cons 1 y))
        + 2 * ∑ y : Cube k, (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2 := by
  rw [Dir, sum_cube_succ]
  have key : ∀ (a : ZMod 2) (y : Cube k),
      ∑ i : Fin (k+1), (f (Fin.cons a y) - f (flipAt i (Fin.cons a y))) ^ 2
        = (f (Fin.cons a y) - f (Fin.cons (a+1) y)) ^ 2
          + ∑ i : Fin k, (f (Fin.cons a y) - f (Fin.cons a (flipAt i y))) ^ 2 := by
    intro a y
    rw [Fin.sum_univ_succ, flipAt_zero_cons]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [flipAt_succ_cons]
  simp only [key]
  rw [show (0 : ZMod 2) + 1 = 1 from by decide, show (1 : ZMod 2) + 1 = 0 from by decide]
  rw [Dir, Dir, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hs : (f (Fin.cons 1 y) - f (Fin.cons 0 y)) ^ 2
      = (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2 := by ring
  rw [hs]
  ring

/-- **Poincaré inequality for the hypercube.** For any mean-zero function the Dirichlet
form dominates `4` times the squared `ℓ²`-norm. -/
lemma poincare (k : ℕ) (f : Cube k → ℝ) (hf : ∑ x : Cube k, f x = 0) :
    4 * ∑ x : Cube k, (f x) ^ 2 ≤ Dir k f := by
  induction k with
  | zero =>
    have hall : ∀ x : Cube 0, f x = 0 := by
      intro x
      rw [← Fintype.sum_subsingleton f x]
      exact hf
    simp [Dir, hall]
  | succ k ih =>
    set g : Cube k → ℝ := fun y => f (Fin.cons 0 y) with hg
    set h : Cube k → ℝ := fun y => f (Fin.cons 1 y) with hh
    have hsum : ∑ y : Cube k, (g + h) y = 0 := by
      rw [← hf, sum_cube_succ f]
      exact Finset.sum_congr rfl fun y _ => rfl
    have hIH : 4 * ∑ y : Cube k, ((g + h) y) ^ 2 ≤ Dir k (g + h) := ih _ hsum
    have hpar : Dir k (g + h) / 2 ≤ Dir k g + Dir k h := Dir_add_le g h
    have hlhs : ∑ x : Cube (k+1), (f x) ^ 2
        = ∑ y : Cube k, ((g y) ^ 2 + (h y) ^ 2) := sum_cube_succ (fun x => (f x) ^ 2)
    have hDir : Dir (k+1) f = Dir k g + Dir k h + 2 * ∑ y : Cube k, (g y - h y) ^ 2 :=
      Dir_succ f
    have hpt : 2 * ∑ y : Cube k, ((g + h) y) ^ 2 + 2 * ∑ y : Cube k, (g y - h y) ^ 2
        = 4 * ∑ y : Cube k, ((g y) ^ 2 + (h y) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Pi.add_apply]
      ring
    rw [hlhs, hDir]
    nlinarith [hIH, hpar, hpt]

/-! ## The Laplacian quadratic form -/

lemma sum_sum_add {k : ℕ} (p q : Cube k → Fin k → ℝ) :
    (∑ x : Cube k, ∑ i : Fin k, p x i) + (∑ x : Cube k, ∑ i : Fin k, q x i)
      = ∑ x : Cube k, ∑ i : Fin k, (p x i + q x i) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => (Finset.sum_add_distrib).symm

lemma sum_sum_sub {k : ℕ} (p q : Cube k → Fin k → ℝ) :
    (∑ x : Cube k, ∑ i : Fin k, p x i) - (∑ x : Cube k, ∑ i : Fin k, q x i)
      = ∑ x : Cube k, ∑ i : Fin k, (p x i - q x i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => (Finset.sum_sub_distrib _ _).symm

lemma sum_sum_mul {k : ℕ} (c : ℝ) (p : Cube k → Fin k → ℝ) :
    c * (∑ x : Cube k, ∑ i : Fin k, p x i) = ∑ x : Cube k, ∑ i : Fin k, c * p x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _

lemma sum_flip_sq {k : ℕ} (f : Cube k → ℝ) :
    ∑ x : Cube k, ∑ i : Fin k, (f (flipAt i x)) ^ 2
      = ∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2 := by
  have hi : ∀ i : Fin k, ∑ x : Cube k, (f (flipAt i x)) ^ 2 = ∑ x : Cube k, (f x) ^ 2 := by
    intro i
    refine Fintype.sum_bijective (flipAt i) ?_ _ _ (fun x => rfl)
    exact Function.bijective_iff_has_inverse.2
      ⟨flipAt i, fun x => flipAt_flipAt i x, fun x => flipAt_flipAt i x⟩
  calc ∑ x : Cube k, ∑ i : Fin k, (f (flipAt i x)) ^ 2
      = ∑ i : Fin k, ∑ x : Cube k, (f (flipAt i x)) ^ 2 := Finset.sum_comm
    _ = ∑ _i : Fin k, ∑ x : Cube k, (f x) ^ 2 := Finset.sum_congr rfl fun i _ => hi i
    _ = ∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2 := Finset.sum_comm

/-- The Laplacian quadratic form equals half the Dirichlet form. -/
lemma quadratic_form_eq {k : ℕ} (f : Cube k → ℝ) :
    ∑ x : Cube k, f x * ((hypercube k).lapMatrix ℝ *ᵥ f) x = Dir k f / 2 := by
  have h1 : ∑ x : Cube k, f x * ((hypercube k).lapMatrix ℝ *ᵥ f) x
      = (∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2)
        - (∑ x : Cube k, ∑ i : Fin k, f x * f (flipAt i x)) := by
    rw [sum_sum_sub]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [SimpleGraph.lapMatrix_mulVec_apply, sum_neighbors, degree_hypercube,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have h2 : Dir k f
      = (∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2)
        - 2 * (∑ x : Cube k, ∑ i : Fin k, f x * f (flipAt i x))
        + (∑ x : Cube k, ∑ i : Fin k, (f (flipAt i x)) ^ 2) := by
    rw [sum_sum_mul, sum_sum_sub, sum_sum_add, Dir]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, sum_flip_sq]
  ring

/-! ## Eigenvalues of the hypercube Laplacian -/

/-- `μ` is an eigenvalue of the Laplacian of the `k`-dimensional hypercube. -/
def IsLapEigenvalue (k : ℕ) (μ : ℝ) : Prop :=
  ∃ f : Cube k → ℝ, f ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ f = μ • f

/-- An eigenvector for a nonzero eigenvalue has zero mean. -/
lemma eigenvector_sum_zero {k : ℕ} {μ : ℝ} {f : Cube k → ℝ} (hμ : μ ≠ 0)
    (hf : (hypercube k).lapMatrix ℝ *ᵥ f = μ • f) : ∑ x : Cube k, f x = 0 := by
  have hcol : ∀ y : Cube k, ∑ x : Cube k, (hypercube k).lapMatrix ℝ x y = 0 := by
    intro y
    have hs := SimpleGraph.isSymm_lapMatrix (R := ℝ) (hypercube k)
    have h0 : ∑ x : Cube k, (hypercube k).lapMatrix ℝ y x = 0 := by
      have h := congrFun (SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℝ) (hypercube k)) y
      simpa [Matrix.mulVec, dotProduct] using h
    rw [← h0]
    exact Finset.sum_congr rfl fun x _ => hs.apply y x
  have h1 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ f) x = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [← Finset.sum_mul, hcol y, zero_mul]
  rw [hf] at h1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h1
  exact (mul_eq_zero.1 h1).resolve_left hμ

/-- Every nonzero Laplacian eigenvalue of the hypercube is at least `2`. -/
lemma two_le_of_isLapEigenvalue {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) (h : IsLapEigenvalue k μ) :
    2 ≤ μ := by
  obtain ⟨f, hf0, hf⟩ := h
  have hmean := eigenvector_sum_zero hμ hf
  have hq := quadratic_form_eq f
  rw [hf] at hq
  have hq' : μ * ∑ x : Cube k, (f x) ^ 2 = Dir k f / 2 := by
    rw [← hq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hpos : 0 < ∑ x : Cube k, (f x) ^ 2 := by
    refine Finset.sum_pos' (fun x _ => sq_nonneg _) ?_
    by_contra hcon
    push_neg at hcon
    apply hf0
    funext x
    have hx := hcon x (Finset.mem_univ x)
    have : (f x) ^ 2 = 0 := le_antisymm hx (sq_nonneg _)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hP := poincare k f hmean
  nlinarith [hP, hq', hpos]

/-- For `k ≥ 1`, the value `2` is an eigenvalue of the hypercube Laplacian:
the character `x ↦ (-1)^{x_0}` is an eigenvector with eigenvalue `2`. -/
lemma two_isLapEigenvalue {k : ℕ} (hk : 1 ≤ k) : IsLapEigenvalue k 2 := by
  classical
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  refine ⟨fun x => if x i0 = 0 then (1:ℝ) else -1, ?_, ?_⟩
  · intro hcon
    have hval := congrFun hcon (fun _ => 0)
    simp at hval
  · funext x
    set c : ℝ := if x i0 = 0 then (1:ℝ) else -1 with hc
    have hflip : ∀ i : Fin k, (if flipAt i x i0 = 0 then (1:ℝ) else -1)
        = if i = i0 then -c else c := by
      intro i
      by_cases hi : i = i0
      · rw [if_pos hi, hi, flipAt_apply_self, hc]
        have hval : x i0 = 0 ∨ x i0 = 1 := by
          generalize x i0 = a
          revert a
          decide
        rcases hval with hx | hx
        · rw [hx, show ((0 : ZMod 2) + 1) = 1 from by decide,
            if_neg (by decide : ¬((1 : ZMod 2) = 0)), if_pos rfl]
        · rw [hx, show ((1 : ZMod 2) + 1) = 0 from by decide, if_pos rfl,
            if_neg (by decide : ¬((1 : ZMod 2) = 0))]
          norm_num
      · rw [if_neg hi, flipAt_apply_of_ne (Ne.symm hi)]
    rw [SimpleGraph.lapMatrix_mulVec_apply, sum_neighbors, degree_hypercube]
    simp only [hflip]
    have hsum : ∑ i : Fin k, (if i = i0 then -c else c) = (k : ℝ) * c - 2 * c := by
      have hterm : ∀ i : Fin k, (if i = i0 then -c else c) = c + (if i = i0 then -2*c else 0) := by
        intro i
        by_cases hi : i = i0
        · simp [hi]; ring
        · simp [hi]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i0 (fun _ => -2*c), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, if_pos (Finset.mem_univ i0)]
      ring
    rw [hsum]
    simp only [Pi.smul_apply, smul_eq_mul]
    show (k : ℝ) * c - ((k : ℝ) * c - 2 * c) = 2 * c
    ring

/-- **Expander uniform gap witness.**

For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube
graph `Q_k` (on `2^k` vertices) is exactly `2`.  Since the bound `2` does not depend on
`k`, the family `(Q_k)_{k ≥ 1}` has a uniform spectral gap. -/
theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k → IsLeast {μ : ℝ | IsLapEigenvalue k μ ∧ μ ≠ 0} 2 := by
  intro k hk
  constructor
  · exact ⟨two_isLapEigenvalue hk, by norm_num⟩
  · rintro μ ⟨hev, hμ⟩
    exact two_le_of_isLapEigenvalue hμ hev

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/
lemma card_cube (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp [Cube, ZMod.card]

/-- **Uniform spectral gap.** There is a single positive constant (namely `2`), independent
of `k`, bounding below every nonzero Laplacian eigenvalue of every hypercube `Q_k`. -/
theorem hypercube_uniform_spectral_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ μ : ℝ, IsLapEigenvalue k μ → μ ≠ 0 → c ≤ μ :=
  ⟨2, by norm_num, fun _ _ _ hev hμ => two_le_of_isLapEigenvalue hμ hev⟩

end Frontier.Spectral

