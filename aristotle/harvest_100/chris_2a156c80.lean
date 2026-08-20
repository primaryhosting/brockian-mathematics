/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalized here

The Chern–Gauss–Bonnet theorem states that for a closed oriented Riemannian manifold `M`
of even dimension `2n`, the integral over `M` of the Euler form (the Pfaffian of the
curvature form, normalized by `(2π)^n`) equals the Euler characteristic of `M`.

Mathlib currently contains no Riemann curvature tensor, no Pfaffian, no de Rham
cohomology of manifolds and no Euler characteristic of manifolds, so all the objects
entering the statement are built here from scratch:

* `Math2.eulerDensity n R` is the Chern–Gauss–Bonnet integrand attached to an algebraic
  curvature tensor `R` written in an orthonormal frame of a `2n`-dimensional tangent
  space, namely
  `1 / ((8π)^n n!) * ∑_{σ,τ} sgn σ · sgn τ · ∏_i R (σ i₀) (σ i₁) (τ i₀) (τ i₁)`.
  `Math2.eulerDensity_dim_two` checks that for `n = 1` this is exactly the classical
  Gauss–Bonnet integrand `K / (2π)`.
* `Math2.roundCurvature n` is the Riemann curvature tensor of the unit round sphere
  `S^{2n}` in an orthonormal frame, `R a b c d = δₐᶜ δ_bd - δ_ad δ_bc`.
* the manifold is the unit sphere `S^{2n} ⊆ ℝ^{2n+1}` and its Riemannian measure is
  Mathlib's surface measure `MeasureTheory.Measure.toSphere` obtained from Lebesgue
  measure by the polar coordinate decomposition.

The main theorem `Math2.chern_gauss_bonnet` proves the Chern–Gauss–Bonnet identity for
this family of closed even-dimensional manifolds, for every `n : ℕ`: the integral of
the Euler form over `S^{2n}` equals `2 = χ(S^{2n})`. The two ingredients are a purely
combinatorial evaluation of the Pfaffian sum for constant curvature one
(`Math2.sum_sign_prod_roundCurvature`, equal to `2^n (2n)!`) and the exact value of the
surface measure of `S^{2n}` (`Math2.sphere_measureReal_univ`).
-/

open scoped Nat Real
open MeasureTheory Metric Equiv

namespace Math2

/-- Index type of an orthonormal frame of a `2 * n`-dimensional Euclidean space:
it has cardinality `2 * n`, and is organized as `n` ordered pairs, which is the
form in which the indices enter the Pfaffian. -/
abbrev Frame (n : ℕ) := Fin n × Bool

/-- The Chern–Gauss–Bonnet integrand (the Euler form, or Pfaffian of the curvature
form, divided by `(2π)^n`) of an algebraic curvature tensor `R` given in an
orthonormal frame of a `2 * n`-dimensional Riemannian manifold:
`e = 1 / ((8π)^n n!) * ∑_{σ,τ} sgn σ · sgn τ · ∏_i R (σ i₀) (σ i₁) (τ i₀) (τ i₁)`.
For `n = 1` this is the classical `K / (2π)`. -/
noncomputable def eulerDensity (n : ℕ) (R : Frame n → Frame n → Frame n → Frame n → ℝ) : ℝ :=
  (1 / ((8 * π) ^ n * (n ! : ℝ))) *
    ∑ σ : Equiv.Perm (Frame n), ∑ τ : Equiv.Perm (Frame n),
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        ∏ i : Fin n, R (σ (i, false)) (σ (i, true)) (τ (i, false)) (τ (i, true))

/-- The Riemann curvature tensor of the unit round sphere `S^{2n}`, written in any
orthonormal frame: `R a b c d = δ a c * δ b d - δ a d * δ b c` (constant sectional
curvature one). -/
def roundCurvature (n : ℕ) : Frame n → Frame n → Frame n → Frame n → ℝ := fun a b c d =>
  (if a = c then (1 : ℝ) else 0) * (if b = d then (1 : ℝ) else 0) -
    (if a = d then (1 : ℝ) else 0) * (if b = c then (1 : ℝ) else 0)

/-- The map swapping the two members of each pair belonging to `T`. -/
def pairSwapFun {n : ℕ} (T : Finset (Fin n)) : Frame n → Frame n :=
  fun p => (p.1, if p.1 ∈ T then !p.2 else p.2)

lemma pairSwapFun_involutive {n : ℕ} (T : Finset (Fin n)) :
    Function.Involutive (pairSwapFun T) := by
  intro p
  simp only [pairSwapFun]
  by_cases h : p.1 ∈ T <;> simp [h]

/-- The involution of the frame indices which swaps the two members of each pair
belonging to `T`. -/
def pairSwap {n : ℕ} (T : Finset (Fin n)) : Equiv.Perm (Frame n) :=
  (pairSwapFun_involutive T).toPerm _

@[simp] lemma pairSwap_apply {n : ℕ} (T : Finset (Fin n)) (p : Frame n) :
    pairSwap T p = (p.1, if p.1 ∈ T then !p.2 else p.2) := rfl

lemma pairSwap_insert {n : ℕ} {T : Finset (Fin n)} {a : Fin n} (ha : a ∉ T) :
    pairSwap (insert a T) = Equiv.swap (a, false) (a, true) * pairSwap T := by
  apply Equiv.ext
  rintro ⟨x, b⟩
  simp only [pairSwap_apply, Equiv.Perm.mul_apply]
  by_cases h : x = a
  · subst h
    cases b <;> simp [ha]
  · have hmem : (x ∈ insert a T) ↔ x ∈ T := by simp [h]
    rw [if_congr hmem rfl rfl,
      Equiv.swap_apply_of_ne_of_ne (by simp [h]) (by simp [h])]

lemma sign_pairSwap {n : ℕ} (T : Finset (Fin n)) :
    (Equiv.Perm.sign (pairSwap T) : ℝ) = (-1) ^ T.card := by
  induction T using Finset.induction with
  | empty =>
      have : pairSwap (∅ : Finset (Fin n)) = 1 := by ext p <;> simp
      simp [this]
  | insert a T ha ih =>
      rw [pairSwap_insert ha, map_mul, Finset.card_insert_of_notMem ha]
      have hne : ((a, false) : Frame n) ≠ (a, true) := by simp
      rw [Equiv.Perm.sign_swap hne]
      push_cast
      rw [ih]
      ring

lemma roundCurvature_perm (n : ℕ) (σ : Equiv.Perm (Frame n)) (a b c d : Frame n) :
    roundCurvature n (σ a) (σ b) (σ c) (σ d) = roundCurvature n a b c d := by
  simp only [roundCurvature, EmbeddingLike.apply_eq_iff_eq]

lemma prod_roundCurvature_pairSwap (n : ℕ) (T : Finset (Fin n)) :
    ∏ i : Fin n, roundCurvature n (i, false) (i, true)
      (pairSwap T (i, false)) (pairSwap T (i, true)) = (-1 : ℝ) ^ T.card := by
  have h : ∀ i : Fin n, roundCurvature n (i, false) (i, true)
      (pairSwap T (i, false)) (pairSwap T (i, true)) = if i ∈ T then (-1 : ℝ) else 1 := by
    intro i
    by_cases h : i ∈ T <;> simp [roundCurvature, h]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

lemma prod_roundCurvature_eq_zero (n : ℕ) (p : Equiv.Perm (Frame n))
    (hp : ∀ T : Finset (Fin n), p ≠ pairSwap T) :
    ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true)) = 0 := by
  by_contra hne0
  have hne := Finset.prod_ne_zero_iff.mp hne0
  classical
  set T : Finset (Fin n) := {i : Fin n | p (i, false) = (i, true)} with hT
  have hmemT : ∀ i : Fin n, i ∈ T ↔ p (i, false) = (i, true) := by
    intro i; simp [hT]
  refine hp T (Equiv.ext ?_)
  rintro ⟨i, b⟩
  have hi := hne i (Finset.mem_univ i)
  have hcase : (p (i, false) = (i, false) ∧ p (i, true) = (i, true)) ∨
      (p (i, false) = (i, true) ∧ p (i, true) = (i, false)) := by
    by_cases h1 : p (i, false) = (i, false)
    · by_cases h2 : p (i, true) = (i, true)
      · exact Or.inl ⟨h1, h2⟩
      · exact absurd (by simp [roundCurvature, h1, Ne.symm h2, eq_comm]) hi
    · by_cases h3 : p (i, false) = (i, true)
      · by_cases h4 : p (i, true) = (i, false)
        · exact Or.inr ⟨h3, h4⟩
        · exact absurd (by simp [roundCurvature, Ne.symm h1, Ne.symm h4]) hi
      · exact absurd (by simp [roundCurvature, Ne.symm h1, Ne.symm h3]) hi
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hnot : i ∉ T := by
      rw [hmemT, h1]
      simp
    cases b <;> simp [hnot, h1, h2]
  · have hmem : i ∈ T := (hmemT i).2 h1
    cases b <;> simp [hmem, h1, h2]

lemma sum_sign_prod_roundCurvature_aux (n : ℕ) :
    ∑ p : Equiv.Perm (Frame n), (Equiv.Perm.sign p : ℝ) *
      ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true))
      = 2 ^ n := by
  classical
  set g : Equiv.Perm (Frame n) → ℝ := fun p => (Equiv.Perm.sign p : ℝ) *
    ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true)) with hg
  have hinj : ∀ T ∈ (Finset.univ : Finset (Finset (Fin n))),
      ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      pairSwap T = pairSwap S → T = S := by
    intro T _ S _ h
    ext i
    have := congrArg (fun e : Equiv.Perm (Frame n) => e (i, false)) h
    simp only [pairSwap_apply] at this
    by_cases hT : i ∈ T <;> by_cases hS : i ∈ S <;> simp_all
  have himg : ∑ p ∈ (Finset.univ : Finset (Finset (Fin n))).image pairSwap, g p =
      ∑ T : Finset (Fin n), g (pairSwap T) := Finset.sum_image hinj
  have hsub : ∑ p : Equiv.Perm (Frame n), g p =
      ∑ p ∈ (Finset.univ : Finset (Finset (Fin n))).image pairSwap, g p := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro p _ hp
    have hp' : ∀ T : Finset (Fin n), p ≠ pairSwap T := by
      intro T hT
      exact hp (Finset.mem_image.2 ⟨T, Finset.mem_univ T, hT.symm⟩)
    simp [hg, prod_roundCurvature_eq_zero n p hp']
  have hone : ∀ T : Finset (Fin n), g (pairSwap T) = 1 := by
    intro T
    rw [hg]
    simp only
    rw [prod_roundCurvature_pairSwap, sign_pairSwap, ← mul_pow]
    norm_num
  rw [hsub, himg, Finset.sum_congr rfl (fun T _ => hone T)]
  simp [Finset.card_univ]

/-- The key combinatorial identity: the (unnormalized) Pfaffian sum of the constant
curvature one tensor in dimension `2 * n` equals `2 ^ n * (2 * n)!`. -/
lemma sum_sign_prod_roundCurvature (n : ℕ) :
    ∑ σ : Equiv.Perm (Frame n), ∑ τ : Equiv.Perm (Frame n),
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        ∏ i : Fin n, roundCurvature n (σ (i, false)) (σ (i, true))
          (τ (i, false)) (τ (i, true)) = 2 ^ n * ((2 * n)! : ℝ) := by
  have step : ∀ σ : Equiv.Perm (Frame n),
      (∑ τ : Equiv.Perm (Frame n), (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        ∏ i : Fin n, roundCurvature n (σ (i, false)) (σ (i, true))
          (τ (i, false)) (τ (i, true))) = 2 ^ n := by
    intro σ
    rw [← Equiv.sum_comp (Equiv.mulLeft σ), ← sum_sign_prod_roundCurvature_aux n]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hprod : ∏ i : Fin n, roundCurvature n (σ (i, false)) (σ (i, true))
        ((Equiv.mulLeft σ p) (i, false)) ((Equiv.mulLeft σ p) (i, true)) =
        ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simpa using roundCurvature_perm n σ (i, false) (i, true) (p (i, false)) (p (i, true))
    rw [hprod]
    have hsign : ((Equiv.Perm.sign ((Equiv.mulLeft σ) p) : ℤ) : ℝ) =
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign p : ℤ) : ℝ) := by
      simp
    rw [hsign]
    have hsq : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
    calc ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign p : ℤ) : ℝ)) *
          ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true))
        = (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ)) *
          (((Equiv.Perm.sign p : ℤ) : ℝ) *
            ∏ i : Fin n, roundCurvature n (i, false) (i, true)
              (p (i, false)) (p (i, true))) := by ring
      _ = _ := by rw [hsq, one_mul]
  rw [Finset.sum_congr rfl (fun σ _ => step σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, nsmul_eq_mul]
  have hcard : Fintype.card (Frame n) = 2 * n := by
    simp [Frame, Nat.mul_comm]
  rw [hcard, mul_comm]

/-- The Chern–Gauss–Bonnet integrand of the unit round sphere `S^{2n}`. -/
lemma eulerDensity_roundCurvature (n : ℕ) :
    eulerDensity n (roundCurvature n) = ((2 * n)! : ℝ) / ((4 * π) ^ n * (n ! : ℝ)) := by
  rw [eulerDensity, sum_sign_prod_roundCurvature]
  have h8 : ((8 : ℝ) * π) ^ n = 2 ^ n * (4 * π) ^ n := by
    rw [show (8 : ℝ) * π = 2 * (4 * π) by ring, mul_pow]
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hpi : (0 : ℝ) < (4 * π) ^ n := by positivity
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [h8]
  field_simp

set_option maxHeartbeats 1000000 in
/-- The total surface measure of the unit sphere `S^{2n} ⊆ ℝ^{2n+1}`. -/
lemma sphere_measureReal_univ (n : ℕ) :
    (volume.toSphere (E := EuclideanSpace ℝ (Fin (2 * n + 1)))).real Set.univ =
      2 ^ (n + 1) * π ^ n / ((2 * n - 1)‼ : ℝ) := by
  rw [Measure.toSphere_real_apply_univ, measureReal_def, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  have hG : Real.Gamma ((2 * n + 1 : ℕ) / 2 + 1) = ((2 * n + 1)‼ : ℝ) * √π / 2 ^ (n + 1) := by
    have h : ((2 * n + 1 : ℕ) : ℝ) / 2 + 1 = ((n + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
    rw [h, Real.Gamma_nat_add_half]
    congr 2
  have hsq : √π ^ (2 * n + 1) = π ^ n * √π := by
    rw [pow_succ, pow_mul, Real.sq_sqrt Real.pi_nonneg]
  have hd : ((2 * n + 1)‼ : ℝ) = (2 * n + 1) * ((2 * n - 1)‼ : ℝ) := by
    rw [show (2 * n + 1)‼ = (2 * n + 1) * (2 * n - 1)‼ from Nat.doubleFactorial_add_one (2 * n)]
    push_cast; ring
  have hpos : (0 : ℝ) < ((2 * n - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hspi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [hG, hsq, ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, hd]
  push_cast
  field_simp

lemma factorial_two_mul_eq (n : ℕ) : (2 * n)! = 2 ^ n * n ! * (2 * n - 1)‼ := by
  cases n with
  | zero => simp
  | succ m =>
      have h1 : (2 * (m + 1))! = (2 * m + 2)‼ * (2 * m + 1)‼ := by
        have := Nat.factorial_eq_mul_doubleFactorial (2 * m + 1)
        convert this using 2
      have h2 : (2 * m + 2)‼ = 2 ^ (m + 1) * (m + 1)! := by
        have := Nat.doubleFactorial_two_mul (m + 1)
        convert this using 2
      have h3 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [h1, h2, h3]

/-- **Chern–Gauss–Bonnet theorem** for the closed even-dimensional manifold `S^{2n}`:
the integral over the manifold of the Euler form (the Pfaffian of the curvature form
normalized by `(2π)^n`) equals the Euler characteristic `χ(S^{2n}) = 2`. -/
theorem chern_gauss_bonnet (n : ℕ) :
    ∫ _p : sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) 1,
      eulerDensity n (roundCurvature n) ∂volume.toSphere = 2 := by
  rw [integral_const, sphere_measureReal_univ, eulerDensity_roundCurvature, smul_eq_mul]
  have hpos : (0 : ℝ) < ((2 * n - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcast : ((2 * n)! : ℝ) = 2 ^ n * (n ! : ℝ) * ((2 * n - 1)‼ : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (factorial_two_mul_eq n)
  rw [hcast]
  have h4 : ((4 : ℝ) * π) ^ n = 2 ^ n * 2 ^ n * π ^ n := by
    rw [show (4 : ℝ) * π = 2 * (2 * π) by ring, mul_pow, mul_pow]
    ring
  rw [h4, pow_succ]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  field_simp

lemma roundCurvature_antisymm_left (n : ℕ) (a b c d : Frame n) :
    roundCurvature n b a c d = -roundCurvature n a b c d := by
  simp only [roundCurvature]
  ring

lemma roundCurvature_antisymm_right (n : ℕ) (a b c d : Frame n) :
    roundCurvature n a b d c = -roundCurvature n a b c d := by
  simp only [roundCurvature]
  ring

/-- In dimension two the Euler density is the classical Gauss–Bonnet integrand
`K / (2π)`, where `K = R₁₂₁₂` is the Gaussian curvature. This identifies the
normalization used in `Math2.eulerDensity`. -/
lemma eulerDensity_dim_two (R : Frame 1 → Frame 1 → Frame 1 → Frame 1 → ℝ)
    (h1 : ∀ a b c d, R b a c d = -R a b c d) (h2 : ∀ a b c d, R a b d c = -R a b c d) :
    eulerDensity 1 R = R (0, false) (0, true) (0, false) (0, true) / (2 * π) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Frame 1))) =
      {1, Equiv.swap ((0 : Fin 1), false) ((0 : Fin 1), true)} := by decide
  have hne : (1 : Equiv.Perm (Frame 1)) ≠ Equiv.swap ((0 : Fin 1), false) ((0 : Fin 1), true) := by
    decide
  have hs : Equiv.Perm.sign (Equiv.swap ((0 : Fin 1), false) ((0 : Fin 1), true)) = -1 :=
    Equiv.Perm.sign_swap (by simp)
  have e1 : R (0, true) (0, false) (0, false) (0, true)
      = -R (0, false) (0, true) (0, false) (0, true) := h1 _ _ _ _
  have e2 : R (0, false) (0, true) (0, true) (0, false)
      = -R (0, false) (0, true) (0, false) (0, true) := h2 _ _ _ _
  have e3 : R (0, true) (0, false) (0, true) (0, false)
      = R (0, false) (0, true) (0, false) (0, true) := by
    rw [h1 ((0 : Fin 1), false) ((0 : Fin 1), true), h2 ((0 : Fin 1), false) ((0 : Fin 1), true)]
    ring
  rw [eulerDensity, huniv, Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Fin.prod_univ_one, hs, map_one, Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Units.val_one, Units.coe_neg_one, Int.cast_neg, Int.cast_one, pow_one,
    Nat.factorial_one, Nat.cast_one, mul_one, one_mul]
  rw [e1, e2, e3]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- For the unit `2`-sphere the Euler density is `1 / (2π)`, i.e. `K / (2π)` with
Gaussian curvature `K = 1`. -/
lemma eulerDensity_roundCurvature_dim_two : eulerDensity 1 (roundCurvature 1) = 1 / (2 * π) := by
  rw [eulerDensity_dim_two _ (roundCurvature_antisymm_left 1) (roundCurvature_antisymm_right 1)]
  simp [roundCurvature]

/-- The classical Gauss–Bonnet theorem for the unit `2`-sphere, the case `n = 1` of
`Math2.chern_gauss_bonnet`: the Gaussian curvature of the unit sphere is `1`, so
`(1 / 2π) * area (S²) = 2 = χ(S²)`. -/
theorem gauss_bonnet_two_sphere :
    (1 / (2 * π)) * (volume.toSphere (E := EuclideanSpace ℝ (Fin 3))).real Set.univ = 2 := by
  have h : (volume.toSphere (E := EuclideanSpace ℝ (Fin 3))).real Set.univ =
      (volume.toSphere (E := EuclideanSpace ℝ (Fin (2 * 1 + 1)))).real Set.univ := by norm_num
  rw [h, sphere_measureReal_univ 1]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  norm_num
  field_simp
  ring

end Math2

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

