/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/
noncomputable def finner (f g : ℕ →₀ ℂ) : ℂ :=
  ∑ i ∈ f.support, (starRingEnd ℂ) (f i) * g i

lemma finner_eq_sum (f g : ℕ →₀ ℂ) {s : Finset ℕ} (hs : f.support ⊆ s) :
    finner f g = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  refine Finset.sum_subset hs ?_
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi]
  simp

lemma finner_single_left (m : ℕ) (c : ℂ) (g : ℕ →₀ ℂ) :
    finner (Finsupp.single m c) g = (starRingEnd ℂ) c * g m := by
  rw [finner_eq_sum _ _ (Finsupp.support_single_subset (a := m) (b := c))]
  simp

lemma finner_add_left (f g h : ℕ →₀ ℂ) : finner (f + g) h = finner f h + finner g h := by
  classical
  have h1 : (f + g).support ⊆ f.support ∪ g.support := Finsupp.support_add
  rw [finner_eq_sum _ _ h1, finner_eq_sum f h Finset.subset_union_left,
    finner_eq_sum g h Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [add_mul]

lemma finner_smul_left (r : ℂ) (f g : ℕ →₀ ℂ) :
    finner (r • f) g = (starRingEnd ℂ) r * finner f g := by
  classical
  have h1 : (r • f).support ⊆ f.support := Finsupp.support_smul
  rw [finner_eq_sum _ _ h1, finner, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_assoc]

lemma finner_conj_symm (f g : ℕ →₀ ℂ) :
    (starRingEnd ℂ) (finner g f) = finner f g := by
  classical
  rw [finner_eq_sum g f Finset.subset_union_right (s := f.support ∪ g.support),
    finner_eq_sum f g Finset.subset_union_left (s := f.support ∪ g.support), map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_comm]

lemma finner_self_eq (f : ℕ →₀ ℂ) :
    finner f f = ((∑ i ∈ f.support, Complex.normSq (f i) : ℝ) : ℂ) := by
  rw [finner]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Complex.normSq_eq_conj_mul_self]

lemma finner_self_nonneg (f : ℕ →₀ ℂ) : 0 ≤ (finner f f).re := by
  rw [finner_self_eq]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

lemma finner_definite (f : ℕ →₀ ℂ) (h : finner f f = 0) : f = 0 := by
  rw [finner_self_eq] at h
  have hsum : ∑ i ∈ f.support, Complex.normSq (f i) = 0 := by exact_mod_cast h
  have hzero : ∀ i ∈ f.support, Complex.normSq (f i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).mp hsum
  ext i
  by_cases hi : i ∈ f.support
  · simpa using Complex.normSq_eq_zero.mp (hzero i hi)
  · simpa using Finsupp.notMem_support_iff.mp hi

/-- The Fock inner product, as an `Inner` structure. -/
noncomputable def fockInnerStruct : Inner ℂ (ℕ →₀ ℂ) := ⟨finner⟩

attribute [local instance] fockInnerStruct

/-- The inner product space core on finitely supported complex sequences. -/
noncomputable def fockCore : InnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  toInner := inferInstance
  conj_inner_symm := finner_conj_symm
  re_inner_nonneg := finner_self_nonneg
  add_left := finner_add_left
  smul_left x y r := finner_smul_left r x y
  definite := finner_definite

/-- The norm coming from the Fock inner product. -/
noncomputable def fockNormedAddCommGroup : NormedAddCommGroup (ℕ →₀ ℂ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (ℕ →₀ ℂ) _ _ _ fockCore

attribute [local instance] fockNormedAddCommGroup

/-- The Fock inner product space structure. -/
noncomputable def fockInnerProductSpace : InnerProductSpace ℂ (ℕ →₀ ℂ) :=
  InnerProductSpace.ofCore fockCore.toCore

attribute [local instance] fockInnerProductSpace

lemma inner_eq_finner (f g : ℕ →₀ ℂ) : (inner ℂ f g : ℂ) = finner f g := rfl

/-! ### The ladder operators -/

/-- Annihilation operator, as a function. -/
noncomputable def aFun (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (x.support.image (fun i => i - 1))
    (fun m => (Real.sqrt (m + 1) : ℂ) * x (m + 1))
    (by
      intro m hm
      have hx : x (m + 1) ≠ 0 := fun h => hm (by simp [h])
      exact Finset.mem_image.mpr ⟨m + 1, Finsupp.mem_support_iff.mpr hx, by simp⟩)

lemma aFun_apply (x : ℕ →₀ ℂ) (m : ℕ) :
    aFun x m = (Real.sqrt (m + 1) : ℂ) * x (m + 1) := rfl

/-- Creation operator, as a function. -/
noncomputable def adagFun (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (x.support.image (fun i => i + 1))
    (fun m => if m = 0 then 0 else (Real.sqrt m : ℂ) * x (m - 1))
    (by
      intro m hm
      by_cases h0 : m = 0
      · simp [h0] at hm
      · have hx : x (m - 1) ≠ 0 := fun h => hm (by simp [h0, h])
        refine Finset.mem_image.mpr ⟨m - 1, Finsupp.mem_support_iff.mpr hx, ?_⟩
        omega)

lemma adagFun_apply (x : ℕ →₀ ℂ) (m : ℕ) :
    adagFun x m = if m = 0 then 0 else (Real.sqrt m : ℂ) * x (m - 1) := rfl

/-- The annihilation operator as a linear map. -/
noncomputable def aOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) where
  toFun := aFun
  map_add' x y := by
    ext m; simp only [aFun_apply, Finsupp.add_apply, mul_add]
  map_smul' r x := by
    ext m
    simp only [aFun_apply, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The creation operator as a linear map. -/
noncomputable def adagOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) where
  toFun := adagFun
  map_add' x y := by
    ext m
    by_cases h : m = 0 <;>
      simp only [adagFun_apply, Finsupp.add_apply, h, if_true, if_false, mul_add, add_zero]
  map_smul' r x := by
    ext m
    by_cases h : m = 0
    · simp [adagFun_apply, h]
    · simp only [adagFun_apply, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul, h, if_false]
      ring

@[simp] lemma aOp_apply (x : ℕ →₀ ℂ) (m : ℕ) :
    aOp x m = (Real.sqrt (m + 1) : ℂ) * x (m + 1) := rfl

@[simp] lemma adagOp_apply (x : ℕ →₀ ℂ) (m : ℕ) :
    adagOp x m = if m = 0 then 0 else (Real.sqrt m : ℂ) * x (m - 1) := rfl

lemma aOp_single (m : ℕ) (c : ℂ) :
    aOp (Finsupp.single m c) = Finsupp.single (m - 1) ((Real.sqrt m : ℂ) * c) := by
  ext k
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]

lemma adagOp_single (m : ℕ) (c : ℂ) :
    adagOp (Finsupp.single m c) = Finsupp.single (m + 1) ((Real.sqrt (m + 1) : ℂ) * c) := by
  ext k
  by_cases h0 : k = 0
  · subst h0
    simp
  · by_cases hk : k = m + 1
    · subst hk
      have h1 : (m + 1) - 1 = m := by omega
      simp only [adagOp_apply, h0, if_false, h1, Finsupp.single_eq_same]
      push_cast
      ring
    · have hne : k - 1 ≠ m := by omega
      simp [h0, hk, hne]

/-! ### The canonical commutation relation and the adjoint property -/

theorem fock_ccr (x : ℕ →₀ ℂ) : aOp (adagOp x) - adagOp (aOp x) = x := by
  ext k
  have hk1 : (Real.sqrt ((k : ℝ) + 1) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ) = ((k : ℂ) + 1) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  by_cases h0 : k = 0
  · subst h0
    simp only [Finsupp.sub_apply, aOp_apply, adagOp_apply, if_true, sub_zero]
    norm_num
  · have hk0 : (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = (k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      norm_num
    have hsucc : k - 1 + 1 = k := by omega
    have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      have h1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [h1]; ring
    simp only [Finsupp.sub_apply, aOp_apply, adagOp_apply, h0, if_false, hsucc,
      Nat.add_sub_cancel]
    push_cast
    rw [← mul_assoc, hk1, hcast, ← mul_assoc, hk0]
    ring

theorem fock_adjoint (x y : ℕ →₀ ℂ) : finner (aOp x) y = finner x (adagOp y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [finner, map_zero]
  | add f g hf hg =>
      rw [map_add, finner_add_left, finner_add_left, hf, hg]
  | single m c =>
      rw [aOp_single, finner_single_left, finner_single_left, adagOp_apply]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · have h0 : m ≠ 0 := by omega
        simp only [h0, if_false, map_mul, Complex.conj_ofReal]
        ring

/-! ### Every Landau level is attained -/

theorem number_eigenvector (n : ℕ) :
    adagOp (aOp (Finsupp.single n (1 : ℂ))) = (n : ℂ) • Finsupp.single n (1 : ℂ) := by
  rw [aOp_single, adagOp_single, Finsupp.smul_single, smul_eq_mul, mul_one, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hsucc : n - 1 + 1 = n := by omega
    rw [hsucc]
    congr 1
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]
        norm_num
      rw [this]; ring
    rw [hcast, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num

theorem single_ne_zero (n : ℕ) : Finsupp.single n (1 : ℂ) ≠ 0 := by
  simp

/-- The Landau Hamiltonian `H = ℏ ω_c (a† a + 1/2)` on the Fock model. -/
noncomputable def fockH (hbar omegac : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omegac : ℝ) : ℂ) • (adagOp ∘ₗ aOp + (1 / 2 : ℂ) • LinearMap.id)

lemma fockH_apply (hbar omegac : ℝ) (x : ℕ →₀ ℂ) :
    fockH hbar omegac x = ((hbar * omegac : ℝ) : ℂ) • (adagOp (aOp x) + (1 / 2 : ℂ) • x) := rfl

/-- **The Landau spectrum of the Fock model.**  For `ℏ, ω_c > 0`, a complex number `E` is an
eigenvalue of `H = ℏ ω_c (a† a + 1/2)` if and only if `E = ℏ ω_c (n + 1/2)` for some `n : ℕ`.
The forward direction is the abstract theorem `Frontier.landau_levels`; the backward direction
exhibits the `n`-th number state as an eigenvector, so that all Landau levels really occur. -/
theorem fock_landau_spectrum (hbar omegac : ℝ) (hbar_pos : 0 < hbar) (homega_pos : 0 < omegac)
    (E : ℂ) :
    (∃ v : ℕ →₀ ℂ, v ≠ 0 ∧ fockH hbar omegac v = E • v) ↔
      ∃ n : ℕ, E = ((hbar * omegac : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) := by
  constructor
  · rintro ⟨v, hv, hEv⟩
    exact Frontier.landau_levels aOp adagOp
      (fun x y => by rw [inner_eq_finner, inner_eq_finner]; exact fock_adjoint x y)
      fock_ccr hbar omegac hbar_pos homega_pos (fockH hbar omegac)
      (fockH_apply hbar omegac) hv hEv
  · rintro ⟨n, rfl⟩
    refine ⟨Finsupp.single n (1 : ℂ), single_ne_zero n, ?_⟩
    rw [fockH_apply, number_eigenvector n]
    module

/-- **Consistency of the Landau-level hypotheses.**  There is an inner product space carrying
operators `a`, `a†` which are mutually adjoint and satisfy the canonical commutation
relation `[a, a†] = 1`; hence `Frontier.landau_levels` is not vacuous. -/
theorem landau_hypotheses_consistent :
    (∀ x y : ℕ →₀ ℂ, (inner ℂ (aOp x) y : ℂ) = (inner ℂ x (adagOp y) : ℂ)) ∧
      (∀ x : ℕ →₀ ℂ, aOp (adagOp x) - adagOp (aOp x) = x) :=
  ⟨fun x y => by rw [inner_eq_finner, inner_eq_finner]; exact fock_adjoint x y, fock_ccr⟩

end Frontier.Fock

/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Frontier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- If `B` acts as the adjoint of `A` and `v` is an eigenvector of the number operator
`N = B ∘ A` with eigenvalue `μ`, then `μ` is a nonnegative real number
(indeed `μ = ‖A v‖² / ‖v‖²`). -/
theorem number_eigenvalue_nonneg (A B : V →ₗ[ℂ] V)
    (hadj : ∀ x y : V, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    {v : V} (hv : v ≠ 0) {μ : ℂ} (h : B (A v) = μ • v) :
    ∃ r : ℝ, 0 ≤ r ∧ μ = (r : ℂ) := by
  have hvv : (‖v‖ : ℂ) ^ 2 ≠ 0 := by
    simpa [pow_eq_zero_iff] using (norm_ne_zero_iff.mpr hv)
  have key : ((‖A v‖ : ℂ)) ^ 2 = μ * ((‖v‖ : ℂ)) ^ 2 := by
    have h1 : ⟪A v, A v⟫_ℂ = ⟪v, B (A v)⟫_ℂ := hadj _ _
    rw [h, inner_smul_right] at h1
    rw [inner_self_eq_norm_sq_to_K] at h1
    rw [inner_self_eq_norm_sq_to_K] at h1
    exact_mod_cast h1
  refine ⟨‖A v‖ ^ 2 / ‖v‖ ^ 2, by positivity, ?_⟩
  have : μ = ((‖A v‖ : ℂ)) ^ 2 / ((‖v‖ : ℂ)) ^ 2 := by
    rw [key, mul_div_assoc, div_self hvv, mul_one]
  rw [this]
  push_cast
  ring

/-- Lowering step: if `[A, B] = 1` and `v` is an eigenvector of `N = B ∘ A` with eigenvalue `μ`,
then `A v` is an eigenvector of `N` with eigenvalue `μ - 1` (or is zero). -/
theorem number_ladder_down (A B : V →ₗ[ℂ] V)
    (hcomm : ∀ x : V, A (B x) - B (A x) = x)
    {v : V} {μ : ℂ} (h : B (A v) = μ • v) :
    B (A (A v)) = (μ - 1) • A v := by
  have h1 := hcomm (A v)
  have h2 : A (B (A v)) = μ • A v := by rw [h, map_smul]
  rw [h2] at h1
  have h4 : μ • A v = A v + B (A (A v)) := sub_eq_iff_eq_add.mp h1
  have : B (A (A v)) = μ • A v - A v := by
    rw [h4]; abel
  rw [this, sub_smul, one_smul]

/-- Iterated lowering: `Aⁿ v` is an eigenvector of `N = B ∘ A` with eigenvalue `μ - n`
(or is zero). -/
theorem number_ladder_iterate (A B : V →ₗ[ℂ] V)
    (hcomm : ∀ x : V, A (B x) - B (A x) = x)
    {v : V} {μ : ℂ} (h : B (A v) = μ • v) (n : ℕ) :
    B (A ((A : V → V)^[n] v)) = (μ - n) • (A : V → V)^[n] v := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have := number_ladder_down A B hcomm ih
      rw [Function.iterate_succ_apply' (f := (A : V → V))]
      rw [this]
      push_cast
      ring_nf

/-- **Quantization of the number operator.**  If `B` is the adjoint of `A` and `[A, B] = 1`,
then every eigenvalue of the number operator `N = B ∘ A` is a natural number. -/
theorem number_eigenvalue_nat (A B : V →ₗ[ℂ] V)
    (hadj : ∀ x y : V, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hcomm : ∀ x : V, A (B x) - B (A x) = x)
    {v : V} (hv : v ≠ 0) {μ : ℂ} (h : B (A v) = μ • v) :
    ∃ n : ℕ, μ = (n : ℂ) := by
  by_cases hex : ∃ n : ℕ, (A : V → V)^[n] v = 0
  · classical
    have hne0 : Nat.find hex ≠ 0 := by
      intro h0
      have hs := Nat.find_spec hex
      rw [h0] at hs
      exact hv (by simpa using hs)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne0
    have hw : (A : V → V)^[m] v ≠ 0 := Nat.find_min hex (by omega)
    have hzero : A ((A : V → V)^[m] v) = 0 := by
      have hs := Nat.find_spec hex
      rw [hm, Function.iterate_succ_apply' (f := (A : V → V))] at hs
      exact hs
    have hchain := number_ladder_iterate A B hcomm h m
    rw [hzero, map_zero] at hchain
    have hmu : μ - (m : ℂ) = 0 := by
      rcases smul_eq_zero.mp hchain.symm with h1 | h1
      · exact h1
      · exact absurd h1 hw
    exact ⟨m, by linear_combination hmu⟩
  · push_neg at hex
    have hbound : ∀ n : ℕ, (n : ℝ) ≤ μ.re := by
      intro n
      obtain ⟨r, hr0, hr⟩ :=
        number_eigenvalue_nonneg A B hadj (hex n) (number_ladder_iterate A B hcomm h n)
      have : μ.re - n = r := by
        have := congrArg Complex.re hr
        simpa using this
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt μ.re
    exact absurd (hbound n) (not_le.mpr hn)

/-- **Landau levels.**

A charged particle in a uniform magnetic field is described, after separating the cyclotron
degree of freedom, by the Hamiltonian `H = ℏ ω_c (a† a + 1/2)`, where the ladder operators
satisfy the canonical commutation relation `[a, a†] = 1` and `a†` is the adjoint of `a`.

This theorem says that any eigenvalue `E` of such a Hamiltonian (on a nonzero eigenvector)
is of the form `E = ℏ ω_c (n + 1/2)` for some natural number `n`: the Landau level spectrum. -/
theorem landau_levels (a adag : V →ₗ[ℂ] V)
    (hadj : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, adag y⟫_ℂ)
    (hcomm : ∀ x : V, a (adag x) - adag (a x) = x)
    (hbar omegac : ℝ) (hbar_pos : 0 < hbar) (homega_pos : 0 < omegac)
    (H : V →ₗ[ℂ] V)
    (hH : ∀ x : V, H x = ((hbar * omegac : ℝ) : ℂ) • (adag (a x) + (1 / 2 : ℂ) • x))
    {v : V} (hv : v ≠ 0) {E : ℂ} (hE : H v = E • v) :
    ∃ n : ℕ, E = ((hbar * omegac : ℝ) : ℂ) * (n + 1 / 2) := by
  set c : ℂ := ((hbar * omegac : ℝ) : ℂ) with hc_def
  have hc : c ≠ 0 := by
    simp only [hc_def, ne_eq, Complex.ofReal_eq_zero]
    positivity
  have h1 : c • (adag (a v) + (1 / 2 : ℂ) • v) = E • v := by rw [← hH v]; exact hE
  have h3 : c • adag (a v) = (E - c / 2) • v := by
    have h1' : c • adag (a v) + (c * (1 / 2 : ℂ)) • v = E • v := by
      rw [← smul_smul, ← smul_add]; exact h1
    rw [sub_smul, ← h1']
    module
  have h2 : adag (a v) = ((E - c / 2) / c) • v := by
    apply smul_right_injective V hc
    show c • adag (a v) = c • (((E - c / 2) / c) • v)
    rw [h3, smul_smul]
    congr 1
    field_simp
  obtain ⟨n, hn⟩ := number_eigenvalue_nat a adag hadj hcomm hv h2
  refine ⟨n, ?_⟩
  field_simp at hn
  linear_combination (1 / 2 : ℂ) * hn

end Frontier

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

