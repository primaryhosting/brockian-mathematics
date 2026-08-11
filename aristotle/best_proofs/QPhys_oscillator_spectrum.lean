import RequestProject.Main

/-!
# A concrete model: the Fock space of finitely supported sequences

This file constructs an explicit `QPhys.LadderSystem`, showing that the hypotheses of
`QPhys.oscillator_spectrum` are consistent (non-vacuous).

The state space is `ℕ →₀ ℂ`, the space of finitely supported complex sequences,
with the usual `ℓ²` inner product `⟪f, g⟫ = ∑ conj (f i) * g i`.  The basis vector
`|n⟩ = single n 1` plays the role of the `n`-th excited state, and the ladder operators
act by `a |n⟩ = √n |n-1⟩`, `a† |n⟩ = √(n+1) |n+1⟩`.
-/

open scoped InnerProductSpace

namespace QPhys

namespace Fock

/-- The `ℓ²` inner product on finitely supported complex sequences. -/
noncomputable def fockInner (f g : ℕ →₀ ℂ) : ℂ :=
  ∑ i ∈ f.support ∪ g.support, (starRingEnd ℂ) (f i) * g i

lemma fockInner_eq_sum (f g : ℕ →₀ ℂ) {s : Finset ℕ} (hf : f.support ⊆ s) (hg : g.support ⊆ s) :
    fockInner f g = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  refine Finset.sum_subset (Finset.union_subset hf hg) ?_
  intro i _ hi
  simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, ne_eq, not_not] at hi
  rw [hi.1]
  simp

/-- The inner product space core structure on `ℕ →₀ ℂ`. -/
noncomputable def fockCore : InnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  inner := fockInner
  conj_inner_symm f g := by
    rw [fockInner_eq_sum g f Finset.subset_union_right Finset.subset_union_left,
        fockInner_eq_sum f g Finset.subset_union_left Finset.subset_union_right, map_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  re_inner_nonneg f := by
    show 0 ≤ (fockInner f f).re
    rw [fockInner_eq_sum f f (Finset.Subset.refl _) (Finset.Subset.refl _), Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul]
    nlinarith [sq_nonneg (f i).re, sq_nonneg (f i).im]
  add_left f g h := by
    show fockInner (f + g) h = fockInner f h + fockInner g h
    have h1 : (f + g).support ⊆ f.support ∪ g.support ∪ h.support :=
      Finsupp.support_add.trans Finset.subset_union_left
    have h2 : f.support ⊆ f.support ∪ g.support ∪ h.support :=
      Finset.subset_union_left.trans Finset.subset_union_left
    have h3 : g.support ⊆ f.support ∪ g.support ∪ h.support :=
      Finset.subset_union_right.trans Finset.subset_union_left
    have h4 : h.support ⊆ f.support ∪ g.support ∪ h.support := Finset.subset_union_right
    rw [fockInner_eq_sum (f + g) h h1 h4, fockInner_eq_sum f h h2 h4,
      fockInner_eq_sum g h h3 h4, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Finsupp.add_apply]; ring
  smul_left f g r := by
    show fockInner (r • f) g = (starRingEnd ℂ) r * fockInner f g
    have h1 : (r • f).support ⊆ f.support ∪ g.support :=
      Finsupp.support_smul.trans Finset.subset_union_left
    rw [fockInner_eq_sum (r • f) g h1 Finset.subset_union_right,
      fockInner_eq_sum f g Finset.subset_union_left Finset.subset_union_right,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Finsupp.smul_apply]; ring
  definite f hf := by
    have hf' : fockInner f f = 0 := hf
    have h0 : ∑ i ∈ f.support, Complex.normSq (f i) = 0 := by
      have h5 := congrArg Complex.re hf'
      rw [fockInner_eq_sum f f (Finset.Subset.refl _) (Finset.Subset.refl _), Complex.re_sum] at h5
      simpa [Complex.mul_re, Complex.normSq_apply] using h5
    refine Finsupp.ext fun i => ?_
    by_cases hi : i ∈ f.support
    · have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (f j))).mp h0 i hi
      simpa using Complex.normSq_eq_zero.mp this
    · simpa using hi

noncomputable instance : NormedAddCommGroup (ℕ →₀ ℂ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (ℕ →₀ ℂ) _ _ _ fockCore

noncomputable instance : InnerProductSpace ℂ (ℕ →₀ ℂ) := InnerProductSpace.ofCore fockCore.1

lemma inner_def (f g : ℕ →₀ ℂ) : ⟪f, g⟫_ℂ = fockInner f g := rfl

lemma inner_single_left (i : ℕ) (a : ℂ) (g : ℕ →₀ ℂ) :
    ⟪Finsupp.single i a, g⟫_ℂ = (starRingEnd ℂ) a * g i := by
  rw [inner_def, fockInner_eq_sum (Finsupp.single i a) g
    (Finsupp.support_single_subset.trans (by simp)) (Finset.subset_insert i g.support)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg (Ne.symm hj)]
    simp
  · intro hi
    simp at hi

/-- The weight `√n` appearing in the ladder operators. -/
noncomputable def wt (n : ℕ) : ℂ := (Real.sqrt n : ℂ)

lemma wt_mul_self (n : ℕ) : wt n * wt n = (n : ℂ) := by
  simp only [wt, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Complex.ofReal_natCast]

lemma wt_zero : wt 0 = 0 := by simp [wt]

lemma conj_wt (n : ℕ) : (starRingEnd ℂ) (wt n) = wt n := by simp [wt]

/-- The annihilation operator: `a |n⟩ = √n |n-1⟩`. -/
noncomputable def lower : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => LinearMap.toSpanSingleton ℂ (ℕ →₀ ℂ) (Finsupp.single (n - 1) (wt n))

/-- The creation operator: `a† |n⟩ = √(n+1) |n+1⟩`. -/
noncomputable def raise : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n =>
    LinearMap.toSpanSingleton ℂ (ℕ →₀ ℂ) (Finsupp.single (n + 1) (wt (n + 1)))

lemma lower_single (m : ℕ) (c : ℂ) :
    lower (Finsupp.single m c) = Finsupp.single (m - 1) (c * wt m) := by
  simp [lower, LinearMap.toSpanSingleton_apply, Finsupp.smul_single, smul_eq_mul]

lemma raise_single (m : ℕ) (c : ℂ) :
    raise (Finsupp.single m c) = Finsupp.single (m + 1) (c * wt (m + 1)) := by
  simp [raise, LinearMap.toSpanSingleton_apply, Finsupp.smul_single, smul_eq_mul]

lemma comm_single (m : ℕ) (c : ℂ) :
    lower (raise (Finsupp.single m c)) - raise (lower (Finsupp.single m c)) =
      Finsupp.single m c := by
  rw [raise_single, lower_single, lower_single, raise_single]
  rcases m with _ | k
  · rw [show c * wt (0 + 1) * wt (0 + 1) = c by rw [mul_assoc, wt_mul_self]; norm_num,
      show c * wt 0 * wt (0 - 1 + 1) = 0 by rw [wt_zero]; ring, Finsupp.single_zero, sub_zero]
  · rw [show k + 1 + 1 - 1 = k + 1 from rfl, show k + 1 - 1 + 1 = k + 1 from rfl,
      mul_assoc, wt_mul_self, mul_assoc, wt_mul_self, ← Finsupp.single_sub]
    congr 1
    push_cast
    ring

lemma comm (x : ℕ →₀ ℂ) : lower (raise x) - raise (lower x) = x := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add]
    rw [show lower (raise f) + lower (raise g) - (raise (lower f) + raise (lower g)) =
      (lower (raise f) - raise (lower f)) + (lower (raise g) - raise (lower g)) by abel, hf, hg]
  · exact comm_single

lemma adjoint_single (m k : ℕ) (c d : ℂ) :
    ⟪lower (Finsupp.single m c), Finsupp.single k d⟫_ℂ =
      ⟪Finsupp.single m c, raise (Finsupp.single k d)⟫_ℂ := by
  rw [lower_single, raise_single, inner_single_left, inner_single_left,
    Finsupp.single_apply, Finsupp.single_apply]
  rcases m with _ | j
  · simp [wt_zero]
  · rw [show j + 1 - 1 = j from rfl]
    by_cases h : k = j
    · subst h
      rw [if_pos rfl, if_pos rfl, map_mul, conj_wt]
      ring
    · rw [if_neg h, if_neg (by omega : ¬(k + 1 = j + 1))]
      ring

lemma adjoint (x y : ℕ →₀ ℂ) : ⟪lower x, y⟫_ℂ = ⟪x, raise y⟫_ℂ := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, inner_add_left, hf, hg]
  · intro m c
    refine Finsupp.induction_linear y ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add, inner_add_right, hf, hg]
    · intro k d
      exact adjoint_single m k c d

/-- The concrete ladder system on the Fock space `ℕ →₀ ℂ`. -/
noncomputable def ladder : LadderSystem (ℕ →₀ ℂ) where
  lower := lower
  raise := raise
  adjoint := adjoint
  comm := comm
  vacuum := Finsupp.single 0 1
  vacuum_ne_zero := by
    simp [Finsupp.single_eq_zero]
  lower_vacuum := by
    rw [lower_single]
    simp [wt_zero]

end Fock

/-- The hypotheses of `QPhys.oscillator_spectrum` are satisfiable: there is a concrete
ladder system, on the Fock space of finitely supported complex sequences. -/
theorem exists_ladderSystem : Nonempty (LadderSystem (ℕ →₀ ℂ)) := ⟨Fock.ladder⟩

/-- The harmonic oscillator spectrum in the concrete Fock model. -/
theorem fock_oscillator_spectrum {hbar omega : ℝ} (hbar_pos : 0 < hbar) (omega_pos : 0 < omega) :
    eigenvalues (hamiltonian hbar omega Fock.ladder) =
      {E : ℂ | ∃ n : ℕ, E = ((hbar * omega * ((n : ℝ) + 1 / 2) : ℝ) : ℂ)} :=
  oscillator_spectrum hbar_pos omega_pos Fock.ladder

end QPhys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace QPhys

/-!
# The spectrum of the quantum harmonic oscillator, via ladder operators

We work in the standard algebraic setting for the harmonic oscillator: a complex
inner product space `H` (the space of states), equipped with a *lowering* operator
`a` and a *raising* operator `a†`, which are formally adjoint to one another and
satisfy the canonical commutation relation `[a, a†] = 1`, together with a nonzero
*vacuum* vector annihilated by `a`.

The Hamiltonian is `Ĥ = ℏω (a† a + 1/2)`, and the main theorem
`QPhys.oscillator_spectrum` states that its set of eigenvalues is exactly
`{ℏω (n + 1/2) : n ∈ ℕ}`.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *ladder system* on a complex inner product space: a lowering operator `lower`,
a raising operator `raise` which is formally adjoint to it, satisfying the canonical
commutation relation `[lower, raise] = 1`, together with a nonzero vacuum state. -/
structure LadderSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- the annihilation (lowering) operator `a` -/
  lower : H →ₗ[ℂ] H
  /-- the creation (raising) operator `a†` -/
  raise : H →ₗ[ℂ] H
  /-- `raise` is the formal adjoint of `lower` -/
  adjoint : ∀ x y : H, ⟪lower x, y⟫_ℂ = ⟪x, raise y⟫_ℂ
  /-- canonical commutation relation `[a, a†] = 1` -/
  comm : ∀ x : H, lower (raise x) - raise (lower x) = x
  /-- the vacuum state -/
  vacuum : H
  /-- the vacuum state is nonzero -/
  vacuum_ne_zero : vacuum ≠ 0
  /-- the vacuum state is annihilated by the lowering operator -/
  lower_vacuum : lower vacuum = 0

/-- The number operator `N = a† a` of a ladder system. -/
def numberOp (L : LadderSystem H) : H →ₗ[ℂ] H := L.raise ∘ₗ L.lower

/-- The harmonic oscillator Hamiltonian `Ĥ = ℏω (a† a + 1/2)`. -/
noncomputable def hamiltonian (hbar omega : ℝ) (L : LadderSystem H) : H →ₗ[ℂ] H :=
  ((hbar * omega : ℝ) : ℂ) • (numberOp L + ((1 / 2 : ℂ)) • LinearMap.id)

/-- The set of eigenvalues (the point spectrum) of a linear operator. -/
def eigenvalues (T : H →ₗ[ℂ] H) : Set ℂ := {E : ℂ | ∃ x : H, x ≠ 0 ∧ T x = E • x}

section Basic

variable (L : LadderSystem H)

lemma numberOp_apply (x : H) : numberOp L x = L.raise (L.lower x) := rfl

lemma hamiltonian_apply (hbar omega : ℝ) (x : H) :
    hamiltonian hbar omega L x =
      ((hbar * omega : ℝ) : ℂ) • (numberOp L x + (1 / 2 : ℂ) • x) := by
  simp [hamiltonian]

/-- `N (a† x) = a† (N x) + a† x`. -/
lemma numberOp_raise (x : H) :
    numberOp L (L.raise x) = L.raise (numberOp L x) + L.raise x := by
  have h := sub_eq_iff_eq_add.mp (L.comm x)
  simp only [numberOp_apply, h, map_add]
  abel

/-- `N (a x) = a (N x) - a x`. -/
lemma numberOp_lower (x : H) :
    numberOp L (L.lower x) = L.lower (numberOp L x) - L.lower x := by
  have h := sub_eq_iff_eq_add.mp (L.comm (L.lower x))
  simp only [numberOp_apply]
  rw [h]
  abel

/-- `⟪x, N x⟫ = ‖a x‖²`. -/
lemma inner_numberOp_self (x : H) : ⟪x, numberOp L x⟫_ℂ = ((‖L.lower x‖ ^ 2 : ℝ) : ℂ) := by
  rw [numberOp_apply, ← L.adjoint, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `‖a† x‖² = re ⟪x, N x⟫ + ‖x‖²`. -/
lemma norm_raise_sq (x : H) :
    (‖L.raise x‖ ^ 2 : ℝ) = (⟪x, numberOp L x⟫_ℂ).re + ‖x‖ ^ 2 := by
  have h1 : ⟪L.raise x, L.raise x⟫_ℂ = ⟪L.lower (L.raise x), x⟫_ℂ := by
    rw [L.adjoint]
  have h2 : L.lower (L.raise x) = numberOp L x + x := by
    have h := sub_eq_iff_eq_add.mp (L.comm x)
    rw [numberOp_apply, h]; abel
  rw [h2] at h1
  have h3 : ⟪numberOp L x + x, x⟫_ℂ = ⟪numberOp L x, x⟫_ℂ + ⟪x, x⟫_ℂ := inner_add_left _ _ _
  have h4 : ⟪numberOp L x, x⟫_ℂ = (starRingEnd ℂ) ⟪x, numberOp L x⟫_ℂ := by
    rw [inner_conj_symm]
  rw [h3, h4] at h1
  have h5 := congrArg Complex.re h1
  have h6 : (⟪numberOp L x, x⟫_ℂ).re = (⟪x, numberOp L x⟫_ℂ).re := by
    rw [h4]
    exact Complex.conj_re _
  rw [← h6]
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.add_re, Complex.conj_re,
    inner_self_eq_norm_sq] using h5

end Basic

section Eigen

variable (L : LadderSystem H)

/-- An eigenvalue of the number operator is the nonnegative real number `‖a x‖² / ‖x‖²`. -/
lemma numberOp_eigenvalue_real {E : ℂ} {x : H} (hx : x ≠ 0) (hE : numberOp L x = E • x) :
    E = ((‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_numberOp_self L x
  rw [hE, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx2 : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hxn)
  push_cast at h ⊢
  rw [eq_div_iff hx2]
  exact_mod_cast h

/-- If a number-operator eigenvector has eigenvalue `0`, it is annihilated by `a`. -/
lemma lower_eq_zero_of_eigenvalue_zero {x : H} (hE : numberOp L x = (0 : ℂ) • x) :
    L.lower x = 0 := by
  have h := inner_numberOp_self L x
  rw [hE] at h
  simp only [zero_smul, inner_zero_right] at h
  have : (‖L.lower x‖ : ℝ) ^ 2 = 0 := by exact_mod_cast h.symm
  have : (‖L.lower x‖ : ℝ) = 0 := by nlinarith [norm_nonneg (L.lower x)]
  exact norm_eq_zero.mp this

/-- Descent step: if `x` is a nonzero eigenvector of `N` with eigenvalue `r` and
`a x ≠ 0`, then `a x` is an eigenvector with eigenvalue `r - 1`. -/
lemma numberOp_eigen_lower {r : ℝ} {x : H} (hE : numberOp L x = ((r : ℝ) : ℂ) • x) :
    numberOp L (L.lower x) = (((r - 1 : ℝ)) : ℂ) • L.lower x := by
  rw [numberOp_lower, hE, map_smul]
  push_cast
  module

/-- Every eigenvalue of the number operator is a natural number: descent along the
ladder must terminate. -/
lemma numberOp_eigenvalue_nat_of_le :
    ∀ (k : ℕ) (r : ℝ) (x : H), x ≠ 0 → numberOp L x = ((r : ℝ) : ℂ) • x → r ≤ k →
      ∃ m : ℕ, r = (m : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro r x hx hE hr
      have h0 : ((r : ℝ) : ℂ) = ((‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) :=
        numberOp_eigenvalue_real L hx hE
      have hr0 : r = ‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 := by exact_mod_cast h0
      have hnn : 0 ≤ r := by rw [hr0]; positivity
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero] at hr ⊢
      linarith
  | succ k ih =>
      intro r x hx hE hr
      by_cases hax : L.lower x = 0
      · have hz : ((r : ℝ) : ℂ) • x = 0 := by
          rw [← hE, numberOp_apply, hax, map_zero]
        rcases smul_eq_zero.mp hz with h | h
        · exact ⟨0, by exact_mod_cast h⟩
        · exact absurd h hx
      · obtain ⟨m, hm⟩ := ih (r - 1) (L.lower x) hax (numberOp_eigen_lower L hE)
          (by push_cast at hr ⊢; linarith)
        exact ⟨m + 1, by push_cast; linarith⟩

/-- Every eigenvalue of the number operator is a natural number. -/
lemma numberOp_eigenvalue_is_nat {E : ℂ} {x : H} (hx : x ≠ 0) (hE : numberOp L x = E • x) :
    ∃ n : ℕ, E = (n : ℂ) := by
  set r : ℝ := ‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 with hrdef
  have hE' : E = ((r : ℝ) : ℂ) := numberOp_eigenvalue_real L hx hE
  have hEr : numberOp L x = ((r : ℝ) : ℂ) • x := by rw [hE, hE']
  obtain ⟨m, hm⟩ :=
    numberOp_eigenvalue_nat_of_le L ⌈r⌉₊ r x hx hEr (Nat.le_ceil r)
  exact ⟨m, by rw [hE', hm]; norm_cast⟩

/-- The `n`-th excited state `(a†)ⁿ |0⟩`. -/
def state (L : LadderSystem H) (n : ℕ) : H := (L.raise ^ n) L.vacuum

lemma state_zero : state L 0 = L.vacuum := rfl

lemma state_succ (n : ℕ) : state L (n + 1) = L.raise (state L n) := by
  simp [state, pow_succ']

/-- `N ((a†)ⁿ |0⟩) = n (a†)ⁿ |0⟩`. -/
lemma numberOp_state (n : ℕ) : numberOp L (state L n) = ((n : ℂ)) • state L n := by
  induction n with
  | zero => simp [state_zero, numberOp_apply, L.lower_vacuum]
  | succ n ih =>
      rw [state_succ, numberOp_raise, ih, map_smul]
      push_cast
      module

/-- The excited states are nonzero: `‖(a†)ⁿ |0⟩‖² = n! ‖|0⟩‖²`. -/
lemma norm_state_sq (n : ℕ) : (‖state L n‖ ^ 2 : ℝ) = (n ! : ℝ) * ‖L.vacuum‖ ^ 2 := by
  induction n with
  | zero => simp [state_zero]
  | succ n ih =>
      have h := norm_raise_sq L (state L n)
      rw [numberOp_state, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
      have h' : (‖L.raise (state L n)‖ ^ 2 : ℝ) = (n : ℝ) * ‖state L n‖ ^ 2 + ‖state L n‖ ^ 2 := by
        simpa [Complex.mul_re, ← Complex.ofReal_pow] using h
      rw [state_succ, h', ih, Nat.factorial_succ]
      push_cast
      ring

lemma state_ne_zero (n : ℕ) : state L n ≠ 0 := by
  intro h
  have h1 := norm_state_sq L n
  rw [h] at h1
  simp only [norm_zero] at h1
  have hv : (0 : ℝ) < ‖L.vacuum‖ := norm_pos_iff.mpr L.vacuum_ne_zero
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpos : (0 : ℝ) < (n ! : ℝ) * ‖L.vacuum‖ ^ 2 := mul_pos hfac (pow_pos hv 2)
  rw [← h1] at hpos
  norm_num at hpos

end Eigen

/-- **Spectrum of the quantum harmonic oscillator.**

For a ladder system `L` on a complex inner product space (an annihilation operator `a`,
a creation operator `a†` formally adjoint to it with `[a, a†] = 1`, and a nonzero vacuum
vector annihilated by `a`), the set of eigenvalues of the Hamiltonian
`Ĥ = ℏω (a† a + 1/2)` is exactly `{ℏω (n + 1/2) : n ∈ ℕ}`. -/
theorem oscillator_spectrum {hbar omega : ℝ} (hbar_pos : 0 < hbar) (omega_pos : 0 < omega)
    (L : LadderSystem H) :
    eigenvalues (hamiltonian hbar omega L) =
      {E : ℂ | ∃ n : ℕ, E = ((hbar * omega * ((n : ℝ) + 1 / 2) : ℝ) : ℂ)} := by
  have hc : ((hbar * omega : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (mul_pos hbar_pos omega_pos)
  ext E
  simp only [eigenvalues, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hEq⟩
    rw [hamiltonian_apply, smul_add, smul_smul] at hEq
    have h1 : ((hbar * omega : ℝ) : ℂ) • numberOp L x =
        (E - ((hbar * omega : ℝ) : ℂ) * (1 / 2)) • x := by
      rw [sub_smul, ← hEq]
      module
    have hN : numberOp L x =
        (((hbar * omega : ℝ) : ℂ)⁻¹ * (E - ((hbar * omega : ℝ) : ℂ) * (1 / 2))) • x := by
      calc numberOp L x
          = ((hbar * omega : ℝ) : ℂ)⁻¹ • (((hbar * omega : ℝ) : ℂ) • numberOp L x) := by
            rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = ((hbar * omega : ℝ) : ℂ)⁻¹ • ((E - ((hbar * omega : ℝ) : ℂ) * (1 / 2)) • x) := by
            rw [h1]
        _ = (((hbar * omega : ℝ) : ℂ)⁻¹ * (E - ((hbar * omega : ℝ) : ℂ) * (1 / 2))) • x := by
            rw [smul_smul]
    obtain ⟨n, hn⟩ := numberOp_eigenvalue_is_nat L hx hN
    refine ⟨n, ?_⟩
    have h2 : ((hbar * omega : ℝ) : ℂ) *
        (((hbar * omega : ℝ) : ℂ)⁻¹ * (E - ((hbar * omega : ℝ) : ℂ) * (1 / 2)))
        = ((hbar * omega : ℝ) : ℂ) * (n : ℂ) := by rw [hn]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h2
    push_cast at h2 ⊢
    linear_combination h2
  · rintro ⟨n, rfl⟩
    refine ⟨state L n, state_ne_zero L n, ?_⟩
    rw [hamiltonian_apply, numberOp_state, smul_add, smul_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end QPhys

