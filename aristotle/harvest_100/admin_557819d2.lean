import RequestProject.Main

/-!
# A concrete model for the ladder-operator hypotheses

This file exhibits a concrete inner product space carrying ladder operators satisfying the
hypotheses of `QPhys.oscillator_spectrum`, so that the theorem is not vacuous.

The model is the algebraic Fock space of finitely supported complex sequences `ℕ →₀ ℂ`, with
`a (eₙ) = √n eₙ₋₁` and `a† (eₙ) = √(n+1) eₙ₊₁`.
-/

open scoped InnerProductSpace
open Finsupp

namespace QPhys

/-- The algebraic Fock space: finitely supported complex sequences. -/
abbrev FockSpace : Type := ℕ →₀ ℂ

namespace FockSpace

/-- The inner product on the algebraic Fock space. -/
noncomputable def innerFock (f g : FockSpace) : ℂ :=
  ∑ i ∈ f.support ∪ g.support, (starRingEnd ℂ) (f i) * g i

noncomputable instance : Inner ℂ FockSpace := ⟨innerFock⟩

lemma inner_def (f g : FockSpace) :
    ⟪f, g⟫_ℂ = ∑ i ∈ f.support ∪ g.support, (starRingEnd ℂ) (f i) * g i := rfl

lemma inner_eq_sum {f g : FockSpace} {s : Finset ℕ} (hf : f.support ⊆ s) (hg : g.support ⊆ s) :
    ⟪f, g⟫_ℂ = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  rw [inner_def]
  refine Finset.sum_subset (Finset.union_subset hf hg) ?_
  intro i _ hi
  simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hi
  rw [hi.1]
  simp

lemma inner_self_eq (f : FockSpace) :
    ⟪f, f⟫_ℂ = ((∑ i ∈ f.support, Complex.normSq (f i) : ℝ) : ℂ) := by
  rw [inner_def]
  push_cast
  refine Finset.sum_congr (by simp) ?_
  intro i _
  rw [Complex.normSq_eq_conj_mul_self]

lemma inner_self_re_nonneg (f : FockSpace) : 0 ≤ (⟪f, f⟫_ℂ).re := by
  rw [inner_self_eq]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

lemma inner_definite (f : FockSpace) (h : ⟪f, f⟫_ℂ = 0) : f = 0 := by
  rw [inner_self_eq, Complex.ofReal_eq_zero] at h
  have hz : ∀ i ∈ f.support, Complex.normSq (f i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).mp h
  ext i
  by_cases hi : i ∈ f.support
  · simpa using Complex.normSq_eq_zero.mp (hz i hi)
  · simpa using Finsupp.notMem_support_iff.mp hi

lemma inner_conj_symm' (f g : FockSpace) :
    (starRingEnd ℂ) (⟪g, f⟫_ℂ) = ⟪f, g⟫_ℂ := by
  rw [inner_eq_sum (s := f.support ∪ g.support) Finset.subset_union_right
      Finset.subset_union_left,
    inner_eq_sum (s := f.support ∪ g.support) Finset.subset_union_left Finset.subset_union_right,
    map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_comm]

lemma inner_add_left' (f g h : FockSpace) : ⟪f + g, h⟫_ℂ = ⟪f, h⟫_ℂ + ⟪g, h⟫_ℂ := by
  classical
  set s : Finset ℕ := f.support ∪ g.support ∪ h.support with hs
  have hfs : f.support ⊆ s := (Finset.subset_union_left).trans Finset.subset_union_left
  have hgs : g.support ⊆ s := (Finset.subset_union_right).trans Finset.subset_union_left
  have hhs : h.support ⊆ s := Finset.subset_union_right
  have hfg : (f + g).support ⊆ s :=
    (Finsupp.support_add).trans (Finset.union_subset hfs hgs)
  rw [inner_eq_sum hfg hhs, inner_eq_sum hfs hhs, inner_eq_sum hgs hhs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [add_mul]

lemma inner_smul_left' (f g : FockSpace) (r : ℂ) :
    ⟪r • f, g⟫_ℂ = (starRingEnd ℂ) r * ⟪f, g⟫_ℂ := by
  classical
  set s : Finset ℕ := f.support ∪ g.support with hs
  have hfs : f.support ⊆ s := Finset.subset_union_left
  have hgs : g.support ⊆ s := Finset.subset_union_right
  have hrf : (r • f).support ⊆ s := (Finsupp.support_smul).trans hfs
  rw [inner_eq_sum hrf hgs, inner_eq_sum hfs hgs, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_assoc]

noncomputable instance : NormedAddCommGroup FockSpace :=
  letI : InnerProductSpace.Core ℂ FockSpace :=
    { conj_inner_symm := inner_conj_symm'
      re_inner_nonneg := inner_self_re_nonneg
      add_left := inner_add_left'
      smul_left := inner_smul_left'
      definite := inner_definite }
  this.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℂ FockSpace := .ofCore _

lemma inner_single_single (m n : ℕ) (u v : ℂ) :
    ⟪(Finsupp.single m u : FockSpace), (Finsupp.single n v : FockSpace)⟫_ℂ
      = if m = n then (starRingEnd ℂ) u * v else 0 := by
  classical
  have hm : (Finsupp.single m u : FockSpace).support ⊆ ({m, n} : Finset ℕ) :=
    (Finsupp.support_single_subset).trans (by simp)
  have hn : (Finsupp.single n v : FockSpace).support ⊆ ({m, n} : Finset ℕ) :=
    (Finsupp.support_single_subset).trans (by simp)
  rw [inner_eq_sum hm hn]
  by_cases h : m = n
  · subst h
    simp
  · rw [Finset.sum_pair h]
    simp [h, Ne.symm h]

/-- The annihilation (lowering) operator, `a eₙ = √n eₙ₋₁`. -/
noncomputable def annihilate : FockSpace →ₗ[ℂ] FockSpace :=
  Finsupp.lsum ℂ fun n : ℕ =>
    ((Real.sqrt n : ℝ) : ℂ) • (Finsupp.lsingle (n - 1) : ℂ →ₗ[ℂ] FockSpace)

/-- The creation (raising) operator, `a† eₙ = √(n+1) eₙ₊₁`. -/
noncomputable def create : FockSpace →ₗ[ℂ] FockSpace :=
  Finsupp.lsum ℂ fun n : ℕ =>
    ((Real.sqrt (n + 1) : ℝ) : ℂ) • (Finsupp.lsingle (n + 1) : ℂ →ₗ[ℂ] FockSpace)

lemma annihilate_single (n : ℕ) (c : ℂ) :
    annihilate (Finsupp.single n c) = Finsupp.single (n - 1) (((Real.sqrt n : ℝ) : ℂ) * c) := by
  simp [annihilate, Finsupp.lsum_single, Finsupp.smul_single, smul_eq_mul]

lemma create_single (n : ℕ) (c : ℂ) :
    create (Finsupp.single n c)
      = Finsupp.single (n + 1) (((Real.sqrt (n + 1) : ℝ) : ℂ) * c) := by
  simp [create, Finsupp.lsum_single, Finsupp.smul_single, smul_eq_mul]

lemma adjoint_single (m n : ℕ) (u v : ℂ) :
    ⟪annihilate (Finsupp.single m u), (Finsupp.single n v : FockSpace)⟫_ℂ
      = ⟪(Finsupp.single m u : FockSpace), create (Finsupp.single n v)⟫_ℂ := by
  rw [annihilate_single, create_single, inner_single_single, inner_single_single]
  by_cases h : m = n + 1
  · subst h
    simp [mul_comm, mul_assoc]
  · by_cases h2 : m - 1 = n
    · have hm0 : m = 0 := by omega
      subst hm0
      simp
    · simp [h, h2]

/-- `annihilate` and `create` are mutually adjoint. -/
lemma adjoint_rel (x y : FockSpace) : ⟪annihilate x, y⟫_ℂ = ⟪x, create y⟫_ℂ := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, inner_add_left, hf, hg]
  | single m u =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [map_add, inner_add_right, hf, hg]
    | single n v => exact adjoint_single m n u v

/-- The canonical commutation relation `[a, a†] = 1`. -/
lemma ccr (x : FockSpace) : annihilate (create x) - create (annihilate x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add, map_add, map_add,
      show annihilate (create f) + annihilate (create g)
          - (create (annihilate f) + create (annihilate g))
        = (annihilate (create f) - create (annihilate f))
          + (annihilate (create g) - create (annihilate g)) by abel, hf, hg]
  | single n c =>
    rw [create_single, annihilate_single, annihilate_single, create_single]
    have hsq : ((Real.sqrt (n + 1) : ℝ) : ℂ) * ((Real.sqrt (n + 1) : ℝ) : ℂ)
        = ((n : ℂ) + 1) := by
      have h : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
    match n with
    | 0 =>
      simp only [Nat.add_sub_cancel, Nat.zero_sub, Nat.cast_zero, Real.sqrt_zero,
        Complex.ofReal_zero, zero_mul]
      rw [← mul_assoc]
      norm_num at hsq ⊢
    | (m + 1) =>
      have hsqm : ((Real.sqrt (m + 1) : ℝ) : ℂ) * ((Real.sqrt (m + 1) : ℝ) : ℂ)
          = ((m : ℂ) + 1) := by
        have h : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
          Real.mul_self_sqrt (by positivity)
        exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
      simp only [Nat.add_sub_cancel]
      rw [← Finsupp.single_sub]
      congr 1
      push_cast at hsq hsqm ⊢
      rw [← mul_assoc, ← mul_assoc, hsq, hsqm]
      ring

/-- The vacuum vector. -/
noncomputable def vacuum : FockSpace := Finsupp.single 0 1

lemma vacuum_ne_zero : vacuum ≠ 0 := by
  simp [vacuum, Finsupp.single_eq_zero]

lemma annihilate_vacuum : annihilate vacuum = 0 := by
  simp [vacuum, annihilate_single]

/-- The harmonic oscillator Hamiltonian `H = ℏω (a†a + ½)` on the Fock space. -/
noncomputable def hamiltonian (hbar omega : ℝ) : FockSpace →ₗ[ℂ] FockSpace :=
  ((hbar * omega : ℝ) : ℂ) • (create.comp annihilate + ((1 : ℂ) / 2) • LinearMap.id)

/-- **The Fock-space harmonic oscillator has spectrum `{ℏω(n+½) : n ∈ ℕ}`.**
This is `QPhys.oscillator_spectrum` instantiated at the concrete model, showing in particular
that the hypotheses of that theorem are satisfiable. -/
theorem fock_oscillator_spectrum (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega) :
    {mu : ℂ | ∃ v : FockSpace, v ≠ 0 ∧ hamiltonian hbar omega v = mu • v}
      = {mu : ℂ | ∃ n : ℕ, mu = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)} :=
  QPhys.oscillator_spectrum annihilate create adjoint_rel ccr vacuum vacuum_ne_zero
    annihilate_vacuum hbar omega hhbar homega (hamiltonian hbar omega) (fun _ => rfl)

end FockSpace

end QPhys

import Mathlib
/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

namespace QPhys

open scoped InnerProductSpace

section Ladder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (a ad : V →ₗ[ℂ] V)

/-- The number operator `N = a† a`. -/
def numberOp (a ad : V →ₗ[ℂ] V) : V →ₗ[ℂ] V := ad.comp a

lemma numberOp_apply (x : V) : numberOp a ad x = ad (a x) := rfl

variable (hadj : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
  (hcomm : ∀ x : V, a (ad x) - ad (a x) = x)

include hadj in
/-- For an eigenvector of the number operator, the eigenvalue times `‖v‖²` equals `‖a v‖²`. -/
lemma eigen_norm_eq {lam : ℂ} {v : V} (hv : numberOp a ad v = lam • v) :
    lam * ((‖v‖ : ℂ) ^ 2) = ((‖a v‖ : ℂ) ^ 2) := by
  have h1 : ⟪v, ad (a v)⟫_ℂ = ⟪a v, a v⟫_ℂ := (hadj v (a v)).symm
  have e1 : ⟪v, v⟫_ℂ = ((‖v‖ : ℂ)) ^ 2 := by
    simp
  have e2 : ⟪a v, a v⟫_ℂ = ((‖a v‖ : ℂ)) ^ 2 := by
    simp
  rw [numberOp_apply] at hv
  rw [hv, inner_smul_right, e1, e2] at h1
  exact h1

include hadj in
/-- Eigenvalues of the number operator are nonnegative reals. -/
lemma eigen_nonneg_real {lam : ℂ} {v : V} (hv0 : v ≠ 0) (hv : numberOp a ad v = lam • v) :
    lam.im = 0 ∧ 0 ≤ lam.re := by
  have h := eigen_norm_eq a ad hadj hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hnc : ((‖v‖ : ℂ)) ^ 2 ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using pow_ne_zero 2 (by exact_mod_cast hn : (‖v‖ : ℂ) ≠ 0)
  have hlam : lam = ((‖a v‖ ^ 2 / ‖v‖ ^ 2 : ℝ) : ℂ) := by
    have h2 := eq_div_of_mul_eq hnc h
    rw [h2]
    push_cast
    ring
  rw [hlam]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  positivity

include hadj in
lemma a_ne_zero_of_eigen_ne_zero {lam : ℂ} {v : V} (hv0 : v ≠ 0)
    (hv : numberOp a ad v = lam • v) (hlam : lam ≠ 0) : a v ≠ 0 := by
  intro hz
  have h := eigen_norm_eq a ad hadj hv
  rw [hz] at h
  simp only [norm_zero, Complex.ofReal_zero] at h
  rcases (by simpa using h : lam = 0 ∨ v = 0) with h1 | h1
  · exact hlam h1
  · exact hv0 h1

include hcomm in
/-- Lowering: `a v` is an eigenvector with eigenvalue `lam - 1`. -/
lemma numberOp_lower {lam : ℂ} {v : V} (hv : numberOp a ad v = lam • v) :
    numberOp a ad (a v) = (lam - 1) • (a v) := by
  rw [numberOp_apply] at hv ⊢
  have hx : a (ad (a v)) = a v + ad (a (a v)) := sub_eq_iff_eq_add.mp (hcomm (a v))
  rw [hv, map_smul] at hx
  rw [sub_smul, one_smul, hx]
  abel

include hcomm in
/-- Raising: `a† v` is an eigenvector with eigenvalue `lam + 1`. -/
lemma numberOp_raise {lam : ℂ} {v : V} (hv : numberOp a ad v = lam • v) :
    numberOp a ad (ad v) = (lam + 1) • (ad v) := by
  rw [numberOp_apply] at hv ⊢
  have h2 : a (ad v) = v + ad (a v) := sub_eq_iff_eq_add.mp (hcomm v)
  rw [hv] at h2
  rw [h2, map_add, map_smul, add_smul, one_smul]
  abel

include hadj hcomm in
lemma ad_ne_zero {lam : ℂ} {v : V} (hv0 : v ≠ 0) (hv : numberOp a ad v = lam • v) :
    ad v ≠ 0 := by
  obtain ⟨him, hre⟩ := eigen_nonneg_real a ad hadj hv0 hv
  have hraise := numberOp_raise a ad hcomm hv
  have hne : lam + 1 ≠ 0 := by
    intro h
    have : (lam + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  intro hz
  -- if `ad v = 0` then the eigenvalue equation forces `(lam+1) • v = 0`
  have h2 : a (ad v) = (lam + 1) • v := by
    have h3 : a (ad v) = v + ad (a v) := sub_eq_iff_eq_add.mp (hcomm v)
    rw [numberOp_apply] at hv
    rw [h3, hv]
    module
  rw [hz] at h2
  simp only [map_zero] at h2
  have := (smul_eq_zero.mp h2.symm)
  rcases this with h3 | h3
  · exact hne h3
  · exact hv0 h3

include hadj hcomm in
/-- Every eigenvalue of the number operator is a natural number. -/
lemma numberOp_eigen_nat {lam : ℂ} {v : V} (hv0 : v ≠ 0) (hv : numberOp a ad v = lam • v) :
    ∃ n : ℕ, lam = (n : ℂ) := by
  suffices H : ∀ N : ℕ, ∀ (mu : ℂ) (w : V), w ≠ 0 → numberOp a ad w = mu • w →
      mu.re ≤ (N : ℝ) → ∃ n : ℕ, mu = (n : ℂ) by
    exact H ⌈lam.re⌉₊ lam v hv0 hv (Nat.le_ceil _)
  intro N
  induction N with
  | zero =>
    intro mu w hw hev hle
    obtain ⟨him, hre⟩ := eigen_nonneg_real a ad hadj hw hev
    refine ⟨0, ?_⟩
    have hre0 : mu.re = 0 := le_antisymm (by simpa using hle) hre
    apply Complex.ext <;> simp [him, hre0]
  | succ N ih =>
    intro mu w hw hev hle
    obtain ⟨him, hre⟩ := eigen_nonneg_real a ad hadj hw hev
    by_cases hmu : mu = 0
    · exact ⟨0, by simp [hmu]⟩
    · have haw : a w ≠ 0 := a_ne_zero_of_eigen_ne_zero a ad hadj hw hev hmu
      have hlow := numberOp_lower a ad hcomm hev
      have hle' : (mu - 1).re ≤ (N : ℝ) := by
        simp only [Complex.sub_re, Complex.one_re]
        push_cast at hle
        linarith
      obtain ⟨m, hm⟩ := ih (mu - 1) (a w) haw hlow hle'
      exact ⟨m + 1, by push_cast; linear_combination hm⟩

include hadj hcomm in
/-- Starting from a vacuum vector, every natural number is an eigenvalue. -/
lemma numberOp_eigen_exists (v0 : V) (hv0 : v0 ≠ 0) (hav0 : a v0 = 0) (n : ℕ) :
    ∃ v : V, v ≠ 0 ∧ numberOp a ad v = (n : ℂ) • v := by
  induction n with
  | zero => exact ⟨v0, hv0, by simp [numberOp_apply, hav0]⟩
  | succ n ih =>
    obtain ⟨v, hvne, hev⟩ := ih
    refine ⟨ad v, ad_ne_zero a ad hadj hcomm hvne hev, ?_⟩
    rw [numberOp_raise a ad hcomm hev]
    congr 1
    push_cast
    ring

end Ladder

/-- **Spectrum of the quantum harmonic oscillator.**
If `a`, `a†` are ladder operators on a complex inner product space (mutually adjoint, with
canonical commutation relation `[a, a†] = 1`), admitting a nonzero vacuum vector `v₀`
annihilated by `a`, then the point spectrum of the Hamiltonian
`H = ℏω (a†a + ½)` is exactly `{ℏω(n + ½) : n ∈ ℕ}`. -/
theorem oscillator_spectrum
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a ad : V →ₗ[ℂ] V)
    (hadj : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : V, a (ad x) - ad (a x) = x)
    (v0 : V) (hv0 : v0 ≠ 0) (hav0 : a v0 = 0)
    (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega)
    (H : V →ₗ[ℂ] V)
    (hH : ∀ x : V, H x = ((hbar * omega : ℝ) : ℂ) • (ad (a x) + ((1 : ℂ) / 2) • x)) :
    {mu : ℂ | ∃ v : V, v ≠ 0 ∧ H v = mu • v}
      = {mu : ℂ | ∃ n : ℕ, mu = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)} := by
  set c : ℂ := ((hbar * omega : ℝ) : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  ext mu
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hvne, hHv⟩
    rw [hH v] at hHv
    have key : numberOp a ad v = (c⁻¹ * mu - 1 / 2) • v := by
      rw [numberOp_apply]
      have h1 : c • (ad (a v)) = (mu - c * (1 / 2)) • v := by
        rw [smul_add, smul_smul] at hHv
        rw [sub_smul]
        rw [← hHv]
        module
      have := congrArg (fun x : V => c⁻¹ • x) h1
      simp only [smul_smul, inv_mul_cancel₀ hcne, one_smul] at this
      rw [this]
      congr 1
      field_simp
    obtain ⟨n, hn⟩ := numberOp_eigen_nat a ad hadj hcomm hvne key
    refine ⟨n, ?_⟩
    have : c⁻¹ * mu = (n : ℂ) + 1 / 2 := by linear_combination hn
    calc mu = c * (c⁻¹ * mu) := by field_simp
    _ = c * ((n : ℂ) + 1 / 2) := by rw [this]
  · rintro ⟨n, hn⟩
    obtain ⟨v, hvne, hev⟩ := numberOp_eigen_exists a ad hadj hcomm v0 hv0 hav0 n
    refine ⟨v, hvne, ?_⟩
    rw [hH v, hn]
    rw [numberOp_apply] at hev
    rw [hev]
    module

end QPhys

