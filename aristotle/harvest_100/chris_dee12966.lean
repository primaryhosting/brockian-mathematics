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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A Hilbert–Pólya style scaffold: a *Brockian system* is a complex inner product space equipped
with a symmetric operator whose point spectrum contains the spectral parameter
`-i (ρ - 1/2)` of every nontrivial zero `ρ` of the Riemann zeta function.  The main theorem
`Brockian.RiemannScaffold.RH_of_BrockianSystem` shows that the existence of such a system
implies the Riemann hypothesis, with no further hypotheses.
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace Brockian.RiemannScaffold

open Complex

/-- The *Brockian spectral parameter* attached to a complex number `s`, namely `-i (s - 1/2)`.
It is real exactly when `s` lies on the critical line. -/
noncomputable def spectralParameter (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

/-- `s` lies on the critical line iff its spectral parameter is real. -/
theorem re_eq_half_iff_spectralParameter_im_eq_zero (s : ℂ) :
    s.re = 1 / 2 ↔ (spectralParameter s).im = 0 := by
  have h : (spectralParameter s).im = 1 / 2 - s.re := by
    simp [spectralParameter, Complex.mul_im]
  rw [h]
  constructor <;> intro h' <;> linarith

/-- A **Brockian system** is a Hilbert–Pólya style datum: a complex inner product space
together with a symmetric (formally self-adjoint) linear operator on it whose point spectrum
contains the spectral parameter `-i (ρ - 1/2)` of every nontrivial zero `ρ` of the Riemann
zeta function. -/
structure BrockianSystem where
  /-- The underlying complex inner product space. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  /-- The Brockian operator. -/
  op : carrier →ₗ[ℂ] carrier
  /-- The Brockian operator is symmetric. -/
  op_symm : ∀ x y : carrier, ⟪op x, y⟫_ℂ = ⟪x, op y⟫_ℂ
  /-- Every nontrivial zero of `ζ` contributes an eigenvector whose eigenvalue is the
  corresponding spectral parameter. -/
  hasEigenvector : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    ∃ v : carrier, v ≠ 0 ∧ op v = spectralParameter s • v

attribute [instance] BrockianSystem.normedAddCommGroup BrockianSystem.innerProductSpace

/-- Eigenvalues of a symmetric operator on a complex inner product space are real. -/
theorem eigenvalue_im_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ[ℂ] H) (hT : ∀ x y : H, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    {l : ℂ} {v : H} (hv : v ≠ 0) (hl : T v = l • v) : l.im = 0 := by
  have h := hT v v
  rw [hl, inner_smul_left, inner_smul_right] at h
  have hn : (⟪v, v⟫_ℂ) ≠ 0 := by simpa [inner_self_eq_zero] using hv
  exact Complex.conj_eq_iff_im.mp (mul_right_cancel₀ hn h)

/-- **Main result.** The existence of a Brockian system implies the Riemann hypothesis. -/
theorem RH_of_BrockianSystem (S : BrockianSystem) : RiemannHypothesis := by
  intro s hs htriv hone
  obtain ⟨v, hv, hop⟩ := S.hasEigenvector s hs htriv hone
  exact (re_eq_half_iff_spectralParameter_im_eq_zero s).2
    (eigenvalue_im_eq_zero S.op S.op_symm hv hop)

/-!
## Non-vacuity: a Brockian system exists as soon as the Riemann hypothesis holds

We build the model space `ℝ →₀ ℂ` (finitely supported complex functions on the reals) with its
standard inner product and the multiplication-by-the-index operator, which is symmetric and has
every real number as an eigenvalue.  Consequently the hypothesis of `RH_of_BrockianSystem` is
precisely equivalent to the Riemann hypothesis.
-/

/-- The standard inner product on finitely supported complex functions on `ℝ`. -/
noncomputable def fsInner (f g : ℝ →₀ ℂ) : ℂ := f.sum fun t a => (starRingEnd ℂ) a * g t

theorem fsInner_eq_sum (f g : ℝ →₀ ℂ) (s : Finset ℝ) (hs : f.support ⊆ s) :
    fsInner f g = ∑ t ∈ s, (starRingEnd ℂ) (f t) * g t := by
  refine Finset.sum_subset hs ?_
  intro x _ hx
  simp [Finsupp.notMem_support_iff.mp hx]

theorem fsInner_add_left (f₁ f₂ g : ℝ →₀ ℂ) :
    fsInner (f₁ + f₂) g = fsInner f₁ g + fsInner f₂ g := by
  unfold fsInner
  rw [Finsupp.sum_add_index'] <;> intros <;> simp [add_mul]

theorem fsInner_smul_left (f g : ℝ →₀ ℂ) (r : ℂ) :
    fsInner (r • f) g = (starRingEnd ℂ) r * fsInner f g := by
  unfold fsInner
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  simp [mul_assoc]

theorem fsInner_conj_symm (f g : ℝ →₀ ℂ) :
    (starRingEnd ℂ) (fsInner g f) = fsInner f g := by
  rw [fsInner_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right,
      fsInner_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, map_sum]
  exact Finset.sum_congr rfl (fun t _ => by simp [mul_comm])

theorem fsInner_self_eq (f : ℝ →₀ ℂ) :
    fsInner f f = ((∑ t ∈ f.support, Complex.normSq (f t) : ℝ) : ℂ) := by
  rw [fsInner_eq_sum f f f.support (subset_refl _)]
  push_cast
  exact Finset.sum_congr rfl (fun t _ => by rw [Complex.normSq_eq_conj_mul_self])

theorem fsInner_self_nonneg (f : ℝ →₀ ℂ) : 0 ≤ (fsInner f f).re := by
  rw [fsInner_self_eq]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg (fun t _ => Complex.normSq_nonneg _)

theorem fsInner_definite (f : ℝ →₀ ℂ) (h : fsInner f f = 0) : f = 0 := by
  rw [fsInner_self_eq] at h
  have h' : ∑ t ∈ f.support, Complex.normSq (f t) = 0 := by exact_mod_cast h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => Complex.normSq_nonneg (f t))).mp h'
  ext t
  by_cases ht : t ∈ f.support
  · simpa using Complex.normSq_eq_zero.mp (hz t ht)
  · simpa using Finsupp.notMem_support_iff.mp ht

/-- Multiplication by the index: the model Brockian operator. -/
noncomputable def mulOp : (ℝ →₀ ℂ) →ₗ[ℂ] (ℝ →₀ ℂ) :=
  Finsupp.lsum ℂ (fun t : ℝ => (t : ℂ) • Finsupp.lsingle t)

theorem mulOp_apply (f : ℝ →₀ ℂ) (x : ℝ) : (mulOp f) x = (x : ℂ) * f x := by
  have h1 : mulOp f = f.sum (fun t a => Finsupp.single t ((t : ℂ) * a)) := by
    simp [mulOp, Finsupp.lsum_apply, Finsupp.sum]
  rw [h1, Finsupp.sum, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  by_cases hx : x ∈ f.support
  · rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hx h
  · have hf : f x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hf, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hbx : b ≠ x := by rintro rfl; exact hx hb
    simp [hbx]

theorem mulOp_support (f : ℝ →₀ ℂ) : (mulOp f).support ⊆ f.support := by
  intro x hx
  by_contra h
  rw [Finsupp.mem_support_iff, mulOp_apply, Finsupp.notMem_support_iff.mp h, mul_zero] at hx
  exact hx rfl

theorem fsInner_mulOp_symm (f g : ℝ →₀ ℂ) : fsInner (mulOp f) g = fsInner f (mulOp g) := by
  have hsub : (mulOp f).support ⊆ f.support ∪ g.support :=
    (mulOp_support f).trans Finset.subset_union_left
  rw [fsInner_eq_sum (mulOp f) g _ hsub,
      fsInner_eq_sum f (mulOp g) _ Finset.subset_union_left]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [mulOp_apply, mulOp_apply, map_mul, Complex.conj_ofReal]
  ring

theorem mulOp_single (t : ℝ) :
    mulOp (Finsupp.single t (1 : ℂ)) = (t : ℂ) • Finsupp.single t (1 : ℂ) := by
  ext x
  rw [mulOp_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases h : t = x <;> simp [h]

/-- The model space underlying the Brockian system built from the Riemann hypothesis. -/
def BrockianSpace : Type := ℝ →₀ ℂ

noncomputable instance : AddCommGroup BrockianSpace := inferInstanceAs (AddCommGroup (ℝ →₀ ℂ))
noncomputable instance : Module ℂ BrockianSpace := inferInstanceAs (Module ℂ (ℝ →₀ ℂ))
noncomputable instance : Inner ℂ BrockianSpace := ⟨fsInner⟩

/-- The inner product space core on `BrockianSpace`. -/
noncomputable def brockianCore : InnerProductSpace.Core ℂ BrockianSpace where
  conj_inner_symm x y := fsInner_conj_symm x y
  re_inner_nonneg x := fsInner_self_nonneg x
  add_left x y z := fsInner_add_left x y z
  smul_left x y r := fsInner_smul_left x y r
  definite x h := fsInner_definite x h

noncomputable instance : NormedAddCommGroup BrockianSpace := brockianCore.toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℂ BrockianSpace := .ofCore brockianCore.1

/-- On the critical line the spectral parameter is the (real) imaginary part. -/
theorem spectralParameter_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    spectralParameter s = (s.im : ℂ) := by
  apply Complex.ext <;> simp [spectralParameter, Complex.mul_re, Complex.mul_im, hs]

/-- Assuming the Riemann hypothesis, a Brockian system exists. -/
theorem nonempty_brockianSystem_of_RH (h : RiemannHypothesis) : Nonempty BrockianSystem := by
  refine ⟨{ carrier := BrockianSpace
            op := mulOp
            op_symm := fun x y => fsInner_mulOp_symm x y
            hasEigenvector := ?_ }⟩
  intro s hzero htriv hone
  have hre : s.re = 1 / 2 := h s hzero htriv hone
  refine ⟨(Finsupp.single s.im (1 : ℂ) : ℝ →₀ ℂ), ?_, ?_⟩
  · exact Finsupp.single_ne_zero.mpr one_ne_zero
  · rw [spectralParameter_of_re_eq_half hre]
    exact mulOp_single s.im

/-- The hypothesis of `RH_of_BrockianSystem` is exactly equivalent to the Riemann hypothesis:
the scaffold is neither vacuous nor stronger than what it proves. -/
theorem nonempty_brockianSystem_iff_RH : Nonempty BrockianSystem ↔ RiemannHypothesis :=
  ⟨fun ⟨S⟩ => RH_of_BrockianSystem S, nonempty_brockianSystem_of_RH⟩

end Brockian.RiemannScaffold

