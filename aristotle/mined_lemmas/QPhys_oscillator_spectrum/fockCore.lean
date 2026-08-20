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

