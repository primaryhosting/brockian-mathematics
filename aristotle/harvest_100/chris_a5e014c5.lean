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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Weyl-law style statement proved here: for a linear operator `T` on an infinite
dimensional real vector space (in particular on a real inner product space) whose spectrum is
*discrete* — every spectral subspace below a level is finite dimensional — and whose
eigensystem is *complete*, as furnished by the Rayleigh variational method (RVM), the
eigenvalue counting function `lam ↦ dim (span of eigenvectors with eigenvalue ≤ lam)`
diverges to `+∞`.

The final section exhibits an explicit model (the diagonal operator `f ↦ (n ↦ n * f n)` on
finitely supported real sequences) satisfying all the hypotheses, so the theorem is not
vacuous.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

section General

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The low-lying spectral subspace: the span of all eigenvectors of `T` whose
eigenvalue is at most `lam`. -/
noncomputable def lowSpectrumSpan (T : Module.End ℝ H) (lam : ℝ) : Submodule ℝ H :=
  ⨆ c ∈ {c : ℝ | c ≤ lam}, T.eigenspace c

/-- The Weyl eigenvalue counting function: the total multiplicity (the dimension of the span
of the corresponding eigenvectors) of the eigenvalues of `T` lying below `lam`. -/
noncomputable def counting (T : Module.End ℝ H) (lam : ℝ) : ℕ :=
  Module.finrank ℝ (lowSpectrumSpan T lam)

/-- Discreteness of the spectrum: below every level `lam` only finitely much spectrum
(counted with multiplicity) accumulates, i.e. the corresponding spectral subspace is
finite dimensional. -/
def HasDiscreteSpectrum (T : Module.End ℝ H) : Prop :=
  ∀ lam : ℝ, FiniteDimensional ℝ (lowSpectrumSpan T lam)

/-- Completeness of the eigensystem produced by the Rayleigh variational method (RVM):
the eigenvectors of `T` span the whole space. -/
def RVMComplete (T : Module.End ℝ H) : Prop :=
  ⨆ c : ℝ, T.eigenspace c = ⊤

/-- The spectral subspaces are monotone in the level. -/
theorem lowSpectrumSpan_mono (T : Module.End ℝ H) {a b : ℝ} (hab : a ≤ b) :
    lowSpectrumSpan T a ≤ lowSpectrumSpan T b :=
  iSup_le fun c => iSup_le fun (hc : c ≤ a) =>
    le_iSup₂ (f := fun c (_ : c ≤ b) => T.eigenspace c) c (hc.trans hab)

/-- The counting function is monotone, given discreteness of the spectrum. -/
theorem counting_mono (T : Module.End ℝ H) (hdisc : HasDiscreteSpectrum T) :
    Monotone (counting T) := by
  intro a b hab
  have : FiniteDimensional ℝ (lowSpectrumSpan T b) := hdisc b
  exact Submodule.finrank_mono (lowSpectrumSpan_mono T hab)

/-- If the eigenvectors of `T` span an infinite dimensional space and the spectrum is
discrete, then every prescribed multiplicity is exceeded at some spectral level. -/
theorem exists_le_counting (T : Module.End ℝ H) (hinf : ¬ FiniteDimensional ℝ H)
    (hdisc : HasDiscreteSpectrum T) (hrvm : RVMComplete T) (k : ℕ) :
    ∃ lam : ℝ, k ≤ counting T lam := by
  -- Pick `k` linearly independent vectors; possible since `H` is infinite dimensional.
  have hrank : (k : Cardinal) ≤ Module.rank ℝ H := by
    have hlt : ¬ Module.rank ℝ H < Cardinal.aleph0 := by
      rw [Module.rank_lt_aleph0_iff]
      exact fun h => hinf h
    exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans (not_lt.mp hlt)
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (R := ℝ) (M := H) (n := k) hrank
  -- Each of them lies in the span of finitely many eigenspaces.
  have hmem : ∀ i : Fin k, ∃ s : Finset ℝ, v i ∈ ⨆ c ∈ s, T.eigenspace c := by
    intro i
    have hmem' : v i ∈ ⨆ c : ℝ, T.eigenspace c := by rw [hrvm]; trivial
    exact Submodule.mem_iSup_iff_exists_finset.mp hmem'
  choose s hs using hmem
  -- Take a level above all the finitely many eigenvalues involved.
  obtain ⟨lam, hlam⟩ := (Finset.univ.biUnion s).exists_le
  refine ⟨lam, ?_⟩
  have hspan : Submodule.span ℝ (Set.range v) ≤ lowSpectrumSpan T lam := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hle : (⨆ c ∈ s i, T.eigenspace c) ≤ lowSpectrumSpan T lam :=
      iSup_le fun c => iSup_le fun (hc : c ∈ s i) =>
        le_iSup₂ (f := fun c (_ : c ≤ lam) => T.eigenspace c) c
          (hlam c (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩))
    exact hle (hs i)
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = k := by
    simpa using finrank_span_eq_card hv
  have : FiniteDimensional ℝ (lowSpectrumSpan T lam) := hdisc lam
  calc k = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := hcard.symm
    _ ≤ counting T lam := Submodule.finrank_mono hspan

/-- **Weyl law: divergence of the eigenvalue counting function.**
If a linear operator `T` on an infinite dimensional real vector space (for instance a real
inner product space) has a discrete spectrum — every spectral subspace below a level is
finite dimensional — and a complete eigensystem, as furnished by the Rayleigh variational
method, then its eigenvalue counting function diverges to infinity. -/
theorem counting_diverges_of_discrete_and_rvm (T : Module.End ℝ H)
    (hinf : ¬ FiniteDimensional ℝ H) (hdisc : HasDiscreteSpectrum T)
    (hrvm : RVMComplete T) :
    Filter.Tendsto (counting T) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun k => ?_
  obtain ⟨lam, hlam⟩ := exists_le_counting T hinf hdisc hrvm k
  exact ⟨lam, fun a ha => hlam.trans (counting_mono T hdisc ha)⟩

end General

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Weyl law in the inner product space setting.**
Specialization of `counting_diverges_of_discrete_and_rvm` to an operator on an infinite
dimensional real inner product space. -/
theorem counting_diverges_of_discrete_and_rvm_innerProductSpace (T : Module.End ℝ E)
    (hinf : ¬ FiniteDimensional ℝ E) (hdisc : HasDiscreteSpectrum T)
    (hrvm : RVMComplete T) :
    Filter.Tendsto (counting T) Filter.atTop Filter.atTop :=
  counting_diverges_of_discrete_and_rvm T hinf hdisc hrvm

end InnerProduct

/-! ## A model satisfying all the hypotheses

We check that the hypotheses of `counting_diverges_of_discrete_and_rvm` are consistent, by
exhibiting the diagonal operator `f ↦ (n ↦ n * f n)` on the space `ℕ →₀ ℝ` of finitely
supported real sequences. -/

section Model

/-- The diagonal operator `f ↦ (n ↦ n * f n)` on finitely supported real sequences. -/
noncomputable def diagOp : Module.End ℝ (ℕ →₀ ℝ) :=
  Finsupp.lsum ℝ fun n : ℕ => (n : ℝ) • Finsupp.lsingle n

theorem diagOp_apply (f : ℕ →₀ ℝ) (m : ℕ) : diagOp f m = m * f m := by
  classical
  have hsum : diagOp f = f.sum fun n a => (n : ℝ) • Finsupp.single n a := rfl
  rw [hsum, Finsupp.sum_apply]
  refine (Finsupp.sum_eq_single m ?_ ?_).trans ?_
  · intro n _ hnm
    simp [Ne.symm hnm]
  · intro _
    simp
  · simp

theorem diagOp_single (n : ℕ) (a : ℝ) :
    diagOp (Finsupp.single n a) = (n : ℝ) • Finsupp.single n a := by
  simp [diagOp]

/-- Each standard basis vector is an eigenvector of `diagOp`. -/
theorem single_mem_eigenspace (n : ℕ) :
    Finsupp.single n (1 : ℝ) ∈ diagOp.eigenspace (n : ℝ) := by
  rw [Module.End.mem_eigenspace_iff]
  simpa using diagOp_single n 1

theorem diagOp_rvmComplete : RVMComplete diagOp := by
  refine top_unique ?_
  have htop : Submodule.span ℝ (Set.range fun n : ℕ => Finsupp.single n (1 : ℝ)) = ⊤ := by
    simpa using (Finsupp.basisSingleOne (ι := ℕ) (R := ℝ)).span_eq
  rw [← htop, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact le_iSup (fun c : ℝ => diagOp.eigenspace c) (n : ℝ) (single_mem_eigenspace n)

theorem diagOp_hasDiscreteSpectrum : HasDiscreteSpectrum diagOp := by
  intro lam
  classical
  set N : ℕ := ⌈lam⌉₊ with hN
  set B : Set (ℕ →₀ ℝ) :=
    (fun m : ℕ => Finsupp.single m (1 : ℝ)) '' (Finset.range (N + 1) : Finset ℕ) with hB
  have hBfin : B.Finite := Set.Finite.image _ (Finset.range (N + 1)).finite_toSet
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ B) :=
    FiniteDimensional.span_of_finite ℝ hBfin
  have hle : lowSpectrumSpan diagOp lam ≤ Submodule.span ℝ B := by
    refine iSup_le fun c => iSup_le fun (hc : c ≤ lam) => ?_
    intro f hf
    rw [Module.End.mem_eigenspace_iff] at hf
    -- every coordinate of `f` outside `{m | (m : ℝ) = c}` vanishes
    have hcoord : ∀ m : ℕ, (m : ℝ) ≠ c → f m = 0 := by
      intro m hm
      have h1 := congrArg (fun g : ℕ →₀ ℝ => g m) hf
      simp only [diagOp_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      have hsub : ((m : ℝ) - c) * f m = 0 := by ring_nf; linarith [h1]
      rcases mul_eq_zero.mp hsub with h | h
      · exact absurd (by linarith [sub_eq_zero.mp h] : (m : ℝ) = c) hm
      · exact h
    have hsupp : ∀ m ∈ f.support, m ∈ Finset.range (N + 1) := by
      intro m hm
      have hfm : f m ≠ 0 := Finsupp.mem_support_iff.mp hm
      have hmc : (m : ℝ) = c := by
        by_contra hne
        exact hfm (hcoord m hne)
      have hmlam : (m : ℝ) ≤ lam := hmc ▸ hc
      have hmN : m ≤ N := by exact_mod_cast le_trans hmlam (Nat.le_ceil lam)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmN)
    -- expand `f` in the standard basis
    have hexp : f = f.sum fun m a => a • Finsupp.single m (1 : ℝ) := by
      conv_lhs => rw [← Finsupp.sum_single f]
      exact Finsupp.sum_congr fun m _ => by simp [Finsupp.smul_single]
    rw [hexp, Finsupp.sum]
    refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨m, by simpa using hsupp m hm, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem finsupp_not_finiteDimensional : ¬ FiniteDimensional ℝ (ℕ →₀ ℝ) := by
  intro h
  have hli : LinearIndependent ℝ (fun n : ℕ => Finsupp.single n (1 : ℝ)) := by
    simpa using (Finsupp.basisSingleOne (ι := ℕ) (R := ℝ)).linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite _ hli

/-- The hypotheses of the main theorem are consistent: the diagonal operator on finitely
supported real sequences satisfies all of them, and its counting function diverges. -/
theorem diagOp_counting_diverges :
    Filter.Tendsto (counting diagOp) Filter.atTop Filter.atTop :=
  counting_diverges_of_discrete_and_rvm diagOp finsupp_not_finiteDimensional
    diagOp_hasDiscreteSpectrum diagOp_rvmComplete

end Model

end Brockian.Weyl.WeylLawTarget

