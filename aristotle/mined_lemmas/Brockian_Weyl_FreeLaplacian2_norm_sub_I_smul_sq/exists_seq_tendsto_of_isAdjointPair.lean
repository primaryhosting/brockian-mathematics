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

import Mathlib

/-!
# Essential self-adjointness of the free Laplacian

This file proves that the free Laplacian `-Δ`, defined on the Schwartz space
`𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

## Formalisation of essential self-adjointness

An unbounded operator is modelled here by a pair of linear maps `ι, A : D →ₗ[ℂ] H`
out of an abstract "domain" module `D`: `ι` is the (dense-range) inclusion of the
operator domain into the Hilbert space `H`, and `A` is the operator itself.

* `Brockian.Weyl.FreeLaplacian2.IsAdjointPair ι A u v` says that `(u, v)` belongs to the graph
  of the adjoint operator `A*`, i.e. `⟪v, ι f⟫ = ⟪u, A f⟫` for all `f` in the domain.
* `Brockian.Weyl.FreeLaplacian2.IsEssentiallySelfAdjoint ι A` says that the domain is dense,
  that `A` is symmetric, and that the adjoint `A*` is symmetric.  For a densely defined
  symmetric operator, symmetry of `A*` is the standard characterisation of essential
  self-adjointness (it is equivalent to `A* = A** = closure of A` being self-adjoint).

The abstract criterion `isEssentiallySelfAdjoint_of_dense_ranges` is von Neumann's basic
criterion: a densely defined symmetric operator with `Ran(A + i)` and `Ran(A - i)` dense is
essentially self-adjoint.

## Main results

* `Brockian.Weyl.FreeLaplacian2.fourier_freeLaplacian`: the Fourier transform conjugates the free
  Laplacian into multiplication by the symbol `4 π² ‖ξ‖²`.
* `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier`: the free
  Laplacian on `𝓢(ℝ^d, ℂ) ⊆ L²(ℝ^d, ℂ)` is essentially self-adjoint.  The statement is
  unconditional: the Fourier-side input is supplied by `fourier_freeLaplacian`.
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Filter Topology
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap ContDiff

noncomputable section

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- `IsAdjointPair ι A u v` states that the pair `(u, v)` belongs to the graph of the adjoint
of the operator `A` with domain `ι`, that is, `⟪v, ι f⟫ = ⟪u, A f⟫` for every `f` in the
domain. -/

theorem exists_seq_tendsto_of_isAdjointPair (ι A : D →ₗ[ℂ] H)
    (hsymm : ∀ f g : D, ⟪A f, ι g⟫ = ⟪ι f, A g⟫)
    (hpos : Dense (Set.range (A + Complex.I • ι)))
    (hneg : Dense (Set.range (A - Complex.I • ι)))
    {u v : H} (huv : IsAdjointPair ι A u v) :
    ∃ f : ℕ → D, Tendsto (fun n => ι (f n)) atTop (𝓝 u) ∧
      Tendsto (fun n => A (f n)) atTop (𝓝 v) := by
  set B : D →ₗ[ℂ] H := A - Complex.I • ι with hB
  set t : H := v - Complex.I • u with ht
  have hchoice : ∀ n : ℕ, ∃ g : D, ‖B g - t‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨y, hy, hlt⟩ := hneg.exists_dist_lt t (show (0 : ℝ) < 1 / (n + 1) by positivity)
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, by rwa [dist_comm, dist_eq_norm] at hlt⟩
  choose f hf using hchoice
  have hBtend : Tendsto (fun n => B (f n)) atTop (𝓝 t) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hf n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hBcauchy : CauchySeq (fun n => B (f n)) := hBtend.cauchySeq
  have hle : ∀ m n : ℕ, ‖A (f m) - A (f n)‖ ≤ ‖B (f m) - B (f n)‖ ∧
      ‖ι (f m) - ι (f n)‖ ≤ ‖B (f m) - B (f n)‖ := by
    intro m n
    have hsubeq : B (f m) - B (f n) = A (f m - f n) - Complex.I • ι (f m - f n) := by
      simp [hB, map_sub, smul_sub]; abel
    have hkey := norm_sub_I_smul_sq ι A hsymm (f m - f n)
    rw [← hsubeq] at hkey
    rw [show ‖A (f m - f n)‖ = ‖A (f m) - A (f n)‖ by rw [map_sub],
      show ‖ι (f m - f n)‖ = ‖ι (f m) - ι (f n)‖ by rw [map_sub]] at hkey
    constructor
    · nlinarith [norm_nonneg (A (f m) - A (f n)), norm_nonneg (ι (f m) - ι (f n)),
        norm_nonneg (B (f m) - B (f n))]
    · nlinarith [norm_nonneg (A (f m) - A (f n)), norm_nonneg (ι (f m) - ι (f n)),
        norm_nonneg (B (f m) - B (f n))]
  have hAcauchy : CauchySeq (fun n => A (f n)) := by
    rw [Metric.cauchySeq_iff] at hBcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hBcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hle m n).1 (by rw [← dist_eq_norm]; exact hN m hm n hn)
  have hicauchy : CauchySeq (fun n => ι (f n)) := by
    rw [Metric.cauchySeq_iff] at hBcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hBcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hle m n).2 (by rw [← dist_eq_norm]; exact hN m hm n hn)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hAcauchy
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hicauchy
  have hBtend' : Tendsto (fun n => B (f n)) atTop (𝓝 (w - Complex.I • g)) := by
    have hBn : ∀ n, B (f n) = A (f n) - Complex.I • ι (f n) := fun n => by simp [hB]
    simpa [hBn] using hw.sub (hg.const_smul Complex.I)
  have hlim : w - Complex.I • g = v - Complex.I • u := tendsto_nhds_unique hBtend' hBtend
  have hgw : IsAdjointPair ι A g w := by
    intro φ
    have h1 : Tendsto (fun n => (⟪A (f n), ι φ⟫ : ℂ)) atTop (𝓝 ⟪w, ι φ⟫) :=
      hw.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => (⟪ι (f n), A φ⟫ : ℂ)) atTop (𝓝 ⟪g, A φ⟫) :=
      hg.inner tendsto_const_nhds
    exact tendsto_nhds_unique (h1.congr fun n => hsymm (f n) φ) h2
  have hx : IsAdjointPair ι A (u - g) (Complex.I • (u - g)) := by
    have hvw : v - w = Complex.I • (u - g) := by
      rw [smul_sub]
      rw [sub_eq_sub_iff_sub_eq_sub] at hlim ⊢
      linear_combination (norm := module) -hlim
    intro φ
    rw [← hvw, inner_sub_left, inner_sub_left, huv φ, hgw φ]
  have hzero := eq_zero_of_isAdjointPair_smul_I ι A hpos hx
  have hug : u = g := by rwa [sub_eq_zero] at hzero
  refine ⟨f, hug ▸ hg, ?_⟩
  have hvw : v = w := by
    rw [hug] at hlim
    exact (sub_left_injective (by rw [hlim] : w - Complex.I • g = v - Complex.I • g)).symm
  exact hvw ▸ hw

/-- **Von Neumann's basic criterion**: a densely defined symmetric operator whose ranges
`Ran(A + i)` and `Ran(A - i)` are dense is essentially self-adjoint. -/
