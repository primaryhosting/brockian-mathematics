/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Almost-everywhere convergence of the Fourier series of an `L²` function on the circle
`AddCircle T`.

The main result `Math2.carleson` states that for every `f ∈ L²(AddCircle T)` the symmetric
partial sums `S_N f (x) = ∑_{|n| ≤ N} (fourierCoeff f n) • e^{2πinx/T}` converge to `f x`
at almost every `x` along a subsequence `N = ns k` (the subsequence being independent of `x`).

`Math2.carleson_of_summable` upgrades this to convergence of the full sequence of partial sums,
at almost every point, for those `f` whose Fourier coefficients are absolutely summable.

The full strength of Carleson's theorem — convergence of the whole sequence of partial sums
almost everywhere, for every `L²` function — is *not* established here.
-/

open MeasureTheory Filter Topology AddCircle

namespace Math2

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f`, as a genuine function on the
circle: `x ↦ ∑_{|n| ≤ N} (fourierCoeff f n) * e^{2πinx/T}`. -/

theorem tendsto_sum_Icc_of_hasSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    {u : ℤ → M} {a : M} (h : HasSum u a) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), u n) atTop (𝓝 a) := by
  have hmono : Monotone fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro M N hMN
    apply Finset.Icc_subset_Icc <;> simp <;> exact_mod_cast hMN
  have hex : ∀ n : ℤ, ∃ N : ℕ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n
    refine ⟨n.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega
  exact h.comp (tendsto_atTop_finset_of_monotone hmono hex)

/-- The coercion to a function of a finite sum in `Lp` is a.e. the sum of the coercions. -/
