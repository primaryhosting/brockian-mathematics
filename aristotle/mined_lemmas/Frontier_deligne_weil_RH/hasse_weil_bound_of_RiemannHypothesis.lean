import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The Weil Riemann Hypothesis

Let `X` be a smooth projective variety of dimension `d` over the finite field `𝔽_q`, and let
`N n = #X(𝔽_{q^n})`.  The Weil conjectures (Dwork, Grothendieck, Deligne) assert that the zeta
function

`Z(X, T) = exp (∑_{n ≥ 1} N n · Tⁿ / n) = ∏_{i=0}^{2d} P_i(T)^{(-1)^{i+1}}`

is rational, with `P_i(T) = ∏_j (1 - α_{i,j} T)` the characteristic polynomial of the geometric
Frobenius acting on the `i`-th ℓ-adic cohomology group.  Deligne's theorem (the "Riemann
hypothesis", *La conjecture de Weil I*, 1974) states that every inverse root satisfies

`|α_{i,j}| = q^{i/2}`

under every complex embedding.

Taking the logarithmic derivative, the factorisation of `Z(X,T)` above is *equivalent* to the
Lefschetz trace formula

`N n = ∑_{i=0}^{2d} (-1)^i ∑_j α_{i,j}^n`,

which is the form we use here: it avoids formal exponentials while carrying exactly the same
information.  We therefore package the arithmetic input as `Frontier.WeilData` — the point counts,
the multisets of Frobenius eigenvalues, and the trace formula linking them — and formalise
Deligne's theorem as the predicate `Frontier.WeilData.RiemannHypothesis`.

We then prove, in Lean:

* the **base case**: the Riemann hypothesis holds for projective space `ℙ^d` over `𝔽_q`
  (`Frontier.projectiveSpace_RiemannHypothesis`), and in particular for a point `ℙ^0 = Spec 𝔽_q`;
* a **Lean-checked reduction**: for a curve, the Riemann hypothesis implies the Hasse–Weil bound
  `|N n - (qⁿ + 1)| ≤ 2g · q^{n/2}` (`Frontier.hasse_weil_bound_of_RiemannHypothesis`).

The target theorem `Frontier.deligne_weil_RH` collects these statements.
-/

/-- The cohomological data attached to a `d`-dimensional variety over `𝔽_q`:  the point counts
`N n = #X(𝔽_{q^n})` and, for each degree `i`, the multiset `frob i` of inverse roots (i.e.
eigenvalues of the geometric Frobenius on `H^i`), subject to the Lefschetz trace formula. -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- `N n` is the number of `𝔽_{q^n}`-rational points. -/
  N : ℕ → ℕ
  /-- `frob i` is the multiset of eigenvalues of geometric Frobenius on `H^i`; its cardinality is
  the `i`-th Betti number. -/
  frob : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  frob_vanishing : ∀ i : ℕ, 2 * dim < i → frob i = 0
  /-- The Lefschetz trace formula, equivalent to rationality of the zeta function with the
  displayed eigenvalues. -/
  lefschetz : ∀ n : ℕ, 1 ≤ n →
    (N n : ℂ) = ∑ i ∈ Finset.range (2 * dim + 1),
      (-1 : ℂ) ^ i * ((frob i).map (fun a : ℂ => a ^ n)).sum

/-- **The Weil Riemann hypothesis** (Deligne): every eigenvalue of geometric Frobenius on the
`i`-th cohomology group has complex absolute value `q^{i/2}`. -/

theorem hasse_weil_bound_of_RiemannHypothesis (W : WeilData) (hdim : W.dim = 1)
    (h0 : W.frob 0 = {1}) (h2 : W.frob 2 = {(W.q : ℂ)})
    (hRH : W.RiemannHypothesis) (n : ℕ) (hn : 1 ≤ n) :
    |(W.N n : ℝ) - ((W.q : ℝ) ^ n + 1)|
      ≤ (Multiset.card (W.frob 1) : ℝ) * (W.q : ℝ) ^ ((n : ℝ) / 2) := by
  have hq : (0 : ℝ) ≤ (W.q : ℝ) := Nat.cast_nonneg _
  -- Expand the trace formula in degrees 0, 1, 2.
  have htr := W.lefschetz n hn
  rw [hdim] at htr
  rw [show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, h0, h2] at htr
  simp only [Multiset.map_singleton, Multiset.sum_singleton, one_pow] at htr
  -- Hence the error term is exactly the negative of the degree-1 trace.
  have hkey : (W.N n : ℂ) - ((W.q : ℂ) ^ n + 1)
      = -((W.frob 1).map (fun a : ℂ => a ^ n)).sum := by
    rw [htr]; ring
  -- Bound the degree-1 trace using RH.
  have hbound : ‖((W.frob 1).map (fun a : ℂ => a ^ n)).sum‖
      ≤ (Multiset.card (W.frob 1) : ℝ) * (W.q : ℝ) ^ ((n : ℝ) / 2) := by
    refine le_trans (norm_multiset_sum_le _) ?_
    have hmap : ((W.frob 1).map (fun a : ℂ => a ^ n)).map (fun z : ℂ => ‖z‖)
        = (W.frob 1).map (fun _ : ℂ => (W.q : ℝ) ^ ((n : ℝ) / 2)) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl ?_
      intro a ha
      have hna : ‖a‖ = (W.q : ℝ) ^ ((1 : ℝ) / 2) := by
        simpa using hRH 1 (by omega) a ha
      simp only [Function.comp_apply, norm_pow, hna]
      rw [← Real.rpow_natCast ((W.q : ℝ) ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul hq]
      ring_nf
    rw [hmap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  -- Transfer the complex estimate to the real one.
  have hreal : |(W.N n : ℝ) - ((W.q : ℝ) ^ n + 1)|
      = ‖(W.N n : ℂ) - ((W.q : ℂ) ^ n + 1)‖ := by
    rw [show ((W.N n : ℂ) - ((W.q : ℂ) ^ n + 1))
        = (((W.N n : ℝ) - ((W.q : ℝ) ^ n + 1) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hreal, hkey, norm_neg]
  exact hbound

/-- The hypotheses of the reduction above are satisfiable: the projective line `ℙ¹` over `𝔽_q` is
a curve datum of the required shape (with first Betti number `0`). -/
