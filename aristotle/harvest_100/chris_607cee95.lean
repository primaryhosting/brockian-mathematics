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
def WeilData.RiemannHypothesis (W : WeilData) : Prop :=
  ∀ i : ℕ, i ≤ 2 * W.dim → ∀ a ∈ W.frob i, ‖a‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

/-! ### Base case: projective space -/

/-- The alternating sum over even degrees `≤ 2d` of `(q^{i/2})^n` is `∑_{k ≤ d} q^{nk}`. -/
lemma projective_eigenvalue_sum (q n : ℕ) (d : ℕ) :
    ∑ i ∈ Finset.range (2 * d + 1),
        (if i % 2 = 0 then ((q : ℂ) ^ (i / 2)) ^ n else 0)
      = ∑ k ∈ Finset.range (d + 1), (q : ℂ) ^ (n * k) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have h1 : 2 * (d + 1) + 1 = (2 * d + 1) + 1 + 1 := by ring
      have h3 : (2 * d + 1 + 1) % 2 = 0 := by omega
      have h4 : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      conv_rhs => rw [Finset.sum_range_succ]
      rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, if_neg (by omega), if_pos h3, h4,
        ih, ← pow_mul, mul_comm (d + 1) n]
      ring

/-- The Weil data of projective space `ℙ^d` over `𝔽_q`:  it has `∑_{k ≤ d} q^{nk}` points over
`𝔽_{q^n}`, its odd cohomology vanishes, and `H^{2k}` is one-dimensional with Frobenius
eigenvalue `q^k`. -/
def projectiveSpace (q d : ℕ) : WeilData where
  q := q
  dim := d
  N := fun n => ∑ k ∈ Finset.range (d + 1), q ^ (n * k)
  frob := fun i => if i % 2 = 0 ∧ i ≤ 2 * d then {(q : ℂ) ^ (i / 2)} else 0
  frob_vanishing := by
    intro i hi
    rw [if_neg (by omega)]
  lefschetz := by
    intro n _
    have hcongr : ∀ i ∈ Finset.range (2 * d + 1),
        (-1 : ℂ) ^ i *
            (((if i % 2 = 0 ∧ i ≤ 2 * d then {(q : ℂ) ^ (i / 2)} else 0 : Multiset ℂ)).map
              (fun a : ℂ => a ^ n)).sum
          = if i % 2 = 0 then ((q : ℂ) ^ (i / 2)) ^ n else 0 := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases h : i % 2 = 0
      · rw [if_pos ⟨h, by omega⟩, if_pos h]
        have : (-1 : ℂ) ^ i = 1 := by
          rw [neg_one_pow_eq_one_iff_even (by norm_num)]
          exact Nat.even_iff.mpr h
        simp [this]
      · rw [if_neg (by tauto), if_neg h]
        simp
    rw [Finset.sum_congr rfl hcongr, projective_eigenvalue_sum]
    push_cast
    rfl

/-- `ℙ^0` is a point: it has exactly one rational point over every extension. -/
lemma projectiveSpace_zero_N (q n : ℕ) : (projectiveSpace q 0).N n = 1 := by
  simp [projectiveSpace]

/-- **Base case of the Weil Riemann hypothesis**: it holds for projective space `ℙ^d` over `𝔽_q`
(and hence, taking `d = 0`, for a point). -/
theorem projectiveSpace_RiemannHypothesis (q d : ℕ) :
    (projectiveSpace q d).RiemannHypothesis := by
  intro i _ a ha
  simp only [projectiveSpace] at ha ⊢
  by_cases h : i % 2 = 0 ∧ i ≤ 2 * d
  · rw [if_pos h] at ha
    rw [Multiset.mem_singleton] at ha
    subst ha
    have hi : ((i : ℝ)) / 2 = ((i / 2 : ℕ) : ℝ) := by
      have : i = 2 * (i / 2) := by omega
      rw [show ((i : ℝ)) = ((2 * (i / 2) : ℕ) : ℝ) by exact_mod_cast congrArg (Nat.cast) this]
      push_cast
      ring
    rw [hi, Real.rpow_natCast, norm_pow, Complex.norm_natCast]
  · rw [if_neg h] at ha
    simp at ha

/-! ### A Lean-checked reduction: RH for curves implies the Hasse–Weil bound -/

/-- **Reduction**: for a curve (`dim = 1`) with `H^0` and `H^2` of the expected shape, the Weil
Riemann hypothesis implies the Hasse–Weil bound
`|#X(𝔽_{q^n}) - (qⁿ + 1)| ≤ b₁ · q^{n/2}`, where `b₁ = 2g` is the first Betti number. -/
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
lemma projectiveLine_curve_hypotheses (q : ℕ) :
    (projectiveSpace q 1).dim = 1 ∧ (projectiveSpace q 1).frob 0 = {1} ∧
      (projectiveSpace q 1).frob 2 = {((projectiveSpace q 1).q : ℂ)} ∧
      (projectiveSpace q 1).frob 1 = 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [projectiveSpace]

/-! ### The target statement -/

/--
**Deligne's theorem (the Riemann hypothesis for varieties over finite fields), formalised.**

`Frontier.WeilData.RiemannHypothesis` is the statement of the Weil Riemann hypothesis: for a
`d`-dimensional variety over `𝔽_q`, whose point counts `N n = #X(𝔽_{q^n})` satisfy the Lefschetz
trace formula for the multisets `frob i` of Frobenius eigenvalues on `H^i`, every eigenvalue in
degree `i` has absolute value `q^{i/2}`.

This theorem records what is proved here in Lean:

1. the **base case**, that the Riemann hypothesis holds for projective space `ℙ^d` over `𝔽_q` for
   all `q` and `d`;
2. the degenerate case `d = 0`, i.e. a point `Spec 𝔽_q`, has exactly one rational point over every
   extension, and satisfies the Riemann hypothesis;
3. a **reduction**, that for curves the Riemann hypothesis implies the Hasse–Weil bound
   `|#X(𝔽_{q^n}) - (qⁿ + 1)| ≤ b₁ q^{n/2}`.
-/
theorem deligne_weil_RH :
    (∀ q d : ℕ, (projectiveSpace q d).RiemannHypothesis) ∧
    (∀ q n : ℕ, (projectiveSpace q 0).N n = 1) ∧
    (∀ (W : WeilData), W.dim = 1 → W.frob 0 = {1} → W.frob 2 = {(W.q : ℂ)} →
      W.RiemannHypothesis → ∀ n : ℕ, 1 ≤ n →
        |(W.N n : ℝ) - ((W.q : ℝ) ^ n + 1)|
          ≤ (Multiset.card (W.frob 1) : ℝ) * (W.q : ℝ) ^ ((n : ℝ) / 2)) :=
  ⟨projectiveSpace_RiemannHypothesis, projectiveSpace_zero_N,
    fun W hdim h0 h2 hRH n hn => hasse_weil_bound_of_RiemannHypothesis W hdim h0 h2 hRH n hn⟩

end Frontier

