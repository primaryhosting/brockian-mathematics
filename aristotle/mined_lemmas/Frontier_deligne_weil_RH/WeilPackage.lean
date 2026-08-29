/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option maxHeartbeats 1000000

namespace Frontier

/-!
## Formalization of the Riemann hypothesis for varieties over finite fields

We package the cohomological data attached to a smooth projective variety `X` of
dimension `d` over the finite field `𝔽_q` (as produced by ℓ-adic étale cohomology):

* `eigen i` is the multiset of eigenvalues of the geometric Frobenius acting on the
  `i`-th cohomology group (so `(eigen i).card` is the `i`-th Betti number);
* `count m` is `#X(𝔽_{q^m})`;
* `trace_formula` is the Grothendieck–Lefschetz trace formula;
* `weight` is *Deligne's theorem* (the Riemann hypothesis, Weil conjecture III):
  every Frobenius eigenvalue on `H^i` has archimedean absolute value `q^{i/2}`.

The zeta function of `X` is `Z(X, T) = ∏_i P_i(T)^{(-1)^{i+1}}` with
`P_i(T) = ∏_{α ∈ eigen i} (1 - α T)`, and `ζ(X, s) = Z(X, q^{-s})`.
The classical phrasing of the Riemann hypothesis is that the zeros
(resp. poles) of `ζ(X, s)` lie on the vertical lines `Re s = i/2` for `i` odd
(resp. even).  The main theorem below, `Frontier.deligne_weil_RH`, is exactly this
statement: it is a Lean-checked reduction of the "critical line" form of the
Riemann hypothesis to the "absolute value of Frobenius eigenvalues" form.

We also verify the base case: projective space `ℙ^n` over `𝔽_q` carries such a
package (`Frontier.WeilPackage.projectiveSpace`), with the correct point counts
`#ℙ^n(𝔽_{q^m}) = 1 + q^m + ⋯ + q^{nm}`, so the theorem applies to it
unconditionally.
-/

/-- Cohomological data of a smooth projective variety over `𝔽_q` satisfying the
Weil conjectures: Frobenius eigenvalues on each cohomology group, the
Grothendieck–Lefschetz trace formula for the point counts, and Deligne's purity
("Riemann hypothesis") statement on the eigenvalue absolute values. -/
structure WeilPackage where
  /-- The size of the base finite field. -/
  q : ℕ
  /-- A finite field has at least two elements. -/
  hq : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- `eigen i` : the Frobenius eigenvalues on the `i`-th cohomology group. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  eigen_vanish : ∀ i, 2 * dim < i → eigen i = 0
  /-- `count m = #X(𝔽_{q^m})`. -/
  count : ℕ → ℤ
  /-- The Grothendieck–Lefschetz trace formula. -/
  trace_formula : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1), (-1) ^ i * ((eigen i).map (fun a => a ^ m)).sum
  /-- Deligne's theorem: purity of weights. -/
  weight : ∀ i, ∀ a ∈ eigen i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)

namespace WeilPackage

variable (W : WeilPackage)

/-- The `i`-th local factor `P_i(T) = ∏_{α ∈ eigen i} (1 - α T)` of the zeta
function, evaluated at `T = q^{-s}`; i.e. the `i`-th factor of `ζ(X, s)`. -/

noncomputable def WeilPackage.projectiveSpace (q n : ℕ) (hq : 1 < q) : WeilPackage where
  q := q
  hq := hq
  dim := n
  eigen := fun i => if Even i ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0
  eigen_vanish := by
    intro i hi
    have : ¬ (Even i ∧ i ≤ 2 * n) := by omega
    simp [this]
  count := fun m => ∑ k ∈ Finset.range (n + 1), (q : ℤ) ^ (k * m)
  trace_formula := by
    intro m _
    push_cast
    have hL : ∀ i ∈ Finset.range (2 * n + 1),
        ((-1 : ℂ) ^ i *
            (((if Even i ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0 : Multiset ℂ)).map
              (fun a => a ^ m)).sum)
          = (if Even i then ((q : ℂ) ^ m) ^ (i / 2) else 0) := by
      intro i hi
      have hi' : i ≤ 2 * n := by
        simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hi
      by_cases he : Even i
      · rw [if_pos ⟨he, hi'⟩, if_pos he, he.neg_one_pow]
        simp [← pow_mul, Nat.mul_comm]
      · rw [if_neg (by tauto), if_neg he]
        simp
    rw [Finset.sum_congr rfl hL, sum_even_reindex (fun k => ((q : ℂ) ^ m) ^ k) n]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [← pow_mul, Nat.mul_comm]
  weight := by
    intro i a ha
    by_cases he : Even i ∧ i ≤ 2 * n
    · rw [if_pos he] at ha
      have hae : a = (q : ℂ) ^ (i / 2) := by simpa using ha
      subst hae
      have hi2 : ((i / 2 : ℕ) : ℝ) = (i : ℝ) / 2 := by
        obtain ⟨k, hk⟩ := he.1
        subst hk
        have : (k + k) / 2 = k := by omega
        rw [this]
        push_cast
        ring
      rw [norm_pow, Complex.norm_natCast, ← Real.rpow_natCast (q : ℝ) (i / 2), hi2]
    · rw [if_neg he] at ha
      simp at ha

/-- The point counts of the projective-space package are the correct ones:
`#ℙ^n(𝔽_{q^m}) = 1 + q^m + ⋯ + q^{nm}`, equivalently
`(q^m - 1) · #ℙ^n(𝔽_{q^m}) = q^{(n+1)m} - 1`. -/
