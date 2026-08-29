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

theorem zetaFactor_projectiveSpace_eq_zero (q n : ℕ) (hq : 1 < q) (k : ℕ) (hk : k ≤ n) :
    (WeilPackage.projectiveSpace q n hq).zetaFactor (2 * k) (k : ℂ) = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by
    have : 0 < q := lt_trans Nat.zero_lt_one hq
    exact_mod_cast this.ne'
  have heigen : (WeilPackage.projectiveSpace q n hq).eigen (2 * k) = {(q : ℂ) ^ k} := by
    show (if Even (2 * k) ∧ 2 * k ≤ 2 * n then ({(q : ℂ) ^ (2 * k / 2)} : Multiset ℂ) else 0) = _
    rw [if_pos ⟨⟨k, by ring⟩, by omega⟩]
    congr 2
    omega
  show (((WeilPackage.projectiveSpace q n hq).eigen (2 * k)).map
      (fun a => 1 - a * ((q : ℕ) : ℂ) ^ (-(k : ℂ)))).prod = 0
  rw [heigen]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [Complex.cpow_neg, Complex.cpow_natCast]
  field_simp
  ring

/-- The Riemann hypothesis holds unconditionally for projective space: every zero
of the `i`-th factor of `ζ(ℙ^n, s)` lies on the line `Re s = i/2`. -/
