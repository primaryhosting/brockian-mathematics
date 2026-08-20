/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We generalize the `D₅` (regular pentagon) representation picture to arbitrary regular
`n`-gons.  Concretely, for `n ≠ 0` we build

* `Brockian.zpowRoot n m = exp (2πi·m/n)`, the `n`-th roots of unity indexed by `ℤ`;
* `Brockian.vertex n k`, the vertices of the regular `n`-gon, indexed by `ZMod n`;
* `Brockian.rho n`, the standard two dimensional real representation of
  `DihedralGroup n` realized on `ℂ` (rotations act by multiplication by a root of unity,
  reflections by a root of unity times complex conjugation);
* `Brockian.act n`, the combinatorial action of `DihedralGroup n` on the vertex labels
  `ZMod n`.

The main theorem `Brockian.PentagonPentagonEquivarianceGeneral` states that `rho` is a
representation, that `act` is an action, and that the vertex map
`vertex n : ZMod n → ℂ` is an injective equivariant map between them.  Specializing to
`n = 5` recovers the pentagon statement (`Brockian.pentagon_equivariance`).
-/

namespace Brockian

open Complex

section Aux

/-- `((a.val : ℕ) : ZMod n) = a`. -/

lemma zpowRoot_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ} (h : (a : ZMod n) = (b : ZMod n)) :
    zpowRoot n a = zpowRoot n b := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  obtain ⟨q, hq⟩ : (n : ℤ) ∣ a - b := by
    have h2 : ((a - b : ℤ) : ZMod n) = 0 := by push_cast [h]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have ha : a = b + n * q := by omega
  have hone : zpowRoot n ((n : ℤ) * q) = 1 := by
    unfold zpowRoot
    have hrw : (2 * Real.pi * Complex.I * (((n : ℤ) * q : ℤ) : ℂ) / (n : ℂ))
        = (q : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [hrw, Complex.exp_int_mul_two_pi_mul_I]
  rw [ha, zpowRoot_add, hone, mul_one]

