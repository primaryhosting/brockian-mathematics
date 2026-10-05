/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The proof below is the classical d'Alembert–Argand ("minimum modulus") argument:

* `FTA.exists_pow_eq`: every complex number has `n`-th roots (via `exp`/`log`);
* `FTA.exists_lowest_term`: a nonconstant polynomial can be written `C (q.eval 0) + X ^ k * r`
  with `k ≥ 1` and `r.eval 0 ≠ 0`;
* `FTA.exists_norm_lt`: d'Alembert's lemma — at a point which is not a root, `‖p‖` is not
  minimal;
* `Math.fta_algebra`: since `‖p.eval ·‖` attains a global minimum (it tends to infinity at
  infinity), that minimum must be `0`.

It does not use `Complex.exists_root` or the `IsAlgClosed ℂ` instance from Mathlib.
-/

open Polynomial

namespace FTA

/-- Every complex number has an `n`-th root for `n ≠ 0`. -/

theorem exists_norm_lt (p : ℂ[X]) (hp : 0 < p.natDegree) (z₀ : ℂ) (h : p.eval z₀ ≠ 0) :
    ∃ z : ℂ, ‖p.eval z‖ < ‖p.eval z₀‖ := by
  set q := p.comp (X + C z₀) with hq
  have hev : ∀ z : ℂ, q.eval z = p.eval (z + z₀) := by
    intro z; simp [hq, eval_comp]
  have hdeg : 0 < q.natDegree := by
    rw [hq, natDegree_comp]; simpa using hp
  have h0 : q.eval 0 ≠ 0 := by rw [hev]; simpa using h
  obtain ⟨z, hz⟩ := exists_norm_lt_zero q hdeg h0
  rw [hev, hev] at hz
  exact ⟨z + z₀, by simpa using hz⟩

end FTA

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root. -/
