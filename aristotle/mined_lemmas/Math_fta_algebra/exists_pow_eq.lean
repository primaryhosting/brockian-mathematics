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

theorem exists_pow_eq (a : ℂ) {n : ℕ} (hn : n ≠ 0) : ∃ w : ℂ, w ^ n = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp [hn]⟩
  · refine ⟨Complex.exp (Complex.log a / n), ?_⟩
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn), Complex.exp_log ha]

/-- A nonconstant polynomial can be written as `q = C (q.eval 0) + X ^ k * r` where `k ≥ 1`
and `r.eval 0 ≠ 0`. -/
