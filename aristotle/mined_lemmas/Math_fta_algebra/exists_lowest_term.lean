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

theorem exists_lowest_term (q : ℂ[X]) (hq : 0 < q.natDegree) :
    ∃ (k : ℕ) (r : ℂ[X]), 0 < k ∧ r.eval 0 ≠ 0 ∧ q = C (q.eval 0) + X ^ k * r := by
  classical
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  have hlead : q.coeff q.natDegree ≠ 0 := fun h => hq0 (leadingCoeff_eq_zero.mp h)
  have hex : ∃ n, 0 < n ∧ q.coeff n ≠ 0 := ⟨q.natDegree, hq, hlead⟩
  obtain ⟨hk0, hkne⟩ : 0 < Nat.find hex ∧ q.coeff (Nat.find hex) ≠ 0 := Nat.find_spec hex
  set k := Nat.find hex with hkdef
  have hmin : ∀ d, 0 < d → d < k → q.coeff d = 0 := by
    intro d hd0 hd
    by_contra hc
    exact absurd (Nat.find_le ⟨hd0, hc⟩) (not_le.mpr hd)
  have hdvd : (X : ℂ[X]) ^ k ∣ (q - C (q.eval 0)) := by
    rw [X_pow_dvd_iff]
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp [coeff_zero_eq_eval_zero]
    · simp only [coeff_sub, coeff_C, if_neg (by omega : ¬ d = 0), sub_zero, hmin d hd0 hd]
  obtain ⟨r, hr⟩ := hdvd
  have hcoef : r.coeff 0 = q.coeff k := by
    have h2 := congrArg (fun f => Polynomial.coeff f k) hr
    simp only [coeff_sub, coeff_C, if_neg (by omega : ¬ k = 0), sub_zero] at h2
    have h3 : (X ^ k * r).coeff k = r.coeff 0 := by simpa using coeff_X_pow_mul r k 0
    rw [h3] at h2
    exact h2.symm
  refine ⟨k, r, hk0, ?_, by linear_combination (norm := ring_nf) hr⟩
  rw [← coeff_zero_eq_eval_zero, hcoef]
  exact hkne

/-- d'Alembert's lemma at the origin: if `q` is nonconstant and `q.eval 0 ≠ 0`, then `‖q.eval ·‖`
takes a strictly smaller value somewhere. -/
