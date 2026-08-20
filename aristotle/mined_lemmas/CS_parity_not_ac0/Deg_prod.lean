import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

lemma Deg_prod {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fn n) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg n (k i)) : (∏ i ∈ s, f i) ∈ Deg n (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact Deg_mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

end CS

import RequestProject.Basic

/-!
# Counting estimates

Three elementary estimates used in the final assembly:

* `CS.centralBinom_sq_mul_le` : `C(2m, m)^2 * (3m+1) ≤ 16^m`, the standard
  `C(2m,m) ≤ 4^m / √(3m+1)` bound in square-free form;
* `CS.card_subsets_le` : the number of subsets of a `2m`-element set of size at
  most `m + D` is at most `4^m / 2 + (D+1) * C(2m,m)`;
* `CS.exists_two_pow_dominates` : exponentials beat polynomials.
-/

namespace CS

open Finset

/-- `C(2m,m)^2 * (3m+1) ≤ 16^m`, i.e. `C(2m,m) ≤ 4^m / √(3m+1)`. -/
