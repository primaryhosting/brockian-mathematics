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

lemma mon_univ_eq_sgn_parity {n : ℕ} (x : Bits n) :
    mon (Finset.univ : Finset (Fin n)) x = sgn (parity n x) := by
  classical
  rw [mon, prod_sgn_eq]
  by_cases h : Odd ((Finset.univ.filter (fun i => x i = true)).card)
  · rw [h.neg_one_pow]
    simp [parity, h, sgn]
  · rw [(Nat.not_odd_iff_even.1 h).neg_one_pow]
    simp [parity, h, sgn]

end CS

import RequestProject.Circuit

/-!
# Razborov's approximation of `AC⁰` circuits by low degree `ZMod 3` polynomials

The main result of this file is `CS.exists_approx`: every circuit `C` of depth `d`
and size `s` admits a function `f` in `Deg n ((2ℓ)^d)` (i.e. a polynomial of degree
at most `(2ℓ)^d` over `ZMod 3`, in the `±1` encoding of the cube) which is `0/1`
valued and disagrees with `C` on at most `s * 2^n / 3^ℓ` inputs.
-/

namespace CS

open Finset

section ZMod3

