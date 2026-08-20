import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

theorem prod_one_add_mul_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f)
    (dg : DiophFn g) : DiophFn fun v => ∏ i ∈ range (f v), (1 + (i + 1) * g v) := by
  have d1 : DiophFn fun _ : α → ℕ => (1 : ℕ) := const_dioph 1
  have dK : DiophFn fun v => (1 + f v * g v) ^ f v :=
    pow_dioph (add_dioph d1 (mul_dioph df dg)) df
  have dM : DiophFn fun v => g v * (1 + f v * g v) ^ f v + 1 := add_dioph (mul_dioph dg dK) d1
  have dr : DiophFn fun v => (g v - 1) * (1 + f v * g v) ^ f v + 1 :=
    add_dioph (mul_dioph (sub_dioph dg d1) dK) d1
  have dch : DiophFn fun v => ((g v - 1) * (1 + f v * g v) ^ f v + 1 + f v).choose (f v) :=
    choose_dioph (add_dioph dr df) df
  have dnum : DiophFn fun v => g v ^ f v *
      ((f v)! * ((g v - 1) * (1 + f v * g v) ^ f v + 1 + f v).choose (f v)) :=
    mul_dioph (pow_dioph dg df) (mul_dioph (factorial_dioph df) dch)
  have hd := add_dioph (mod_dioph dnum dM) (sub_dioph d1 dg)
  have heq : (fun v => ∏ i ∈ range (f v), (1 + (i + 1) * g v))
      = fun v => g v ^ f v * ((f v)! *
          ((g v - 1) * (1 + f v * g v) ^ f v + 1 + f v).choose (f v))
            % (g v * (1 + f v * g v) ^ f v + 1) + (1 - g v) :=
    funext fun v => prod_formula _ _
  rw [heq]
  exact hd

end CS

/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command of a file, so the header above is written
-- as a plain comment and repeated as a module docstring below.)

import Mathlib
import RequestProject.DiophAux

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `CS.haltSet`, `CS.haltSet_re`, `CS.haltSet_not_computable`: the halting problem, transported
  from `Nat.Partrec.Code` to a subset of `ℕ`.
* `CS.MRDP`: the statement of the Matiyasevich–Robinson–Davis–Putnam theorem ("every recursively
  enumerable set of naturals is Diophantine").  Mathlib contains the deepest number-theoretic
  ingredient of its proof (`Dioph.pow_dioph`, Matiyasevich's theorem that exponentiation is
  Diophantine) but not the theorem itself; see the `TODO` in `Mathlib/NumberTheory/Dioph.lean`
  ("Finish the solution of Hilbert's tenth problem").  It is therefore taken here as an explicit
  hypothesis of `CS.hilbert10_undecidable` rather than being reproved.
* `CS.hilbert10_undecidable`: **Hilbert's tenth problem is undecidable**.  Assuming `MRDP`, there
  is a single integer polynomial `p` in one distinguished parameter and finitely many further
  unknowns such that no algorithm decides, given the parameter `a`, whether `p (a, t) = 0` is
  solvable in natural numbers `t`.
* `CS.dioph_rePred` and `CS.dioph_iff_rePred`: the converse (easy) half of MRDP, proved
  unconditionally: every Diophantine subset of `ℕ` is recursively enumerable.  Consequently
  Diophantine sets are exactly the recursively enumerable sets if and only if `MRDP` holds.

The file `RequestProject/DiophAux.lean` contains further unconditional steps towards MRDP that go
beyond Mathlib: binomial coefficients (`CS.choose_dioph`), factorials (`CS.factorial_dioph`) and
the products `∏_{k=1}^{y} (1 + k * t)` (`CS.prod_one_add_mul_dioph`) are Diophantine functions.
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ## The halting set, transported to `ℕ` -/

/-- The halting set: `n ∈ haltSet` iff the `n`-th partial recursive program halts on input `0`. -/
