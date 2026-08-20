/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Hereditary base representations

For a base `b ≥ 2`, every positive natural number `n` can be written as
`n = b ^ e * c + r` with `e = Nat.log b n`, `1 ≤ c < b` and `r < b ^ e`, and iterating this
inside the exponent yields the *hereditary base-`b` representation* of `n`.

Two operations are defined by this recursion:

* `ordOf b n` : the ordinal obtained by replacing the base `b` by `ω` in the hereditary
  base-`b` representation of `n` (a "Goodstein ordinal", an ordinal `< ε₀`);
* `shiftBase b n` : the natural number obtained by replacing the base `b` by `b + 1`
  in the hereditary base-`b` representation of `n`.
-/


lemma ordOf_shiftBase {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ordOf (b + 1) (shiftBase b n) = ordOf b n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn : n ≠ 0 := by omega
    have hb1 : 2 ≤ b + 1 := by omega
    set e := Nat.log b n with he
    set c := n / b ^ e with hc
    set r := n % b ^ e with hr
    have heN : e < n := Nat.log_lt_self b hn
    have hrlt : r < b ^ e := Nat.mod_lt _ (pow_log_pos b n)
    have hrn : r < n := mod_pow_log_lt b n hn
    have hcpos : 0 < c := div_pow_log_pos hn
    have hcb : c < b := div_pow_log_lt hb
    set E := shiftBase b e with hE
    set R := shiftBase b r with hR
    have hSE : ordOf (b + 1) E = ordOf b e := IH e heN
    have hSR : ordOf (b + 1) R = ordOf b r := IH r hrn
    have hRlt : R < (b + 1) ^ E := by
      have h1 : ordOf (b + 1) R < ordOf (b + 1) ((b + 1) ^ E) := by
        rw [hSR, ordOf_pow hb1 E, hSE]
        exact ordOf_lt_opow hb hrlt
      exact (ordOf_strictMono hb1).lt_iff_lt.mp h1
    have hS : shiftBase b n = (b + 1) ^ E * c + R := shiftBase_eq_of_ne_zero hn
    have hSne : shiftBase b n ≠ 0 := shiftBase_ne_zero hn
    have hlog : Nat.log (b + 1) (shiftBase b n) = E := by
      refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
      · rw [hS]
        have : (b + 1) ^ E ≤ (b + 1) ^ E * c := Nat.le_mul_of_pos_right _ hcpos
        omega
      · rw [hS, pow_succ]
        have h2 : (b + 1) ^ E * c + (b + 1) ^ E = (b + 1) ^ E * (c + 1) := by ring
        have h3 : (b + 1) ^ E * (c + 1) ≤ (b + 1) ^ E * (b + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    have hdiv : shiftBase b n / (b + 1) ^ E = c := by
      rw [hS, Nat.mul_add_div (pow_pos (Nat.succ_pos b) _), Nat.div_eq_of_lt hRlt, Nat.add_zero]
    have hmod : shiftBase b n % (b + 1) ^ E = R := by
      rw [hS, Nat.mul_add_mod, Nat.mod_eq_of_lt hRlt]
    rw [ordOf_eq_of_ne_zero hSne, hlog, hdiv, hmod, hSE, hSR, ordOf_eq_of_ne_zero hn]

/-! ## The Goodstein ordinals lie below `ε₀`

The ordinals `ordOf b n` used as the termination measure are exactly the ordinals `< ε₀`
occurring in the usual proof of Goodstein's theorem; this is the point where the
(unprovable in `PA`) well-foundedness of `ε₀` is used. -/

