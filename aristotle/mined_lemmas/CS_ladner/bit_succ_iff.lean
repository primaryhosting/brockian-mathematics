import RequestProject.Main

/-!
# A consistency witness for `CS.LadnerSetup`

`CS.ladner` is stated relative to the abstract axiomatisation `CS.LadnerSetup`.
To rule out the possibility that this package of hypotheses is contradictory
(in which case the theorem would be vacuous), we build an explicit model of it.

The model takes both classes to be the class `FC` of languages that are *finite
variations of a constant language* (equivalently: finite or cofinite sets), which
is enumerable, closed under finite variation, contains the finite languages and is
closed downwards under the reductions of the model; `SAT` is taken to be the
cofinite language `{x | x ≠ 0}`, which is complete for `FC` under those
reductions, and the clock is taken to be constant (so all four clock-semantics
fields hold trivially or vacuously).

Of course `P = NP` holds in this model, so `CS.ladner` says nothing about it; the
point of the construction is only that the hypotheses of `CS.LadnerSetup` are
jointly satisfiable, hence consistent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

namespace FinCofinModel

attribute [local instance] Classical.propDecidable

/-! ### Binary digits -/

/-- `bit n x` says that the `x`-th binary digit of `n` is `1`. -/

theorem bit_succ_iff (c m x : Nat) (hc : c < 2) : bit (c + 2 * m) (x + 1) ↔ bit m x := by
  unfold bit
  have hp : (2 : Nat) ^ (x + 1) = 2 * 2 ^ x := by
    rw [Nat.pow_succ]
    omega
  have hhalf : (c + 2 * m) / 2 = m := by omega
  rw [hp, ← Nat.div_div_eq_div_mul, hhalf]

