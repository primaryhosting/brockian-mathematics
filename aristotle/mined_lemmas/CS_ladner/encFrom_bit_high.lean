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

theorem encFrom_bit_high (d : Nat → Prop) :
    ∀ (len start x : Nat), len ≤ x → ¬ bit (encFrom d start len) x := by
  intro len
  induction len with
  | zero =>
      intro start x _
      show ¬ bit 0 x
      exact bit_high 0 x (Nat.zero_le _)
  | succ len ih =>
      intro start x hx
      have hc := encFrom_lt_two d start
      cases x with
      | zero => exact absurd hx (by omega)
      | succ x =>
          show ¬ bit ((if d start then 1 else 0) + 2 * encFrom d (start + 1) len) (x + 1)
          rw [bit_succ_iff _ _ _ hc]
          exact ih (start + 1) x (by omega)

/-! ### The class of finite variations of constant languages -/

/-- `FC A` says that `A` agrees with a fixed truth value on all large inputs, i.e.
`A` is finite or cofinite. -/
