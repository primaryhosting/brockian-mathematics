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

theorem encFrom_bit (d : Nat → Prop) :
    ∀ (len start x : Nat), x < len → (bit (encFrom d start len) x ↔ d (start + x)) := by
  intro len
  induction len with
  | zero =>
      intro start x hx
      exact absurd hx (Nat.not_lt_zero x)
  | succ len ih =>
      intro start x hx
      have hc := encFrom_lt_two d start
      cases x with
      | zero =>
          show bit ((if d start then 1 else 0) + 2 * encFrom d (start + 1) len) 0 ↔ _
          rw [bit_zero_iff _ _ hc]
          have hzero : start + 0 = start := by omega
          rw [hzero]
          by_cases hd : d start
          · rw [if_pos hd]
            exact ⟨fun _ => hd, fun _ => rfl⟩
          · rw [if_neg hd]
            exact ⟨fun hcc => absurd hcc (by omega), fun hcc => absurd hcc hd⟩
      | succ x =>
          show bit ((if d start then 1 else 0) + 2 * encFrom d (start + 1) len) (x + 1) ↔ _
          rw [bit_succ_iff _ _ _ hc, ih (start + 1) x (by omega)]
          have hs : start + 1 + x = start + (x + 1) := by omega
          rw [hs]

