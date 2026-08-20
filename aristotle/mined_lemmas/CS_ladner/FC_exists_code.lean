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

theorem FC_exists_code {A : Lang} (hA : FC A) : ∃ n : Nat, ∀ x, (A x ↔ dec n x) := by
  obtain ⟨N, b, hb⟩ := hA
  by_cases hbb : b
  · -- the eventual value is `True`; encode the positions where `A` fails
    refine ⟨1 + 2 * encFrom (fun y => ¬ A y) 0 N, fun x => ?_⟩
    have hmod : (1 + 2 * encFrom (fun y => ¬ A y) 0 N) % 2 = 1 := by omega
    have hdiv : (1 + 2 * encFrom (fun y => ¬ A y) 0 N) / 2
        = encFrom (fun y => ¬ A y) 0 N := by omega
    unfold dec
    rw [hmod, hdiv, if_pos rfl]
    by_cases hx : x < N
    · have hbit := encFrom_bit (fun y => ¬ A y) N 0 x hx
      have hzero : 0 + x = x := by omega
      rw [hzero] at hbit
      rw [hbit]
      exact ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩
    · have hbit := encFrom_bit_high (fun y => ¬ A y) N 0 x (by omega)
      have hAx : A x := (hb x (by omega)).mpr hbb
      exact ⟨fun _ => hbit, fun _ => hAx⟩
  · -- the eventual value is `False`; encode the positions where `A` holds
    refine ⟨2 * encFrom (fun y => A y) 0 N, fun x => ?_⟩
    have hmod : (2 * encFrom (fun y => A y) 0 N) % 2 = 0 := by omega
    have hdiv : (2 * encFrom (fun y => A y) 0 N) / 2 = encFrom (fun y => A y) 0 N := by omega
    unfold dec
    rw [hmod, hdiv, if_neg (by omega : ¬ (0 = 1))]
    by_cases hx : x < N
    · have hbit := encFrom_bit (fun y => A y) N 0 x hx
      have hzero : 0 + x = x := by omega
      rw [hzero] at hbit
      exact hbit.symm
    · have hbit := encFrom_bit_high (fun y => A y) N 0 x (by omega)
      have hAx : ¬ A x := fun hc => hbb ((hb x (by omega)).mp hc)
      exact ⟨fun hc => absurd hc hAx, fun hc => absurd hc hbit⟩

/-! ### The model -/

/-- The complete language of the model. -/
