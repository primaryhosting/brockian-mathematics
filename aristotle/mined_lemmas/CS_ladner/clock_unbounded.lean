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

theorem clock_unbounded (hPNP : S.P ≠ S.NP) : ∀ n : Nat, ∃ x : Nat, n < S.clock x := by
  intro n
  apply Classical.byContradiction
  intro hcontra
  have hcon : ∀ x : Nat, S.clock x ≤ n := by
    intro x
    apply Classical.byContradiction
    intro hx
    exact hcontra ⟨x, by omega⟩
  obtain ⟨c, N, hcN⟩ := eventually_const_of_bounded n S.clock S.clock_mono hcon
  rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with hc | hc
  · -- stuck at an even stage: `SAT` is a finite variant of `pEnum i ∈ P`
    refine S.SAT_not_mem_P hPNP ?_
    obtain ⟨i, hi⟩ : ∃ i : Nat, c = 2 * i := ⟨c / 2, by omega⟩
    have hstage : ∀ x : Nat, N ≤ x → S.clock x = 2 * i := by
      intro x hx
      rw [hcN x hx, hi]
    have hagree := S.clock_stuck_even i N hstage
    have hmem : S.P (S.pEnum i) := (S.P_iff_range _).2 ⟨i, fun _ => Iff.rfl⟩
    exact S.P_finVar (S.pEnum i) S.SAT hmem ⟨N, fun x hx => (hagree x hx).symm⟩
  · -- stuck at an odd stage: Ladner's language is finite and `SAT` reduces to it
    refine S.SAT_not_mem_P hPNP ?_
    obtain ⟨i, hi⟩ : ∃ i : Nat, c = 2 * i + 1 := ⟨c / 2, by omega⟩
    have hstage : ∀ x : Nat, N ≤ x → S.clock x = 2 * i + 1 := by
      intro x hx
      rw [hcN x hx, hi]
    have hred := S.clock_stuck_odd i N hstage
    have hfin : S.P (fun x => S.SAT x ∧ S.clock x % 2 = 0) := by
      refine S.P_finite _ ⟨N, ?_⟩
      intro x hx hmem
      have h1 := hstage x hx
      have h2 := hmem.2
      omega
    exact S.P_reduce _ _ ⟨i, hred⟩ hfin

/-- Ladner's language lies in `NP`. -/
