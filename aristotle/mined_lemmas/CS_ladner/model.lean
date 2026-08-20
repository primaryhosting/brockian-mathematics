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

noncomputable def model : LadnerSetup where
  P := FC
  NP := FC
  SAT := satL
  pEnum := pEnumM
  redEnum := redEnumM
  clock := fun _ => 0
  P_iff_range := by
    intro A
    constructor
    · intro hA
      obtain ⟨n, hn⟩ := FC_exists_code hA
      exact ⟨n + 1, fun x => Iff.trans (hn x) (pEnumM_succ n x).symm⟩
    · intro h
      obtain ⟨i, hi⟩ := h
      exact FC_congr (fun x => (hi x).symm) (pEnumM_FC i)
  P_subset_NP := fun _ h => h
  SAT_mem_NP := satL_FC
  SAT_hard := by
    intro A hA
    obtain ⟨n, hn⟩ := FC_exists_code hA
    exact ⟨n, fun x => Iff.trans (hn x) (redEnumM_spec n x).symm⟩
  P_reduce := by
    intro A B h _
    obtain ⟨i, hi⟩ := h
    obtain ⟨N, b, hb⟩ := dec_FC i
    by_cases hbb : b
    · refine ⟨N, B 1, fun x hx => ?_⟩
      have hd : dec i x := (hb x hx).mpr hbb
      have hval : redEnumM i x = 1 := by unfold redEnumM; rw [if_pos hd]
      rw [hi x, hval]
    · refine ⟨N, B 0, fun x hx => ?_⟩
      have hd : ¬ dec i x := fun hc => hbb ((hb x hx).mp hc)
      have hval : redEnumM i x = 0 := by unfold redEnumM; rw [if_neg hd]
      rw [hi x, hval]
  P_finVar := by
    intro A B hA h
    obtain ⟨N₁, b, hb⟩ := hA
    obtain ⟨N₂, hN₂⟩ := h
    exact ⟨N₁ + N₂, b, fun x hx => Iff.trans (hN₂ x (by omega)).symm (hb x (by omega))⟩
  P_finite := by
    intro A h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, False, fun x hx => ⟨fun hAx => hN x hx hAx, fun hf => hf.elim⟩⟩
  NP_inter_P := by
    intro A B hA hB
    obtain ⟨N₁, b₁, hb₁⟩ := hA
    obtain ⟨N₂, b₂, hb₂⟩ := hB
    refine ⟨N₁ + N₂, b₁ ∧ b₂, fun x hx => ?_⟩
    have h1 := hb₁ x (by omega)
    have h2 := hb₂ x (by omega)
    exact ⟨fun h => ⟨h1.1 h.1, h2.1 h.2⟩, fun h => ⟨h1.2 h.1, h2.2 h.2⟩⟩
  clock_mono := fun _ _ _ => Nat.le_refl 0
  gap_mem_P := ⟨0, True, fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩⟩
  clock_stuck_even := by
    intro i N h x _
    have h0 : (0 : Nat) = 2 * i := h N (Nat.le_refl N)
    have hi : i = 0 := by omega
    subst hi
    unfold pEnumM
    rw [if_pos rfl]
  clock_stuck_odd := by
    intro i N h
    have h0 : (0 : Nat) = 2 * i + 1 := h N (Nat.le_refl N)
    exact absurd h0 (by omega)
  clock_pass_even := by
    intro i h
    obtain ⟨x, hx⟩ := h
    exact absurd hx (Nat.not_lt_zero _)
  clock_pass_odd := by
    intro i h
    obtain ⟨x, hx⟩ := h
    exact absurd hx (Nat.not_lt_zero _)

end FinCofinModel

/-- The hypotheses packaged in `CS.LadnerSetup` are consistent: they have a model.
(In that model `P = NP`, so `CS.ladner` applies to it only vacuously; the purpose of
the model is exactly to show that the axiomatisation is satisfiable.) -/
