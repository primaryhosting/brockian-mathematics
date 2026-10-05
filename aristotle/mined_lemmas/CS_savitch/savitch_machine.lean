import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem savitch_machine {s : ℕ} (M : NMachine s) :
    ∃ D : DMachine (9 * (s + 1) ^ 2), D.Halts ∧ (D.Accepts ↔ M.Accepts) := by
  classical
  set n := M.size + 1 with hn
  set K := s + 1 with hK
  have hnle : n ≤ 2 ^ K := by
    have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 := M.hsize
    calc n ≤ 2 ^ s + 1 := by omega
    _ ≤ 2 ^ s + 2 ^ s := by omega
    _ = 2 ^ K := by rw [hK, pow_succ]; ring
  set R := sinkRel M with hR
  set a₀ : Fin n := Fin.castSucc M.start with ha₀
  set b₀ : Fin n := Fin.last M.size with hb₀
  have hanswer : cy R K a₀ b₀ = true ↔ M.Accepts := by
    rw [cy_iff_reachLe, ← reflTransGen_iff_reachLe hnle]
    exact sink_reach_iff M
  have hcard : Fintype.card (Conf n K) ≤ 2 ^ (9 * (s + 1) ^ 2) :=
    le_trans (card_conf_le n K) (savitch_card_bound hnle)
  obtain ⟨D, hacc, hhalt⟩ := exists_dmachine hcard (dstep R K) (dstart a₀ b₀ K)
    (fun c => decide (c = dfinal n K true))
  obtain ⟨N, hN⟩ := dstep_run R K a₀ b₀
  refine ⟨D, ⟨N, (hhalt N).mpr ?_⟩, ?_⟩
  · rw [hN]
    exact dstep_dfinal _
  · constructor
    · rintro ⟨t, ht⟩
      rw [hacc t] at ht
      simp only [decide_eq_true_eq] at ht
      have h1 : (dstep R K)^[N + t] (dstart a₀ b₀ K) = dfinal n K true := by
        rw [Function.iterate_add_apply, ht]
        exact Function.iterate_fixed (dstep_dfinal _) N
      have h2 : (dstep R K)^[t + N] (dstart a₀ b₀ K) = dfinal n K (cy R K a₀ b₀) := by
        rw [Function.iterate_add_apply, hN]
        exact Function.iterate_fixed (dstep_dfinal _) t
      rw [Nat.add_comm, h1] at h2
      exact hanswer.mp (dfinal_inj h2).symm
    · intro hM
      refine ⟨N, ?_⟩
      rw [hacc N, hN, hanswer.mpr hM]
      simp

/-- **Savitch's theorem**: nondeterministic space `f` is contained in deterministic
space `O(f ^ 2)`; concretely `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`. -/
