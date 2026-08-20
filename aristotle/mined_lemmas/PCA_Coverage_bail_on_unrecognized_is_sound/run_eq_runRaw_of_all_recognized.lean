/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The model

An *isolation engine* processes a stream of events.  Each event is either
*recognized* (it lies inside the engine's verified coverage fragment) or not.
Recognized events are handled by the engine's `step` function; unrecognized
events cause the engine to *bail* into a designated safe fallback (`bail`).

The soundness statement we prove is the central design justification for this
architecture: to know that a safety invariant `Inv` holds along **every**
execution, it suffices to verify `step` on the **recognized** fragment only,
together with the (single, event-independent) fact that bailing is safe.

The development is self-contained: it needs nothing beyond Lean 4 core, so the
file has no imports.  (Mathlib's `List.foldl` API — e.g. `List.foldl_cons` —
would let one phrase `PCA.Coverage.Engine.run` as a `List.foldl`; the induction
below is the same one that `List.foldl` recursion performs, so no external

theorem run_eq_runRaw_of_all_recognized (M : Engine S E) (s : S) :
    ∀ (tr : List E), (∀ e ∈ tr, M.recognized e = true) → M.run s tr = M.runRaw s tr
  | [], _ => rfl
  | e :: tr, h => by
      have he : M.recognized e = true := h e (List.mem_cons_self ..)
      simp only [Engine.run_cons, M.handle_of_recognized s he]
      exact run_eq_runRaw_of_all_recognized M _ tr
        (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- If the engine's behaviour on a trace differs from the unguarded one, the
trace must contain an unrecognized event: the engine never bails spuriously. -/
