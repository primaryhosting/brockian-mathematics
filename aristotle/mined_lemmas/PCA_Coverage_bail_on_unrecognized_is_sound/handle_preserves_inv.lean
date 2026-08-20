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

theorem handle_preserves_inv (M : Engine S E) (Inv : S → Prop)
    (hstep : ∀ s e, Inv s → M.recognized e = true → Inv (M.step s e))
    (hbail : ∀ s, Inv s → Inv (M.bail s))
    (s : S) (e : E) (hs : Inv s) : Inv (M.handle s e) := by
  unfold Engine.handle
  cases he : M.recognized e with
  | false => simpa using hbail s hs
  | true => simpa using hstep s e hs he

/-- **Bailing on unrecognized input is sound.**

If a safety invariant `Inv` is preserved by the engine's handler on every
*recognized* event, and is preserved by the bail action, then `Inv` holds after
running the engine on an **arbitrary** trace — including traces containing
events the engine was never verified against.

Thus verification effort may be confined to the recognized coverage fragment:
everything outside it is discharged once and for all by the bail action. -/
