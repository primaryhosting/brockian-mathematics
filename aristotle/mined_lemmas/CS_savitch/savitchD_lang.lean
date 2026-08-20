/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module documentation, so the header above is
-- written as a plain comment; it is repeated as the module docstring below.)
import RequestProject.Savitch.Final

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The machine model is the standard off-line random-access model of space bounded computation
(see `RequestProject/Savitch/Model.lean`): the memory of a machine is a bit string, one step
rewrites the memory using the memory content and a single input bit, read at a position which
is determined by the memory, and the space used on an input is the maximal length of a memory
string occurring in the computation.

`NSPACE f` and `DSPACE g` are the classes of languages accepted by nondeterministic,
respectively deterministic, machines running in space `O (f n)`, respectively `O (g n)`.

The proof is Savitch's: for a nondeterministic machine `M` running in space `S` on the input
`x`, deciding whether `M` accepts amounts to deciding reachability in the configuration graph
of `M` on `x`, whose vertices are the words of length at most `S`.  Reachability by a path of
length at most `2 ^ k` is decided by the midpoint recursion `savR`, whose recursion depth is
`k`; taking `k = S + 1` suffices because there are only `2 ^ (S + 1) - 1` configurations.  The
simulator runs this recursion with an explicit stack of at most `S + 2` frames, each holding
three words of length at most `S`, so it uses `O (S ^ 2)` bits.  Since the simulator does not
know `S`, it runs the whole procedure for stages `s = 0, 1, 2, …`, and at each stage also
checks whether some reachable configuration has a successor of length more than `s`; the first
stage at which this check fails gives the correct answer, and this happens at the latest at
stage `S`.
-/

namespace CS

namespace Savitch

/-- A deterministic machine viewed as a nondeterministic machine. -/

theorem savitchD_lang (M : NMachine) (x : Word) (S : ℕ)
    (hS : ∀ c, M.Reach x c → c.length ≤ S) :
    (x ∈ (savitchD M).lang ↔ x ∈ M.lang) := by
  obtain ⟨σ', ⟨T, hT⟩, hstage, hdone, hiff⟩ := sim_halts M x S hS
  constructor
  · rintro ⟨t, ht⟩
    rw [savitchD_verdict_run] at ht
    have hne : (dstepIter M x t initState).done ≠ none := by rw [ht]; simp
    have hdone' : (dstepIter M x T initState).done ≠ none := by rw [hT]; exact hdone
    have hTdone : (dstepIter M x T initState).done = some true := by
      rcases le_total t T with hle | hle
      · rw [frozen hle hne, ht]
      · rw [← frozen hle hdone']
        exact ht
    rw [hT] at hTdone
    exact hiff.1 hTdone
  · intro hx
    refine ⟨T, ?_⟩
    rw [savitchD_verdict_run, hT]
    exact hiff.2 hx

