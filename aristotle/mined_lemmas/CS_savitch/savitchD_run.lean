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

theorem savitchD_run (M : NMachine) (x : Word) :
    ∀ t, (savitchD M).run x t = if t = 0 then [] else enc (dstepIter M x t initState) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev : dec ((savitchD M).run x t) = dstepIter M x t initState := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · simpa using dec_nil
        · rw [ih, if_neg (by omega), dec_enc]
      have hverd : (savitchD M).verdict ((savitchD M).run x t)
          = (dstepIter M x t initState).done := by
        show (dec ((savitchD M).run x t)).done = _
        rw [hprev]
      rw [if_neg (Nat.succ_ne_zero t), run_succ]
      by_cases hd : (dstepIter M x t initState).done = none
      · rw [if_pos (by rw [hverd]; exact hd)]
        show enc (sstep M x[M.ask (askWord (dec ((savitchD M).run x t)))]?
          (dec ((savitchD M).run x t))) = _
        rw [hprev, dstepIter_succ']
        rfl
      · rw [if_neg (by rw [hverd]; exact hd)]
        rw [dstepIter_succ', dstep_done hd]
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exact absurd (by simp [initState] : (dstepIter M x 0 initState).done = none) hd
        · rw [ih, if_neg (by omega)]

