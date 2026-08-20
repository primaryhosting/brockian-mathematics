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

theorem scan_run (M : NMachine) (x : Word) (stage : ℕ) :
    ∀ (n : ℕ) (c : Word) (acc esc : Bool), rem stage c = n → c.length ≤ stage →
      ∃ σ', Runs M x ⟨stage, c, acc, esc, Inner.call (stage + 1) [] c, [], none⟩ σ' ∧
        (if (acc || anyMid (accP M x stage) n c) = true then
            σ'.done = some true ∧ σ'.stage = stage
          else if (esc || anyMid (escP M x stage) n c) = true then
            σ' = ⟨stage + 1, [], false, false, Inner.call (stage + 2) [] [], [], none⟩
          else σ'.done = some false ∧ σ'.stage = stage) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro c acc esc hrem hc
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := rem_pos (s := stage) hc; omega⟩
    have hstart := call_run M x stage c acc esc (stage + 1) [] c []
    by_cases h2 : 2 ≤ rem stage c
    · obtain ⟨hsome, hlen⟩ := univNext_eq_some hc h2
      obtain ⟨σ', hrun, hprop⟩ := ihn m (by omega) (wnext c)
        (acc || accP M x stage c) (esc || escP M x stage c)
        (by rw [rem_wnext, hrem]; omega) hlen
      refine ⟨σ', hstart.trans ((Runs.one (dstep_scan_some hsome)).trans hrun), ?_⟩
      rw [anyMid_succ, anyMid_succ, ← Bool.or_assoc, ← Bool.or_assoc]
      exact hprop
    · have hnone : univNext stage c = none := (univNext_eq_none hc).2 (by omega)
      have hm : m = 0 := by omega
      subst hm
      have hA1 : anyMid (accP M x stage) 1 c = accP M x stage c := by simp [anyMid]
      have hX1 : anyMid (escP M x stage) 1 c = escP M x stage c := by simp [anyMid]
      rw [hA1, hX1]
      by_cases hA : (acc || accP M x stage c) = true
      · refine ⟨_, hstart.trans (Runs.one (dstep_scan_none_acc hnone hA)), ?_⟩
        rw [if_pos hA]
        exact ⟨rfl, rfl⟩
      · have hA' : (acc || accP M x stage c) = false := by simpa using hA
        by_cases hX : (esc || escP M x stage c) = true
        · refine ⟨_, hstart.trans (Runs.one (dstep_scan_none_esc hnone hA' hX)), ?_⟩
          rw [if_neg hA, if_pos hX]
        · have hX' : (esc || escP M x stage c) = false := by simpa using hX
          refine ⟨_, hstart.trans (Runs.one (dstep_scan_none_rej hnone hA' hX')), ?_⟩
          rw [if_neg hA, if_neg hX]
          exact ⟨rfl, rfl⟩

/-! ## The simulator halts with the right answer -/

