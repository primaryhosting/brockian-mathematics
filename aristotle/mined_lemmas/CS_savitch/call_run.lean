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

theorem call_run (M : NMachine) (x : Word) (stage : ℕ) (target : Word) (acc esc : Bool) :
    ∀ (k : ℕ) (a b : Word) (stack : List Frame),
      Runs M x ⟨stage, target, acc, esc, Inner.call k a b, stack, none⟩
        ⟨stage, target, acc, esc, Inner.ret (savR (edgeB M x) stage k a b), stack, none⟩ := by
  intro k
  induction k with
  | zero =>
      intro a b stack
      exact Runs.one (by rw [dstep_call_zero, savR_zero])
  | succ k ih =>
      have loop : ∀ (n : ℕ) (a b mid : Word) (stack : List Frame),
          rem stage mid = n → mid.length ≤ stage →
          Runs M x
              ⟨stage, target, acc, esc, Inner.call k a mid, ⟨k, a, b, mid, false⟩ :: stack, none⟩
              ⟨stage, target, acc, esc,
                Inner.ret (anyMid (fun m => savR (edgeB M x) stage k a m &&
                                            savR (edgeB M x) stage k m b) n mid),
                stack, none⟩ := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ihn =>
          intro a b mid stack hrem hmid
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
            have := rem_pos (s := stage) hmid
            exact ⟨n - 1, by omega⟩
          set E := edgeB M x with hE
          set P : Word → Bool := fun w => savR E stage k a w && savR E stage k w b with hP
          -- advancing to the next midpoint
          have adv : ∀ (sec : Bool), P mid = false →
              Runs M x
                ⟨stage, target, acc, esc, Inner.ret false, ⟨k, a, b, mid, sec⟩ :: stack, none⟩
                ⟨stage, target, acc, esc, Inner.ret (anyMid P (m + 1) mid), stack, none⟩ := by
            intro sec hPmid
            rw [anyMid_succ, hPmid, Bool.false_or]
            by_cases h2 : 2 ≤ rem stage mid
            · obtain ⟨hsome, hlen⟩ := univNext_eq_some hmid h2
              refine Runs.step (dstep_ret_false_some stack hsome) ?_
              exact ihn m (by omega) a b (wnext mid) stack (by rw [rem_wnext, hrem]; omega) hlen
            · have hnone : univNext stage mid = none := (univNext_eq_none hmid).2 (by omega)
              have hm : m = 0 := by omega
              subst hm
              refine Runs.one ?_
              rw [dstep_ret_false_none stack hnone]
              simp [anyMid]
          by_cases hv1 : savR E stage k a mid = true
          · refine (ih a mid (⟨k, a, b, mid, false⟩ :: stack)).trans ?_
            rw [hv1]
            refine Runs.step (dstep_ret_first_true stack) ?_
            refine (ih mid b (⟨k, a, b, mid, true⟩ :: stack)).trans ?_
            by_cases hv2 : savR E stage k mid b = true
            · rw [hv2]
              refine Runs.one ?_
              rw [dstep_ret_second_true stack]
              have hPmid : P mid = true := by simp [hP, hv1, hv2]
              rw [anyMid_succ, hPmid, Bool.true_or]
            · have hv2' : savR E stage k mid b = false := by simpa using hv2
              rw [hv2']
              exact adv true (by simp [hP, hv2'])
          · have hv1' : savR E stage k a mid = false := by simpa using hv1
            refine (ih a mid (⟨k, a, b, mid, false⟩ :: stack)).trans ?_
            rw [hv1']
            exact adv false (by simp [hP, hv1'])
      intro a b stack
      by_cases hab : a = b
      · refine Runs.one ?_
        rw [dstep_call_succ_eq stack hab]
        congr 1
        rw [savR_succ]
        simp [hab]
      · refine Runs.step (dstep_call_succ_ne stack hab) ?_
        have h2 := loop (rem stage ([] : Word)) a b [] stack rfl (by simp)
        refine h2.trans ?_
        have hrem : rem stage ([] : Word) = wordCount stage := by simp [rem]
        rw [hrem, savR_succ, show (a == b) = false from beq_eq_false_iff_ne.2 hab,
          Bool.false_or]
        exact Runs.refl M x _

/-! ## The scan over all candidate configurations -/

/-- Started at the target `c`, the simulator scans all remaining targets, and then either halts
or moves to the next stage, according to the two flags it has accumulated. -/
