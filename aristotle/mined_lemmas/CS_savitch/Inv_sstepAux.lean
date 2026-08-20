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

theorem Inv_sstepAux (M : NMachine) (bit : Option Bool) (σ : SState) (h : Inv σ) :
    Inv (sstepAux M bit σ) := by
  rcases σ with ⟨stage, target, acc, esc, inner, stack, done⟩
  obtain ⟨htg, hin⟩ := h
  simp only at htg hin
  cases inner with
  | call k a b =>
      obtain ⟨ha, hb, hst⟩ := hin
      cases k with
      | zero => exact ⟨htg, hst.top⟩
      | succ k =>
          simp only [sstepAux]
          by_cases hab : a = b
          · rw [if_pos hab]
            exact ⟨htg, hst.top⟩
          · rw [if_neg hab]
            exact ⟨htg, ha, by simp, rfl, ha, hb, by simp, hst⟩
  | ret v =>
      cases stack with
      | nil =>
          simp only [sstepAux]
          rcases hu : univNext stage target with _ | t'
          · split_ifs
            · exact ⟨htg, trivial⟩
            · exact ⟨by simp, by simp, by simp, by simp [StackOK]⟩
            · exact ⟨htg, trivial⟩
          · exact ⟨univNext_length hu, by simp, univNext_length hu, by simp [StackOK]⟩
      | cons fr rest =>
          obtain ⟨hk, hfa, hfb, hfm, hrest⟩ := hin
          simp only [sstepAux]
          by_cases h2 : fr.second = true
          · rw [if_pos h2]
            by_cases hv : v = true
            · rw [if_pos hv]
              exact ⟨htg, hrest.top⟩
            · rw [if_neg hv]
              exact Inv_advanceMid htg hfa hfb hrest
          · rw [if_neg h2]
            by_cases hv : v = true
            · rw [if_pos hv]
              exact ⟨htg, hfm, hfb, rfl, hfa, hfb, hfm, hrest⟩
            · rw [if_neg hv]
              exact Inv_advanceMid htg hfa hfb hrest

