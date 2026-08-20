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

theorem savR_complete_of_no_escape {M : NMachine} {x : Word} {stage : ℕ}
    (hX : ∀ u : Word, u.length ≤ stage → escP M x stage u = false) :
    ∀ c, M.Reach x c → c.length ≤ stage ∧ savR (edgeB M x) stage (stage + 1) [] c = true := by
  intro c hc
  induction hc with
  | refl => exact ⟨by simp, by simp [savR_succ]⟩
  | @tail c₁ c₂ hab hstep ih =>
      obtain ⟨hlen, hsav⟩ := ih
      have hesc : escapes M x[M.ask c₁]? stage c₁ = false := by
        have h0 := hX c₁ hlen
        simpa [escP, hsav] using h0
      have hlen2 : c₂.length ≤ stage := by
        by_contra hcon
        rw [escapes, Bool.and_eq_false_iff] at hesc
        rcases hesc with h | h
        · rw [beq_eq_false_iff_ne] at h
          exact h hstep.1
        · rw [List.any_eq_false] at h
          have := h c₂ hstep.2
          simp only [decide_eq_true_eq] at this
          omega
      refine ⟨hlen2, ?_⟩
      obtain ⟨n, hp⟩ := (savR_reach_iff (edgeB M x) stage (by simp) hlen).1 hsav
      have hp2 : PathN (edgeB M x) stage (n + 1) [] c₂ :=
        hp.comp (PathN.single hlen (edgeB_of_stepRel hstep)) hlen
      exact (savR_reach_iff (edgeB M x) stage (by simp) hlen2).2 ⟨n + 1, hp2⟩

end Savitch
end CS

