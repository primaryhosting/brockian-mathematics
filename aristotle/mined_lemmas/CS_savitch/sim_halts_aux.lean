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

theorem sim_halts_aux (M : NMachine) (x : Word) (S : ℕ)
    (hS : ∀ c, M.Reach x c → c.length ≤ S) :
    ∀ (d stage : ℕ), S - stage = d → stage ≤ S →
      ∃ σ', Runs M x ⟨stage, [], false, false, Inner.call (stage + 1) [] [], [], none⟩ σ' ∧
        σ'.stage ≤ S ∧ σ'.done ≠ none ∧ (σ'.done = some true ↔ x ∈ M.lang) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro stage hd hstage
    obtain ⟨σ', hrun, hprop⟩ :=
      scan_run M x stage (rem stage ([] : Word)) [] false false rfl (by simp)
    have hrem : rem stage ([] : Word) = wordCount stage := by simp [rem]
    rw [hrem] at hprop
    by_cases hA : (false || anyMid (accP M x stage) (wordCount stage) []) = true
    · rw [if_pos hA] at hprop
      obtain ⟨hdone, hst⟩ := hprop
      have hlang : x ∈ M.lang := by
        rw [Bool.false_or, anyMid_all] at hA
        obtain ⟨u, hu, hacc⟩ := hA
        exact accP_sound hu hacc
      exact ⟨σ', hrun, by omega, by rw [hdone]; simp, by rw [hdone]; simp [hlang]⟩
    · rw [if_neg hA] at hprop
      have hA' : ∀ u : Word, u.length ≤ stage → accP M x stage u = false := by
        intro u hu
        by_contra hcon
        exact hA (by rw [Bool.false_or, anyMid_all]; exact ⟨u, hu, by simpa using hcon⟩)
      by_cases hX : (false || anyMid (escP M x stage) (wordCount stage) []) = true
      · rw [if_pos hX] at hprop
        -- the stage must be increased; this cannot happen at stage `S`
        have hlt : stage < S := by
          rcases Nat.lt_or_ge stage S with h | h
          · exact h
          · exfalso
            have hstageS : stage = S := by omega
            subst hstageS
            rw [Bool.false_or, anyMid_all] at hX
            obtain ⟨u, hu, hesc⟩ := hX
            rw [escP_eq_false_of_bound hS u hu] at hesc
            exact Bool.false_ne_true hesc
        obtain ⟨σ'', hrun'', hrest⟩ := ihd (S - (stage + 1)) (by omega) (stage + 1) rfl (by omega)
        exact ⟨σ'', hrun.trans (hprop ▸ hrun''), hrest⟩
      · rw [if_neg hX] at hprop
        obtain ⟨hdone, hst⟩ := hprop
        have hX' : ∀ u : Word, u.length ≤ stage → escP M x stage u = false := by
          intro u hu
          by_contra hcon
          exact hX (by rw [Bool.false_or, anyMid_all]; exact ⟨u, hu, by simpa using hcon⟩)
        have hnot : x ∉ M.lang := by
          rintro ⟨c, hreach, hver⟩
          obtain ⟨hlen, hsav⟩ := savR_complete_of_no_escape hX' c hreach
          have : accP M x stage c = true := by simp [accP, hsav, hver]
          rw [hA' c hlen] at this
          exact Bool.false_ne_true this
        refine ⟨σ', hrun, by omega, by rw [hdone]; simp, ?_⟩
        rw [hdone]
        simp [hnot]

