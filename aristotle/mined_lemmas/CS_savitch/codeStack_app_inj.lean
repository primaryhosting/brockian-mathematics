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

theorem codeStack_app_inj : ∀ (l₁ l₂ : List Frame) (r₁ r₂ : Word),
    codeStack l₁ ++ r₁ = codeStack l₂ ++ r₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ r₁ r₂ h
      cases l₂ with
      | nil => exact ⟨rfl, by simpa [codeStack] using h⟩
      | cons f t => simp [codeStack] at h
  | cons f t ih =>
      intro l₂ r₁ r₂ h
      cases l₂ with
      | nil => simp [codeStack] at h
      | cons g t' =>
          simp only [codeStack, List.cons_append, List.cons.injEq, true_and,
            List.append_assoc] at h
          obtain ⟨hf, h⟩ := codeFrame_app_inj _ _ _ _ h
          obtain ⟨ht, hr⟩ := ih t' r₁ r₂ h
          exact ⟨by rw [hf, ht], hr⟩

