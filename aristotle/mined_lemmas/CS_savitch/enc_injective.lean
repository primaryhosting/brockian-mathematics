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

theorem enc_injective : Function.Injective enc := by
  intro σ τ h
  rcases σ with ⟨st, tg, ac, es, inn, stk, dn⟩
  rcases τ with ⟨st', tg', ac', es', inn', stk', dn'⟩
  simp only [enc, List.append_assoc] at h
  obtain ⟨h1, h⟩ := codeN_app_inj _ _ _ _ h
  obtain ⟨h2, h⟩ := codeW_app_inj _ _ _ _ h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨h3, h4, h⟩ := h
  obtain ⟨h5, h⟩ := codeDone_app_inj _ _ _ _ h
  obtain ⟨h6, h⟩ := codeInner_app_inj _ _ _ _ h
  have h7 : stk = stk' := (codeStack_app_inj stk stk' [] [] (by simpa using h)).1
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  rfl

