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

theorem enc_length_le {σ : SState} (h : Inv σ) :
    (enc σ).length ≤ 25 * (σ.stage + 1) ^ 2 := by
  have h1 : (codeW σ.target).length ≤ 2 * σ.stage + 1 := by
    rw [codeW_length]
    have := h.1
    omega
  have h2 : (codeDone σ.done).length ≤ 2 := by
    cases σ.done <;> simp [codeDone]
  have h3 := h.inner_length
  have h4 : (codeStack σ.stack).length ≤ 1 + (σ.stage + 1) * (7 * σ.stage + 8) := by
    have hb := codeStack_length_le σ.stage σ.stack h.frame_bounds
    have hl : σ.stack.length ≤ σ.stage + 1 := h.stack_length
    have : σ.stack.length * (7 * σ.stage + 8) ≤ (σ.stage + 1) * (7 * σ.stage + 8) :=
      Nat.mul_le_mul_right _ hl
    omega
  have hexp : (σ.stage + 1) * (7 * σ.stage + 8) = 7 * (σ.stage * σ.stage) + 15 * σ.stage + 8 := by
    ring
  have hsq : 25 * (σ.stage + 1) ^ 2 = 25 * (σ.stage * σ.stage) + 50 * σ.stage + 25 := by
    ring
  simp only [enc, List.length_append, codeN_length, List.length_cons, List.length_nil]
  rw [hexp] at h4
  rw [hsq]
  generalize σ.stage * σ.stage = Q at h4 ⊢
  omega

/-! ## Preservation of the invariant -/

