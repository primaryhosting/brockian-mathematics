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

theorem wrank_injective : Function.Injective wrank := by
  intro w
  induction w with
  | nil =>
      intro v hv
      cases v with
      | nil => rfl
      | cons b t => exact absurd hv.symm (Nat.ne_of_gt (wrank_pos_of_cons b t))
  | cons b t ih =>
      intro v hv
      cases v with
      | nil => exact absurd hv (Nat.ne_of_gt (wrank_pos_of_cons b t))
      | cons b' t' =>
          have h : b.toNat + 2 * wrank t + 1 = b'.toNat + 2 * wrank t' + 1 := hv
          have hbb : b = b' := by
            cases b <;> cases b' <;>
              simp only [Bool.toNat_true, Bool.toNat_false] at h <;>
              first | rfl | (exfalso; omega)
          subst hbb
          have ht : wrank t = wrank t' := by
            cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] at h <;> omega
          rw [ih ht]

/-- Upper bound for the rank of a word of length `n`: `wrank w < 2 ^ (n + 1) - 1`. -/
