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

theorem stage_mono {M : NMachine} {x : Word} {σ : SState} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (dstepIter M x t₁ σ).stage ≤ (dstepIter M x t₂ σ).stage := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [dstepIter_add]
  exact stage_dstepIter_ge _ _ _ _

end Savitch
end CS

/-
# A machine model for space-bounded computation

We use the standard *off-line random-access* model of a space bounded machine:

* the input `x : List Bool` is read-only and is accessed one bit at a time, at a position
  which is determined by the current memory content (`ask`);
* the machine's whole workspace is a bit string `m : List Bool` (its *memory*); one step
  rewrites the memory using the current memory and the single input bit that was read;
* the *space* used on an input is the maximal length of a memory string occurring in a
  computation.

Nondeterministic machines have a list of possible successor memories, deterministic machines
exactly one.  A machine halts as soon as `verdict` of the current memory is `some b`.

Note that no computability assumption is placed on the three components `ask`, `next`,
`verdict` of a machine; they are arbitrary (possibly non-computable) functions of the memory.
This is the usual abstraction of "an arbitrary finite control", and it is what makes the
*space* bound the only resource restriction.  It is a genuine restriction: a machine whose
memory is bounded by `g (|x|)` bits can only ever be in one of `2 ^ (g |x| + 1) - 1` memory
states, and it can only see the input through the single bit it reads at each step.
-/
import Mathlib

namespace CS

/-- Words (bit strings): inputs, and memory contents, are words. -/
abbrev Word := List Bool

/-- A language is a set of words. -/
abbrev Language := Set Word

/-- A nondeterministic space-bounded machine. -/
structure NMachine where
  /-- Position of the input bit that is read, as a function of the current memory. -/
  ask : Word → ℕ
  /-- Possible successor memories, given the current memory and the input bit that was read
  (`none` if the position is beyond the end of the input). -/
  next : Word → Option Bool → List Word
  /-- `none` means "keep computing", `some b` means "halt and output `b`". -/
  verdict : Word → Option Bool

/-- A deterministic space-bounded machine. -/
structure DMachine where
  /-- Position of the input bit that is read, as a function of the current memory. -/
  ask : Word → ℕ
  /-- The successor memory, given the current memory and the input bit that was read. -/
  next : Word → Option Bool → Word
  /-- `none` means "keep computing", `some b` means "halt and output `b`". -/
  verdict : Word → Option Bool

namespace NMachine

variable (M : NMachine)

/-- One computation step of `M` on input `x`. -/
