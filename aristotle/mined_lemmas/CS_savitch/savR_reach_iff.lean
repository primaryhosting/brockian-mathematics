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

theorem savR_reach_iff (E : Word → Word → Bool) (s : ℕ) {a b : Word}
    (ha : a.length ≤ s) (hb : b.length ≤ s) :
    savR E s (s + 1) a b = true ↔ ∃ n, PathN E s n a b := by
  constructor
  · intro h
    obtain ⟨n, -, hp⟩ := (savR_iff E s (s + 1) ha hb).1 h
    exact ⟨n, hp⟩
  · rintro ⟨n, hp⟩
    obtain ⟨n', hn', hp'⟩ := hp.shorten hb
    refine (savR_iff E s (s + 1) ha hb).2 ⟨n', ?_, hp'⟩
    have hw : wordCount s ≤ 2 ^ (s + 1) := by
      simp only [wordCount]
      exact Nat.sub_le _ _
    exact le_of_lt (lt_of_lt_of_le hn' hw)

end Savitch
end CS

/-
# Correctness of the simulator

The simulator implements the Savitch recursion `savR` with an explicit stack, and scans all
words of length at most the current stage, looking for a reachable accepting configuration and
for a reachable configuration that leaves the current stage.
-/
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Encode

namespace CS
namespace Savitch

variable {M : NMachine} {x : Word} {stage : ℕ} {target : Word} {acc esc : Bool}

/-- `Runs M x σ σ'` : the simulator started in state `σ` reaches state `σ'`. -/
