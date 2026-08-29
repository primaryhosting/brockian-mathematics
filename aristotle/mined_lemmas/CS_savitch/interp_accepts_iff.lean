/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Interp

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
`NSPACE f ⊆ DSPACE (16 * (f + 1)^2)`, i.e. Savitch's theorem, and the corollary
`PSPACE = NPSPACE`.

The model of computation is set up in `RequestProject.Savitch.Model`: a device is
a configuration graph with read-only access to the input tape, and the space it
uses is the number of bits needed to encode a configuration.

The proof follows the classical argument.  Given a nondeterministic device `M`
using `s` bits of space, its configuration graph (extended by a single absorbing
accepting vertex) has at most `2 ^ (s+1)` vertices, so acceptance amounts to
reachability in a graph of that size.  Reachability is computed deterministically
by the midpoint recursion `reach` of `RequestProject.Savitch.Reach`, of depth
`K = s + 1`, and this recursion is executed by the explicit stack machine of
`RequestProject.Savitch.Interp`, whose states consist of at most `K` frames, each
holding three vertices and a bit.  That machine therefore has at most
`2 ^ (16 * K ^ 2)` configurations, i.e. it runs in space `O(s²)`.
-/

namespace CS

/-! ### Counting the states of the evaluator -/

section Card

variable {C : Type} [Fintype C] (K : ℕ)

/-- Encoding of a state of the evaluator by its mode and the (padded) list of its
frames. -/

theorem interp_accepts_iff (h : IsInterp K R dstep) (a b : C) :
    Reaches dstep (Mode.ask a b, ([] : List (Frame C))) (Mode.ret true, []) ↔
      reach R K a b = true := by
  have hrun : Reaches dstep (Mode.ask a b, ([] : List (Frame C)))
      (Mode.ret (reach R K a b), []) := askEval h K [] (by simp) a b
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := hrun
    exact (halted_unique h ht ht').symm
  · intro hb
    rw [hb] at hrun
    exact hrun

end Interp

end CS

/-
Space-bounded computation: the model.

A *device* is a configuration graph with read-only access to the input word.
Concretely, a device has

* a type `Conf` of configurations,
* a function `head : Conf → ℕ` giving the position of the input head in each
  configuration,
* a transition relation (resp. function) which, given the current configuration
  and the symbol currently scanned on the input tape, describes the possible
  (resp. the unique) successor configuration,
* an initial configuration and a set of accepting configurations.

The *space* used by such a device is the number of bits needed to write down a
configuration, i.e. `s` such that `Conf` embeds into `Fin s → Bool`.  This is the
standard abstract way of measuring space: a Turing machine with a read-only
input tape and a work tape of `s` cells over a fixed finite work alphabet has
`2^{O(s)}` configurations (plus the input head position, recorded here by
`head`), and conversely.

`NSPACE f` (resp. `DSPACE f`) is the class of languages decided by a family of
nondeterministic (resp. deterministic) devices, one for each input length, whose
configuration space uses at most `f n` bits.

Two remarks on the formalisation.

* A member of a space class is a *family* of devices indexed by the input length,
  with no uniformity condition relating the different lengths; this is the
  non-uniform reading of a space class.  Savitch's construction below is
  nevertheless uniform in the device: the deterministic device is obtained from
  the nondeterministic one by one explicit transformation, applied length by
  length.
* Space is counted in bits, so `f n = 0` allows a single configuration only.
  Accordingly the deterministic bound obtained below is `16 * (f n + 1) ^ 2`,
  which is `O(f²)` and also meaningful when `f n = 0`.
-/
import Mathlib

namespace CS

/-- A language over the alphabet `Γ`. -/
abbrev Language (Γ : Type) := List Γ → Prop

/-- A nondeterministic space-bounded device (a configuration graph together with
read-only access to the input). -/
structure NDevice (Γ : Type) where
  /-- The type of configurations. -/
  Conf : Type
  /-- Position of the input head in a configuration. -/
  head : Conf → ℕ
  /-- `step c σ c'` holds if `c'` is a possible successor of `c` when the symbol
  scanned on the input tape is `σ` (`none` meaning "past the end of the input"). -/
  step : Conf → Option Γ → Conf → Prop
  /-- The initial configuration. -/
  init : Conf
  /-- The accepting configurations. -/
  acc : Conf → Prop

/-- A deterministic space-bounded device. -/
structure DDevice (Γ : Type) where
  /-- The type of configurations. -/
  Conf : Type
  /-- Position of the input head in a configuration. -/
  head : Conf → ℕ
  /-- The successor of a configuration, given the scanned input symbol. -/
  step : Conf → Option Γ → Conf
  /-- The initial configuration. -/
  init : Conf
  /-- The accepting configurations. -/
  acc : Conf → Prop

namespace NDevice

variable {Γ : Type}

/-- A device runs in space `s` if its configurations can be encoded by `s` bits. -/
