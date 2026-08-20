# The Attestation Gap
### On the separation of mathematical truth from its machine certificate

*A metamathematical exposition, occasioned by ten theorems that were true, sound, and
machine-checkable, yet simultaneously reported "failed."*

---

## 0. A disclaimer worthy of the subject

This is not a claim to new mathematics, and the reader should distrust any exposition of a
software incident that reaches for the Fields Medal. The medal is for theorems. What
follows is metamathematics: an analysis of the *act of certification* in mechanized proof,
occasioned by a concrete event in a live verification pipeline. Its ambition is
foundational clarity, not priority. That the analysis is honest about what it is is not
incidental to its argument — it is the argument.

## 1. The event

A corpus of 854 Lean 4 modules, each carrying an independent AXLE attestation of the form
"module verified; declarations depend only on the trusted kernel axioms
{`propext`, `Classical.choice`, `Quot.sound`}," was migrated from the Lean toolchain
`4.32.0` to `4.32.2`. Eight hundred forty-four re-verified without incident. Ten did not:
they reported `failed`, with the verifier emitting `error: unknown constant`.

The natural inference — that a compiler upgrade had broken ten proofs — is false. Every
one of the ten module bodies compiled cleanly under `4.32.2`. Every theorem remained a
theorem. What had changed was not the provability of the statements but the ability of the
certifying apparatus to *name* the objects it was certifying: the attestation appends
`#print axioms N` for each theorem `N`, and under the newer toolchain the names it
constructed no longer resolved. The proofs were sound; the certificate could not be
issued. The failure lived entirely in the space *between* the proof and its attestation.

I will argue that this space — call it the **attestation gap** — is a permanent structural
feature of mechanized mathematics, not an artifact of one bug; that it has a precise
description; and that taking it seriously changes what a "verified" flag is allowed to
mean.

## 2. Two properties of a machine proof

Fix a formal system with a small trusted kernel (Lean's, say), and a proof term `p` whose
type is a proposition `φ`. I distinguish two properties.

**Soundness.** `p : φ` type-checks in the kernel, and the axioms on which `p` depends lie
in an approved set `A`. This is a property of the mathematics. It is invariant under any
change to the surrounding toolchain that preserves the kernel's logic: it does not depend
on tactic implementations, on elaboration heuristics, on the pretty-printer, on module
names, or on the version string. If `φ` is sound today it is sound in every world whose
kernel agrees.

**Attestability.** A *particular verification apparatus* `V`, at a *particular
configuration* `c` (toolchain version, environment, module layout, the exact commands the
apparatus issues), can be driven to emit a trusted certificate that `p` is sound. This is
a property of the *pipeline*, not of the mathematics. It depends on everything soundness
does not: on how `V` addresses declarations, on what the reflection command `#print axioms`
accepts as a name, on whether the module's namespace matches the string `V` guessed for it.

The first is a fact about `φ`. The second is a fact about `V`, `c`, and their interaction
with `p`. **They are not the same property, and the second does not entail the first in
either direction.** A proof can be sound yet unattestable (the event above). A pipeline can
issue a certificate that is not backed by soundness (any verifier with a false-accept bug).
The literature has a name for guarding the second direction — the *de Bruijn criterion*,
that trust reduce to a small independently-checkable kernel — but the first direction, the
sound-yet-unattestable proof, is less discussed and is what the event exhibits.

## 3. Why the gap is structural, not incidental

One might hope attestability is merely soundness plus good engineering — that a
sufficiently careful pipeline closes the gap. It cannot, for a reason that is itself
mathematical.

A certificate is a finite artifact produced by a program `V` that must *refer* to the
proof's constituents: to issue "`N` depends only on `A`," `V` must name `N`. Naming is not
part of the proof term; it is a presentation layer, and presentation is not invariant. The
same declaration is `Brockian.WeylOperator.foo` to one addressing scheme, `foo` under an
opened namespace, `Brockian.Weyl.Operator.IsSymmetric.foo` fully qualified — three names
for one immutable object. Soundness quantifies over the object; attestation must commit to
a name. Whenever the naming discipline of `V` and the naming reality of `p` diverge — and a
toolchain is free to tighten name resolution between versions, as `4.32.0 → 4.32.2` did —
the certificate fails though the mathematics is untouched.

This is an instance of a general pattern: **a proof is invariant, but every finite
certificate about it is a choice of presentation, and presentations are governed by the
mutable machine, not the immutable logic.** The gap is the shadow cast by the fact that we
verify *representations* of proofs with *programs*, and neither representations nor programs
are canonical. It is the mechanized analogue of a phenomenon Thurston described for human
proof — that the socially transmitted object and the underlying truth are distinct, and the
transmission channel has its own failure modes — sharpened to the point where the "channel"
is a versioned compiler and the "social" step is a string match.

## 4. The event, precisely

The ten failures had two compounding causes, and both are pure attestation-gap phenomena.

1. **Under-qualified reference.** The apparatus addressed declarations by
   `open M in #print axioms n`, where `M` was a *guessed* module string (derived from the
   file name) and `n` a bare identifier. For a declaration `M'.C.n` living in a nested
   namespace `C` — and with `M' ≠ M`, the file name not matching the true namespace —
   neither `open M` nor the bare `n` reaches it. Under `4.32.0` the resolver's search was
   lax enough to find it anyway; `4.32.2` was stricter, and `n` became `unknown constant`.
   The repair is to address by the *fully qualified* name, recovered by tracking the
   namespace stack — a canonical presentation, chosen precisely because it is the one the
   machine's resolver treats as invariant.

2. **Category error in reference.** The apparatus applied `#print axioms` — a query
   meaningful only for proof terms — to objects it had *misclassified* as theorems. A
   definition written `def Namespace.foo` was read as a theorem because the classifier
   matched only unqualified names after the keyword. Asking for the axiom footprint of a
   definition is not false; it is *ill-typed as a question*, and one ill-typed question
   aborts the whole certificate.

Both are failures to *refer correctly*, and neither touches provability. The correlation
that made the ten look like a coherent mathematical cluster — nine of them the `Weyl`
spectral-theory modules — was a **naming-idiom correlation**: those modules share the
design habit `namespace Brockian.Weyl.X` with nested `IsSymmetric`/`Adjoint`, and it was
exactly nesting that the guessed-`open` scheme could not address. The apparent
mathematical structure was an artifact of a shared *notational* convention. This is worth
dwelling on: **a bug in the certifier can manufacture the appearance of mathematical
correlation** where there is only correlation of presentation. An investigator who trusted
the "failed" verdicts would have gone looking for a shared broken lemma in spectral theory
and found none, because none exists.

## 5. The design consequence: never let the gap masquerade

If attestability and soundness are distinct, a verification system must be built so that a
failure of the former can *never be reported as* a failure of the latter. Concretely, three
disciplines follow, and the pipeline in question observes all three:

- **Non-downgrade.** When re-attestation of a previously-sound module fails, the system
  does not overwrite its standing certificate. It preserves the last valid attestation and
  *flags the event for adjudication*. In the migration this rule quarantined exactly the
  ten, refusing to record ten false failures — and so preserved the corpus's integrity
  against its own tooling. A system that trusts its latest run over its accumulated
  evidence would have silently deleted ten sound theorems.

- **Separation of the certificate from the claim.** The certificate records the environment
  it was issued under. A module attested at `4.32.0` and not yet re-attested at `4.32.2` is
  not thereby *false*; it is *honestly labeled* as certified under a named, possibly-stale
  configuration. The registry never conflates "we could not currently re-issue the
  certificate" with "the theorem is not proved."

- **Canonical reference as the invariant.** The repair is not a patch to a symptom but a
  move to the one addressing scheme the machine treats as version-stable — full
  qualification — thereby shrinking the gap wherever it can be shrunk. The gap cannot be
  closed (any future toolchain may move the resolver again), but the apparatus can be made
  to sit on the most invariant presentation available.

## 6. What the gap says about "verified"

The reflexive reading of a green "PROVED" is *this statement is true*. The attestation gap
forces a more exact reading: **a certificate is a claim about a pipeline's behavior at a
configuration, which — if and only if the pipeline's kernel and axiom discipline are
themselves sound — is *evidence about* the mathematics.** The mathematics is what makes the
evidence worth having; but the flag is not the mathematics, and the two can come apart
without the mathematics moving an inch. Ten theorems in this corpus were, for a span of one
toolchain upgrade, *true, sound, kernel-checkable, and marked failed simultaneously* — a
combination that is incoherent only if one has conflated the theorem with its certificate.

The honest verification program takes this as a first principle rather than an
embarrassment. It refuses to let the certificate speak louder than it can justify; it
records what was checked, under what, and by what; it treats a flipped flag as a question
about the apparatus before it is ever a question about the truth. That posture is not
weakness about rigor. It is the only posture under which a machine's "PROVED" means, in the
end, exactly what it should — no more, and precisely no less.

## 7. Coda

The event resolved without a single change to a single proof. Ten modules went from
`failed` to `verified` because the certifier learned to name what was always there. If
there is a moral fit for the seriousness the occasion was asked to bear, it is this: in
mechanized mathematics the hardest thing to keep honest is not the proof but the *account
we give of it* — and a system earns the right to say "proved" precisely to the degree that
it knows the difference.
