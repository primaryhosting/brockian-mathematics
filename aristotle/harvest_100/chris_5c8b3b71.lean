/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace PCA

/-- An *artifact* handed to the isolation engine: a piece of code (a list of opcodes,
encoded as natural numbers) together with the policy (the list of opcodes the code is
permitted to use). -/
structure Artifact where
  /-- The opcodes making up the application code. -/
  code : List Nat
  /-- The whitelist of opcodes permitted by the isolation policy. -/
  policy : List Nat
  deriving DecidableEq

namespace Artifact

/-- A prefix-free serialisation of an artifact: the length of the code section, followed
by the code section, followed by the policy section.  Recording the length of the first
section makes the concatenation unambiguous, hence the encoding injective. -/
def encode (a : Artifact) : List Nat :=
  a.code.length :: (a.code ++ a.policy)

/-- The serialisation is injective: distinct artifacts have distinct encodings.
The key library lemma is `List.append_inj`, which cancels an append once the two left
factors are known to have equal length. -/
theorem encode_injective : Function.Injective encode := by
  rintro ⟨c₁, p₁⟩ ⟨c₂, p₂⟩ h
  simp only [encode, List.cons.injEq] at h
  obtain ⟨hlen, hcat⟩ := h
  obtain ⟨hc, hp⟩ := List.append_inj hcat hlen
  simp [hc, hp]

@[simp] theorem encode_inj {a b : Artifact} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff

/-- The isolation check performed by the engine: every opcode used by the code is
permitted by the policy. -/
def Isolated (a : Artifact) : Prop := ∀ x ∈ a.code, x ∈ a.policy

instance (a : Artifact) : Decidable (Isolated a) := by
  unfold Isolated; infer_instance

/-- The decision procedure run by the engine. -/
def check (a : Artifact) : Bool := decide (Isolated a)

@[simp] theorem check_eq_true_iff {a : Artifact} : check a = true ↔ Isolated a := by
  simp [check]

end Artifact

/-- A certificate emitted by the isolation engine: the digest of the artifact it was
issued for, together with the verdict of the isolation check. -/
structure Cert where
  /-- The digest (serialisation) of the artifact the certificate was issued for. -/
  digest : List Nat
  /-- The verdict of the isolation check on that artifact. -/
  verdict : Bool
  deriving DecidableEq

namespace Cert

/-- Running the engine on an artifact: compute its digest and its isolation verdict. -/
def reprove (a : Artifact) : Cert := ⟨Artifact.encode a, Artifact.check a⟩

/-- `c` is the certificate that the engine issued for the original artifact `a₀`. -/
def IssuedFor (c : Cert) (a₀ : Artifact) : Prop := c = reprove a₀

/-- The artifact `a` that we received is *untampered* with respect to the original
artifact `a₀` if it is bit-for-bit the same artifact. -/
def Untampered (a₀ a : Artifact) : Prop := a = a₀

/-- **Main theorem.**  Given a certificate `c` issued by the isolation engine for an
original artifact `a₀`, re-running the engine on a received artifact `a` reproduces `c`
exactly if and only if `a` is untampered.

*Soundness*: a matching re-proof rules out any tampering.
*Completeness*: an untampered artifact always re-proves to the stored certificate. -/
theorem reprove_matches_iff_untampered
    {c : Cert} {a₀ a : Artifact} (hc : IssuedFor c a₀) :
    reprove a = c ↔ Untampered a₀ a := by
  subst hc
  constructor
  · intro h
    have : Artifact.encode a = Artifact.encode a₀ := congrArg Cert.digest h
    exact Artifact.encode_injective this
  · rintro rfl
    rfl

/-- Corollary (soundness of the transported verdict): if the re-proof matches the
certificate, then the certificate's verdict really is the verdict of the isolation check
on the artifact in hand. -/
theorem isolated_of_reprove_matches
    {c : Cert} {a : Artifact} (h : reprove a = c)
    (hv : c.verdict = true) : Artifact.Isolated a := by
  have : Artifact.check a = true := by
    rw [show Artifact.check a = (reprove a).verdict from rfl, h]; exact hv
  simpa using this

/-- Corollary (tamper detection): if the artifact was modified, the re-proof cannot
match the stored certificate. -/
theorem reprove_ne_of_tampered
    {c : Cert} {a₀ a : Artifact} (hc : IssuedFor c a₀) (h : a ≠ a₀) :
    reprove a ≠ c := fun hmatch => h ((reprove_matches_iff_untampered hc).mp hmatch)

end Cert

end PCA

-- Axiom audit for the target theorem.
#print axioms PCA.Cert.reprove_matches_iff_untampered

