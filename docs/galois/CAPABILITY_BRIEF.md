# Capability Brief — AI-Assisted Formal Verification, Independently Gated

**Prepared for:** Galois, Inc.
**Subject:** An AI-driven, independently-verified formal-methods pipeline, demonstrated on seL4-class security properties.
**Date:** 2026-08-21
**Status of every theorem cited here:** machine-checked in Lean 4 / Mathlib, **independently re-verified** by the AXLE cloud prover (env `lean-4.32.2`), and **axiom-audited** (axioms ⊆ `{propext, Classical.choice, Quot.sound}` — no `sorry`, no `native_decide`, no `sorryAx`). Nothing in this document is aspirational unless explicitly labeled OPEN or CONDITIONAL.

---

## 1. One-paragraph thesis

The scarce resource in formal methods has inverted: generating a candidate proof is now cheap, and the entire locus of value is **verification and trust**. We have built a pipeline that (a) generates proofs at scale with AI, (b) re-verifies each one with an *independent* prover, (c) audits axioms and **statement fidelity**, and (d) records provenance so a claim renders as *verified*, *conditional*, or *unverified* — never ambiguously. We are not proposing to re-verify seL4 (already done, in Isabelle, over ~20 person-years). We are demonstrating that this pipeline can verify **seL4-class properties** — integrity, confidentiality/noninterference, memory separation, capability confinement — and that it carries a **trust discipline** built for exactly the failure modes AI introduces.

## 2. What we built (the demonstrator) — verified security core of a capability microkernel

Every item below is a live, independently-verified Lean theorem. Fully-qualified names are given so they can be checked against the public registry.

### 2.1 Integrity — authority confinement
`Brockian.HighAssurance.CapabilityIntegrity.integrity_confinement` — over a capability access-control state machine (`Right = read | write | grant`, guarded `grant`/`revoke` operations), if the initial capability set is within policy, then **every reachable state's capabilities stay within policy**. Proved by induction over arbitrary operation sequences (`Relation.ReflTransGen`), not by finite enumeration.

Non-vacuity (also verified): `grant_can_progress` (authority *does* flow when permitted), `grant_blocked_off_policy` (the guard operationally rejects an unauthorized grant), `integrity_is_nontrivial` (a concrete off-policy state is provably excluded from reachability). The grant-guard is load-bearing: delete the policy check and the theorem becomes false. This is the direct analog of seL4's integrity theorem.

### 2.2 Confidentiality — noninterference
`Brockian.HighAssurance.Noninterference.noninterference` — on a labeled state machine with an explicit "high must not flow to low" policy, the low domain's final observation depends **only on the low actions**; secret (high) actions leak zero information downward. Proved via the standard **Rushby/seL4 unwinding architecture**: `step_consistency` (a step preserves low-indistinguishability) + `local_respect` (a high action is invisible to low), composed by induction over an arbitrary run. Non-vacuous: secrets provably change while the low view stays fixed.

### 2.3 Proof-Carrying Apps — the software-security layer (already in production use)
Seven modules, 20+ verified theorems (namespaces `PCA`, `PCA.Isolation`, `PCA.WriteIntegrity`, `PCA.Cert`, `PCA.Invariant`, `PCA.Coverage`, `PCA.Fix`):
- **Access control:** `PCA.default_deny`, `PCA.Invariant.default_deny_excludes_only_allowlist`, `PCA.Invariant.rls_off_implies_no_row_protection`.
- **Isolation:** `PCA.Isolation.priv_escape_monotone`, `PCA.Isolation.null_escape_iff_unowned_reachable`, `PCA.Isolation.no_clean_proved_with_escape`.
- **Write integrity:** `PCA.WriteIntegrity.member_check_prevents_cross_tenant_write`, `PCA.WriteIntegrity.with_check_true_admits_forge`.
- **Crypto/cert:** `PCA.Cert.ed25519_verify_sound`, `PCA.Cert.reprove_matches_iff_untampered`.

### 2.4 The kernel security core (wave 1 — all verified, inductive, non-vacuous)
- **Take-grant authority confinement** — `Brockian.HighAssurance.TakeGrant.authority_confined` + `confinement`, `confinement_of_coloring`: the classical capability-security result (seL4 integrity is a special case) — reachable authority never exceeds the take-grant closure. Includes an *honest* sound-but-strict over-approximation (`closure_is_strict_over_approximation`).
- **Lattice noninterference** — `Brockian.HighAssurance.LatticeNoninterference.noninterference`: Goguen–Meseguer/Rushby confidentiality over an *arbitrary security lattice* (diamond-lattice witness), by unwinding. A domain's observation depends only on domains cleared to influence it.
- **Memory separation** — `Brockian.HighAssurance.MemorySeparation.{frame, cross_subject_isolation, memory_separation}`: separation-kernel memory integrity — an address changes only under an authorized write; disjoint-authority subjects are mutually invisible.
- **IPC confinement** — `Brockian.HighAssurance.IPCConfinement.ipc_confinement`: capability-gated endpoints — every delivered message is explained by an authorized send; no unmediated channel.
- **Refinement / forward simulation** — `Brockian.HighAssurance.Refinement.{forward_simulation, refinement_run, safety_transported}`: the seL4 *methodology* itself — an abstract safety property transported to a structurally-different concrete layer through a coupling relation + load-bearing invariant.

Together these five plus §2.1–2.2 are the verified security core of a capability microkernel: **integrity, confidentiality (2-domain and full-lattice), spatial separation, communication confinement, and refinement** — the crown-jewel property classes of the seL4 proof, mechanized and independently gated.

### 2.5 Crypto layer (wave 2 — Cryptol/SAW idiom, honest about assumptions)
Each theorem separates what is proved *unconditionally on the model* from the one genuinely *computational* assumption, which is always named explicitly (never smuggled in as proved).
- **MAC** — `Brockian.HighAssurance.MAC.{verify_correct, verify_sound, mac_determines_tag, cross_key_rejects, no_forgery}`: correctness, soundness (verify accepts *only* the true tag), unique-tag, and cross-key rejection are unconditional; computational unforgeability is derived from an explicit hardness premise `hHard`. The reduction "forgery ⇒ computing the tag" is itself the unconditional `forged_reveals_tag`.
- **AEAD** (encrypt-then-MAC) — `Brockian.HighAssurance.AEAD.{aead_roundtrip, auth_required, tamper_rejected, replay_rejected}`: roundtrip correctness and fail-closed authentication are unconditional; tamper/replay rejection is gated on MAC collision-freedom. A concrete XOR construction *provably satisfies* that assumption (`cMac_inj2`), so the hypotheses are demonstrably non-vacuous.
- **Merkle tamper-evidence** — `Brockian.HighAssurance.Merkle.{inclusion_complete, tamper_detected, root_binding, inclusion_sound}`: completeness is assumption-free; tamper-evidence and root-binding need *no axioms*; full soundness holds under honestly-stated hash-injectivity + domain-separation (the agent flagged the domain-separation requirement rather than hide it — without it soundness is genuinely false).
- **Constant-time / side-channel** — `Brockian.HighAssurance.ConstantTime.{ct_trace_noninterference, leaky_program_leaks}`: for data-oblivious programs the observable trace (branch outcomes + accessed addresses = the timing/cache leakage model) is provably independent of secrets; a `branchOnSecret` counterexample proves the restriction has teeth; `condMove` preserves functional correctness while leaking nothing.

The honesty pattern across the crypto layer *is* the pitch to a high-assurance audience: every computational assumption is a named, visible hypothesis, and the structural guarantees around it are proved outright.

## 2.6 Multi-prover cross-verification (Phase-1 preview — the answer to "Lean-only")

`scripts/smt_gate.py` + `docs/galois/smt_cross_verification.json`: three security-relevant properties — a bitvector one-time-pad involution `(m⊕k)⊕k = m`, a boolean access-control default-deny law, and an array-theory unauthorized-write memory frame — are each discharged **independently by Z3 (SMT, v4.16.0)** *and* by **Lean 4/Mathlib (AXLE-verified)** on the identical statement (`Brockian.HighAssurance.SMTMirror.*`). The gate marks a property **CROSS-VERIFIED only when both verdicts agree**. Result: `ALL CROSS-VERIFIED: True`.

This is a working proof-of-concept of the multi-prover gate (§7 Phase 1): the same class of obligation that seL4's binary translation-validation and Galois's SAW/Cryptol workflow discharge with SMT is here checked by an SMT solver *and* an interactive prover, with agreement required. "Verified" is not Lean-only.

## 3. The pipeline (how, and why it is trustworthy)

```
  AI generation  →  independent AXLE re-verification  →  axiom audit  →
  statement-fidelity review  →  provenance-gated registry  →  honest certificate surface
```

- **Independent verification.** Proofs are generated by one system and re-checked by another (AXLE, a pinned cloud Lean+Mathlib). A proof only counts if a *second, independent* toolchain agrees.
- **Axiom audit.** Every registered theorem's `#print axioms` must be a subset of the three standard foundational axioms — no `native_decide` (unverified compiler reflection), no `sorryAx`.
- **Statement fidelity.** The hard problem in AI verification is not false proofs (the kernel catches those) but *valid proofs of subtly wrong statements*. Each promotion is fidelity-checked against the intended statement.
- **Provenance + honest tiers.** The registry distinguishes `PROVED` (green), `CONDITIONAL` (proved under a named open hypothesis — never green), `CONJECTURE` (statement only), and `DEFINITION`. A public certificate surface renders these states distinctly; a claim with no backing theorem renders as a visible **⊘ UNVERIFIED** state, not a badge.

## 4. The trust story (this is the part built for AI-in-the-loop)

We recently audited **114 AI-produced "proofs" of famous open problems** (Twin Primes, Goldbach, RH, P-vs-NP, and analogues). Result: **zero unsound proofs** — but the audit surfaced the *real* failure modes:
- **9 empty stubs** — imports-only files with grand names, scored as "passing proofs" by a naive `no-sorry` classifier. (We added a `≥1 theorem` guard.)
- **Pervasive mislabeling** — honest *conditional reductions* (`Conjecture ⇐ NamedHypothesis`) and *circular repackagings* (a hypothesis provably equivalent to its conclusion) presented under the bare conjecture name.

The lesson, and the pitch: **the enemy was never a false proof; it was a true proof of the wrong thing, and an empty file with a grand name.** A high-assurance shop adopting AI proving needs exactly this failure taxonomy and the gate that enforces it. That is as much of the deliverable as the theorems.

## 5. On seL4 specifically

seL4 is already fully verified (~10k lines of C, ~1M lines of Isabelle/HOL, a refinement stack abstract ⊒ executable ⊒ C ⊒ binary, plus integrity/confidentiality/availability). We do **not** propose to re-prove it. Where AI-assisted verification is genuinely useful to the seL4 ecosystem:
1. **Proof engineering at the ~20:1 cost ratio** — the mechanical bulk (invariant maintenance, proof repair on code change, new-platform port re-verification).
2. **New properties / components above the kernel** — verifying seL4-*based* systems (the HACMS pattern).
3. **A second, independent verification leg** for confidence, and a provenance/trust layer for AI-generated proof contributions.

A companion document, `UNDERSTANDING_SEL4.md`, maps the seL4 proof structure to the specific points where this pipeline plugs in.

## 6. Honest limits

- **Ecosystem gap.** seL4 is Isabelle; Galois is SAW/Cryptol/Coq; we are Lean/AXLE. The pipeline's value is *multi-prover orchestration + trust*, not a claim that Lean subsumes these. A real engagement includes a bridge to an SMT/SAW/Isabelle backend for the gate.
- **The spec is human.** AI verifies; it does not tell you what "correct" means. Statement fidelity is a permanent human responsibility.
- **Trust bootstrapping.** Who verifies AXLE, or the SMT solver? Real high-assurance answers this with proof-producing solvers and a small trusted kernel; our gate must eventually verify itself.
- **Kernel *implementation* is a multi-year systems effort.** We can build the verified *mathematics* of a secure kernel now (§2); a running verified kernel down to binary is seL4-scale.

## 7. Proposed engagement (tiers)

1. **Phase 0 (done — this brief).** Verified seL4-class security core + the gate + provenance surface.
2. **Phase 1 — multi-prover gate.** Add an SMT (Z3/CVC5) and a second interactive backend to the verification gate, so "verified" is not Lean-only. This is the step that makes the capability *complete* rather than a large Lean corpus.
3. **Phase 2 — code level.** Wire SAW+Cryptol (crypto) and Verus/Dafny (code) into dispatch and the gate — Galois's core workflow, and where seL4-based-systems verification lives.
4. **Phase 3 — a verified capability microkernel model**, refined toward executable code, as a joint high-assurance artifact.

---

*All theorem names in this document resolve in the public verified registry (`torus.riemannlab.com`), where each renders its own certificate. Conditional and open results are labeled as such and never render as verified.*
