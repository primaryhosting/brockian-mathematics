# A Concrete Contribution to the seL4 Ecosystem — Verified capDL Isolation

*Companion to the Galois capability brief. Where `CAPABILITY_BRIEF.md` shows the demonstrator on our own models, this is a contribution aimed at the **actual seL4 org** — grounded in its live repositories, filling an acknowledged gap, and requiring no Isabelle bridge.*

## The gap, in one line

**seL4 the kernel is proven; the systems built *on* it are not.** The kernel's isolation guarantee is conditional on the system above it being wired correctly — and that wiring is described by **capDL** (`github.com/seL4/capdl`), the Capability Distribution Language that `microkit` and CAmkES systems compile to. Nothing in the ecosystem formally checks that a given capDL spec actually enforces the isolation architecture the integrator intended. A stray capability across a protection-domain boundary silently breaks isolation, and today that is caught by review, not proof.

## What we built

**A verified capDL isolation checker** (`Brockian.HighAssurance.CapDLIsolation`, AXLE-verified, axiom-clean): a decidable function that takes a capDL capability distribution + a protection-domain assignment + an inter-domain connection policy, and *certifies* that every capability stays within the permitted domain connections — with a machine-checked **soundness-and-completeness** theorem that the checker's verdict is exactly isolation.

<!-- THEOREMS: filled from the verified module -->
- `checkIsolation_correct` — the decidable checker exactly decides `WellIsolated`: a `true` verdict is a machine-checked certificate that the capDL spec enforces the policy.
- `names_only_permitted` — in a well-isolated spec no object can even *name* an object across a disallowed boundary.
- `isolated_domain_unreachable` — a fully-isolated protection domain is unreachable, *transitively through any chain of capabilities*, from outside — the seL4 isolation guarantee at the capDL level.
- Non-vacuity: a microkit-style two-domain system (driver + app sharing only a permitted endpoint, plus a fully-isolated secret domain) *passes*; a mis-wired variant with a stray cross-domain capability is *rejected*.

Because it is a **decidable checker with a proof of soundness**, it is not just a theorem about a model — it is a *tool*: feed it a real system's capability distribution and it returns a certificate, or a specific rejected edge. That is directly consumable by the seL4 build pipeline.

## Why this is the right first contribution (grounded in the live org)

The seL4 org today has two centers of gravity:
- **The mature Isabelle proof corpus** — `l4v` (629★, 73 open issues, actively maintained). Contributing here means Isabelle/HOL — a real barrier, and the Phase-1 bridge.
- **A fast-moving, mostly-unverified systems frontier** — `microkit` (197★, Rust), `rust-sel4` (210★, Rust), `capdl` (Haskell tooling). This is where seL4-*based* systems are built, and where an outside contributor with an independent proving pipeline can add value *immediately, without the Isabelle bridge*.

A capDL isolation checker sits exactly in that frontier: it operates on the artifact (`capdl`) that every static seL4 system already produces, it certifies the property (`microkit`/CAmkES isolation) integrators most need, and it is self-contained — a PR-shaped deliverable, not a pitch.

## How it would land as a real contribution

1. **Now (this artifact):** the verified checker + soundness, with a microkit-shaped worked example.
2. **Packaging:** a small front-end that parses a real capDL spec (the JSON/Haskell-emitted distribution from `capdl-tool`) into the checker's input, so it runs on actual system descriptions — surfaced as an optional CI check (`github.com/seL4/ci-actions`) that certifies isolation or flags the offending capability.
3. **Deepening (Phase 1+):** connect the capDL-level guarantee to the kernel-level integrity proof (the checker certifies the *initial* state; the kernel's proven integrity keeps it invariant), and extend to information-flow (which domains may *influence* which, not merely *name* which) using the noninterference machinery already in the demonstrator.

## The honest boundary

- This checks the **capability distribution** (the isolation architecture). It does not verify the C of a driver or the Rust of a component — that is the Verus/SAW code-level work (Phase 2).
- The domain assignment and the connection policy are the **spec** — the human statement of "what isolation means for this system." The checker proves the wiring *matches* that spec; it cannot tell you the spec is the right one.
- It complements, not replaces, `l4v`: `l4v` proves the kernel enforces capabilities faithfully; this proves a given system's capabilities encode the intended isolation.

*Every theorem named here is AXLE-verified and renders its own certificate on the Proof-Carrying Systems lab.*
