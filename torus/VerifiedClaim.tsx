/**
 * VerifiedClaim — a certificate badge that binds a visual/textual claim to a
 * formally-verified theorem, resolved through the honesty firewall.
 *
 * THE HONESTY CONTRACT (non-negotiable):
 *   - A verified badge is rendered ONLY when the theorem resolves to a real
 *     record in the public verified registry.
 *   - If the theorem is NOT in the registry (or the lookup errors), the
 *     component renders a visually DISTINCT, red "⊘ UNVERIFIED" BLOCKED state.
 *     It NEVER renders a verified badge for an unbacked claim.
 *   - CONJECTURE resolves in-registry but is NOT a proof: it renders as a
 *     distinct "claimed / not proved" state, never a green verified badge.
 *
 * Self-contained: depends only on React + the useVerified hook. Styling via
 * Tailwind-style className strings (the torus site is React/Tailwind/shadcn).
 * Works light + dark; keyboard-focusable and screen-reader labelled.
 */

import React from "react";
import { useVerified, type VerifiedRecord } from "./useVerified";

export interface VerifiedClaimProps {
  /** Human-facing claim the visual is asserting (e.g. "exactly 5 residues"). */
  claim: string;
  /** Fully-qualified theorem name backing the claim (registry key). */
  theorem: string;
  /** Optional extra classes for the outer element. */
  className?: string;
}

interface Style {
  label: string;
  glyph: string;
  /** wrapper classes (border/background/text) for light + dark. */
  wrap: string;
  /** small pill/tag classes. */
  pill: string;
  verified: boolean;
}

// Per-register presentation. `verified: true` only for registers that legitimately
// represent a completed, kernel/AXLE-checked proof or definition.
const REGISTER_STYLE: Record<string, Style> = {
  PROVED: {
    label: "Verified",
    glyph: "✓",
    wrap:
      "border-emerald-300 bg-emerald-50 text-emerald-900 " +
      "dark:border-emerald-700 dark:bg-emerald-950 dark:text-emerald-100",
    pill: "bg-emerald-600 text-white dark:bg-emerald-500",
    verified: true,
  },
  DEFINITION: {
    label: "Verified definition",
    glyph: "≝",
    wrap:
      "border-sky-300 bg-sky-50 text-sky-900 " +
      "dark:border-sky-700 dark:bg-sky-950 dark:text-sky-100",
    pill: "bg-sky-600 text-white dark:bg-sky-500",
    verified: true,
  },
  DISCHARGED: {
    label: "Discharged to a known result",
    glyph: "⇢",
    wrap:
      "border-teal-300 bg-teal-50 text-teal-900 " +
      "dark:border-teal-700 dark:bg-teal-950 dark:text-teal-100",
    pill: "bg-teal-600 text-white dark:bg-teal-500",
    verified: true,
  },
  CONDITIONAL: {
    label: "Conditional (premise open)",
    glyph: "⊢?",
    wrap:
      "border-amber-300 bg-amber-50 text-amber-900 " +
      "dark:border-amber-600 dark:bg-amber-950 dark:text-amber-100",
    pill: "bg-amber-600 text-white dark:bg-amber-500",
    verified: false, // conditional is NOT an unconditional proof
  },
  CONJECTURE: {
    label: "Conjecture — not proved",
    glyph: "◇",
    wrap:
      "border-violet-300 bg-violet-50 text-violet-900 " +
      "dark:border-violet-700 dark:bg-violet-950 dark:text-violet-100",
    pill: "bg-violet-600 text-white dark:bg-violet-500",
    verified: false, // named conjecture, never a proof
  },
};

// The mandatory BLOCKED presentation: unbacked / missing / errored claims.
const BLOCKED_STYLE: Style = {
  label: "UNVERIFIED",
  glyph: "⊘",
  wrap:
    "border-red-400 bg-red-50 text-red-900 " +
    "dark:border-red-600 dark:bg-red-950 dark:text-red-100",
  pill: "bg-red-600 text-white dark:bg-red-500",
  verified: false,
};

function Row({ k, v }: { k: string; v: React.ReactNode }) {
  return (
    <div className="flex gap-2 text-xs leading-5">
      <span className="shrink-0 font-medium opacity-70">{k}</span>
      <span className="break-words font-mono">{v}</span>
    </div>
  );
}

function Certificate({ rec }: { rec: VerifiedRecord }) {
  const checker =
    rec.verified_by ??
    (rec.axle_verdict ? "AXLE" : "—");
  return (
    <div className="mt-2 flex flex-col gap-1 border-t border-current/20 pt-2">
      <Row k="theorem" v={rec.name} />
      <Row k="source" v={rec.source} />
      <Row k="checker" v={`${checker}${rec.env ? ` · ${rec.env}` : ""}`} />
      {rec.axle_verdict && <Row k="verdict" v={rec.axle_verdict} />}
      <Row
        k="axioms"
        v={
          rec.axioms.length
            ? `${rec.axioms.join(", ")}${rec.axioms_ok ? " (clean)" : " (nonstandard)"}`
            : "none"
        }
      />
      {rec.conditional_rung && <Row k="rung" v={rec.conditional_rung} />}
      {rec.discharged_by && <Row k="discharged by" v={rec.discharged_by} />}
    </div>
  );
}

export function VerifiedClaim({ claim, theorem, className = "" }: VerifiedClaimProps) {
  const { record, status } = useVerified(theorem);

  // Loading: neutral, non-committal skeleton (never implies verified).
  if (status === "loading") {
    return (
      <span
        role="status"
        aria-live="polite"
        aria-label={`Checking verification for claim: ${claim}`}
        className={
          "inline-flex items-center gap-2 rounded-md border border-dashed " +
          "border-slate-300 bg-slate-50 px-3 py-1.5 text-sm text-slate-600 " +
          "dark:border-slate-600 dark:bg-slate-900 dark:text-slate-300 " +
          className
        }
      >
        <span className="animate-pulse" aria-hidden="true">
          ⋯
        </span>
        <span>Checking verification…</span>
      </span>
    );
  }

  // Resolve the presentation. Missing record OR error => BLOCKED (mandatory).
  const style: Style =
    status === "verified" && record
      ? REGISTER_STYLE[record.register] ?? BLOCKED_STYLE
      : BLOCKED_STYLE;

  const isBlocked = !style.verified;
  const blockedReason =
    status === "error"
      ? "verification lookup failed"
      : !record
        ? "not in the verified registry"
        : record.register === "CONJECTURE"
          ? "registered as a conjecture — not proved"
          : record.register === "CONDITIONAL"
            ? "conditional on an open premise"
            : "unverified";

  const ariaLabel = isBlocked
    ? `UNVERIFIED. Claim "${claim}" is ${blockedReason}. No verified certificate is shown.`
    : `Verified. Claim "${claim}" is backed by theorem ${record?.name} ` +
      `(${record?.register}), checked by ${record?.verified_by ?? "AXLE"} ` +
      `on ${record?.env ?? "the verified core"}.`;

  return (
    <span
      role="note"
      tabIndex={0}
      aria-label={ariaLabel}
      data-verified={!isBlocked}
      data-register={record?.register ?? "MISSING"}
      className={
        "group inline-flex max-w-md flex-col rounded-md border px-3 py-2 text-sm " +
        "shadow-sm outline-none transition focus-visible:ring-2 " +
        "focus-visible:ring-offset-1 focus-visible:ring-current " +
        style.wrap +
        " " +
        className
      }
    >
      <span className="flex items-center gap-2">
        <span
          aria-hidden="true"
          className={
            "inline-flex h-5 min-w-[1.25rem] items-center justify-center rounded px-1 " +
            "text-xs font-bold " +
            style.pill
          }
        >
          {style.glyph}
        </span>
        <span className="font-semibold uppercase tracking-wide">
          {isBlocked && status !== "verified" ? "⊘ UNVERIFIED" : style.label}
        </span>
      </span>

      <span className="mt-1 font-medium">{claim}</span>

      {isBlocked ? (
        <span className="mt-1 text-xs opacity-80">
          {blockedReason}. A picture cannot show a claim the registry does not
          back.
          {theorem ? (
            <>
              {" "}
              (<span className="font-mono">{theorem}</span>)
            </>
          ) : null}
        </span>
      ) : record ? (
        <Certificate rec={record} />
      ) : null}
    </span>
  );
}

export default VerifiedClaim;
