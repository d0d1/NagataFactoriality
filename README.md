# NagataFactoriality

A Lean 4 / Mathlib project aimed at a **publication-ready formalization of a prime-generated version of Nagata's factoriality theorem**.

## Current status

- The repository contains a Mathlib-based formal development around localization, irreducibles, and UFDs.
- `NagataFactoriality\Nagata\Theorem.lean` now proves a **prime-generated** version of Nagata's factoriality theorem.
- `NagataFactoriality\Nagata\Theorem.lean` also exposes abstract `_isLocalization` wrappers and packaged entry points for prime-generator closures, including a finite-prime-generator criterion.
- `NagataFactoriality\Localization\IsLocalization.lean` provides a small helper API for moving between concrete `Localization S` proofs and abstract `IsLocalization` instances.
- The application layer now contains two structurally distinct Nagata-based routes to the polynomial UFD theorem:
  - `NagataFactoriality\Applications\Laurent.lean` localizes at powers of `X`
  - `NagataFactoriality\Applications\FractionField.lean` localizes at the constant primes and compares with `Frac(R)[X]`
- `NagataFactoriality\Applications\Laurent.lean` also contains an iterated polynomial corollary obtained by reusing the same Nagata package.
- `isabelle\Nagata-Factoriality\` now contains an AFP-style Isabelle/HOL session that formalizes the prime-generated multiplicative-set core, the AFP-localization helper layer, record-based Nagata theorem variants for prime-generated and prime-or-unit multiplicative sets, and an abstract polynomial application for localization away `X`.
- CI, citation metadata, and a successful full `lake build` are in place.
- `paper\main.tex` now provides a manuscript draft with introduction, cited related work, proof architecture, upstreaming scope, and artifact-release guidance.
- No public formalization of Nagata's factoriality theorem is currently known to us from available Lean, Coq, or Isabelle sources.
- `paper\main.tex` now contains a submission-quality manuscript draft.

## Contribution summary

At this point, the repository contributes:

1. A Lean 4 / Mathlib formalization of a **prime-generated** Nagata-style factoriality theorem for noetherian domains.
2. A public theorem surface that includes both concrete `Localization S` statements and abstract `_isLocalization` wrappers, together with packaged variants for arbitrary and finite prime-generator families.
3. Supporting localization lemmas that bridge the concrete and abstract localization interfaces.
4. Two theorem-driven Nagata applications for `R[X]` via different localizations, plus an iterated polynomial corollary showing direct reuse of the package.
5. An AFP-style Isabelle/HOL session that packages the prime-generated multiplicative-set infrastructure, a wrapper layer over AFP localization, record-based Nagata theorem variants, and the first abstract polynomial application layer as the core of the Isabelle port.

## Related-work snapshot

- No public formalization of Nagata's factoriality theorem is currently known to us from available Lean/Mathlib, Coq/MathComp, or Isabelle/AFP sources.
- The manuscript draft in `paper\main.tex` records the nearby formal-library context and states this novelty claim cautiously as a present public-state assessment.

## Draft abstract

We present a Lean 4 / Mathlib formalization of Nagata's factoriality theorem for noetherian integral domains. The central hypothesis is a *prime-generated* condition on the multiplicative set: every element of the submonoid is a finite product of elements that are both prime in the ring and members of the submonoid. Under this hypothesis, if the localization is a UFD, then so is the base ring. The formal development packages the result both for the concrete type `Localization S` and at the abstract `IsLocalization` level, with the transport chain itself available through the abstract interface. As applications, we give two Nagata-based proofs that if `R` is a noetherian UFD then `R[X]` is a UFD—one via Laurent-polynomial localization at powers of `X`, and one via localization at the constant primes and comparison with `Frac(R)[X]`—and we derive the iterated polynomial corollary `R[X][Y]` by reusing the same package. No public formalization of Nagata's factoriality theorem is currently known to us from available Lean, Coq, or Isabelle sources.

## Publication target

The realistic path for this repository is an **ITP/FM-style paper** together with an upstreamable Mathlib contribution:

1. Turn the current formalization into a paper-quality contribution statement.
2. Complete the related-work and prior-formalization audit.
3. Finish the publication-facing exposition around the theorem and its applications.
4. Write the paper around the resulting formalization.

The current draft entry point for that paper is `paper\main.tex`, which now also records the current related-work position and release-packaging guidance.
The current tagged submission snapshot is `afm-submission-draft-2026-04-04`.

See `ROADMAP.md` for the full execution plan.

## Project snapshot

- 18 Lean source files under `NagataFactoriality\`
- 1352 Lean source lines under `NagataFactoriality\`
- 97 theorem/lemma declarations

## Limitations and next publication steps

- The related-work position is now citation-backed, but the manuscript will still need venue-specific bibliography and prose polish.
- The theorem surface and transport chain now both support the abstract `IsLocalization` interface; the remaining upstreaming question is how best to split that material into reviewable Mathlib PRs.
- The second polynomial route is meant as a structurally distinct reuse test, not as a stronger theorem than the Laurent-polynomial argument.
- Some localization API choices are tailored to this repository and may still benefit from later Mathlib-oriented cleanup.

## Concrete upstreaming split

If upstreaming is pursued, the current artifact now supports a concrete three-stage split:

1. **PR1:** `PrimeGenerated`, `Avoids`, zero-exclusion lemmas, closure/powers lemmas, and generic multiset bookkeeping from `NagataFactoriality\Nagata\Lemmas.lean` plus `Localization\MultSet.lean`.
2. **PR2:** abstract localization helpers from `NagataFactoriality\Localization\IsLocalization.lean` together with the abstract divisibility / irreducibility / primality transport lemmas in `NagataFactoriality\Nagata\Lemmas.lean`.
3. **PR3:** the abstract Nagata theorem family in `NagataFactoriality\Nagata\Theorem.lean`, including the closure and finite-prime-generator corollaries.

The application files are intentionally left outside that split and serve as downstream demonstrations rather than upstreaming prerequisites.

## Building

```bash
lake exe cache get
lake build
```

## Isabelle / AFP scaffold

The directory `isabelle\Nagata-Factoriality\` is organized as a single-session AFP entry:

- `ROOT` defines the `Nagata-Factoriality` session in chapter `AFP`
- `Prime_Generated.thy` formalizes prime-generated multiplicative sets and closure lemmas
- `Localization_Interface.thy` packages a small wrapper layer over AFP's `Localization_Ring`, including representative equality, surjectivity, denominator rescaling, cross-multiplication, unit, and injectivity lemmas
- `Nagata_Lemmas.thy` proves the record-based descent lemmas and theorems `nagata_theorem` and `nagata_theorem_of_prime_or_unit`
- `Polynomial_Applications.thy` proves `polynomial_prime_X` over fields together with the abstract away-`X` descent theorem `polynomial_factorial_of_localized_X_factorial`
- `Fraction_Field_Applications.thy` packages the constant-prime closure specialization `polynomial_factorial_of_localized_constant_primes_factorial`, i.e. the abstract fraction-field route before the final localization/comparison step
- `Nagata_Factoriality.thy` exposes the top-level entry surface and the constant-prime polynomial corollary
- `document\root.tex` and `document\root.bib` provide the AFP document sources

Because this session now depends on the AFP entry `Localization_Ring`, the AFP
theory collection must be on Isabelle's session path. With Isabelle installed,
one working AFP-style build command is:

```bash
isabelle build -d /path/to/afp/thys -v -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -D isabelle/Nagata-Factoriality
```

## References

- Nagata, M. *Local Rings*, 1962
- Samuel, P. *Lectures on Unique Factorization Domains*, 1964
- Matsumura, H. *Commutative Ring Theory*, Cambridge University Press, 1989
