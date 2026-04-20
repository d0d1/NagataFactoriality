# 01 Adversarial Review

This is a converged adversarial review of the submission paper after two independent harsh passes and manual re-checking against the repository and cited sources. Only findings that survived re-verification are included here.

Several of the concrete manuscript-drift findings recorded here were then acted
on in the accompanying revision to `paper/main.tex`. Unless a section says
otherwise, the quoted manuscript line references below refer to the pre-fix
draft reviewed during this pass, not the revised manuscript now shipped in this
branch.

## Overall verdict

The Lean artifact looks real, nontrivial, and substantially consistent with the paper's high-level contribution claim. At review start, the biggest problem was **trust erosion from stale prose and stale code listings**, not evidence of fake mathematics. I do **not** see a clear mathematical error in the core formalization. Several of those paper/code-drift issues were then corrected in the accompanying revision.

## Severity summary

| Severity | Finding |
| --- | --- |
| Medium | In the pre-fix draft, multiple displayed `_isLocalization` signatures did not match the shipped Lean code; the accompanying revision fixes them. |
| Medium | In the pre-fix draft, the prose description of `nagata_theorem_isLocalization` described a `Localization S`/`algEquiv` transport design that the current code did not use; the accompanying revision fixes that drift. |
| Medium | In the pre-fix draft, the paper never stated whether the Isabelle/HOL companion was part of the submission artifact or out of scope; the accompanying revision now does. |
| Low | In the pre-fix draft, reproducibility infrastructure was described inaccurately: the checked-out artifact was not pinned by a committed `lake-manifest.json`. The accompanying revision fixes this. |
| Low | Several historical/source claims are plausible but under-cited: the paper asks the reader to trust book-level references without page or theorem pointers. |
| Low | The paper had several exposition-level rough edges during review: repeated novelty claims, a long/repetitive lessons section, abrupt proof-sketch variables, and visible LaTeX layout warnings in the original committed build logs. |

## 1. Hallucination / unsupported claims

### 1.1 The displayed abstract theorem signatures are not the kernel-checked signatures

**Severity:** Medium

This finding applied to the pre-fix draft reviewed in this pass. The
accompanying revision updates the displayed signatures to match the Lean code.

The paper states:

- `paper/main.tex` lines 661-665: "All declarations shown below are kernel-checked."

But the displayed abstract theorem signatures do not match the actual Lean code:

- `paper/main.tex` lines 711-716 show `nagata_theorem_isLocalization` with `[CancelCommMonoidWithZero T]`
- `paper/main.tex` lines 737-744 and 753-759 do the same for the prime-generator `_isLocalization` variants
- `NagataFactoriality/Nagata/Theorem.lean` lines 20-27, 40-46, and 61-66 require `[IsDomain T]`

`IsDomain T` is strictly stronger than `CancelCommMonoidWithZero T`. This is not a stylistic paraphrase; it is a different API surface. A reader relying on the paper would infer weaker hypotheses than the code actually requires.

### 1.2 The proof-architecture description of the abstract theorem is stale

**Severity:** Medium

This finding applied to the pre-fix draft reviewed in this pass. The
accompanying revision rewrites the prose to describe the current direct
abstract-interface proof path.

The paper says:

- `paper/main.tex` lines 720-724: the proof core still descends through concrete `Localization S`, and the UFD structure is transported via `IsLocalization.algEquiv`

The shipped theorem does something else:

- `NagataFactoriality/Nagata/Theorem.lean` lines 23-27 directly call `nagata_key_lemma_primeGenerated_isLocalization` at target `T` and never build a concrete `Localization S`, never invoke `IsLocalization.algEquiv`, and never transport the UFD structure in the way the prose describes.

This reads like stale text left over from an earlier implementation. For a paper whose contribution is partly about proof architecture, that is a real credibility problem.

### 1.3 Historical claims are plausible but weakly supported as written

**Severity:** Low

The paragraph at `paper/main.tex` lines 1365-1378 makes several fairly specific historical claims:

- Nagata 1957 gave the result in the stated form
- Samuel treats the single-generator/polynomial case cleanly
- Matsumura and Kaplansky present the result in full generality
- the Stacks Project gives a modern exposition and also includes the class-group-to-UFD statement

The sources are real, but the paper gives **no page numbers, theorem numbers, chapter references, or section pointers** for the book claims. That turns a checkable literature statement into "trust me, I remember the books." For a submission paper, that is too loose.

## 2. Correctness

### 2.1 What looks correct

- The repository contains **18 Lean source files** under `NagataFactoriality/`
- The Lean LOC total is **1546**
- The theorem/lemma count is **97**
- I found **no** `sorry`, `admit`, `axiom`, or `native_decide` in `NagataFactoriality/**/*.lean`
- The main named results cited in the paper exist in the code:
  - `nagata_theorem`
  - `nagata_theorem_isLocalization`
  - `nagata_theorem_of_prime_generators`
  - `nagata_theorem_of_finite_prime_generators`
  - `dvd_of_localization_dvd_primeGenerated`
  - `localization_irreducible_of_irreducible_primeGenerated`
  - `prime_of_localization_prime_primeGenerated`
  - `laurentPolynomial_uniqueFactorizationMonoid`
  - `polynomial_uniqueFactorizationMonoid_via_nagata`
  - `polynomial_uniqueFactorizationMonoid_via_fractionField`

### 2.2 What still weakens the correctness story

The core problem is not that the artifact appears mathematically broken. The problem is that the paper **misquotes its own code** in the most reader-visible section ("Formal Lean statements"). That makes every other code-facing statement less trustworthy than it should be.

### 2.3 Minor proof-sketch issue

**Severity:** Low

At `paper/main.tex` lines 432-437, the proof sketch for the "irreducibles dividing prime factorizations are prime" lemma introduces a quotient variable `d` abruptly ("then `q` divides `p * d` for some `d`") without explicitly saying it comes from the witness that `p` divides the product of the prime factors. This is not a mathematical error; it is a proof-sketch clarity lapse.

## 3. Completeness

### 3.1 The paper never resolves the Isabelle companion's scope

**Severity:** Medium

This was resolved in the accompanying revision, which now marks the Isabelle
directory out of scope for the paper's Lean artifact claims.

The repository README and artifact surface prominently advertise an Isabelle/HOL companion under `isabelle/`, but the paper is written as a Lean-only submission. A reviewer cloning the artifact can reasonably ask:

- Is the Isabelle development part of the claimed contribution?
- Is it an out-of-scope companion experiment?
- Is it unfinished and intentionally omitted?

The paper should say so explicitly. Right now the artifact surface and the manuscript tell different stories about what the submission is.

### 3.2 The manuscript does not identify the exact submission snapshot in-body

**Severity:** Low

This was resolved in the accompanying revision by naming the submission tag
`afm-submission-draft-2026-04-04` in the release-packaging discussion.

There is a real remote tag, `afm-submission-draft-2026-04-04`, but the manuscript itself never names the exact tag or commit. It says only that the artifact is a tagged source release. That is weaker than it needs to be.

### 3.3 Related work is formalization-heavy but mathematically thin

**Severity:** Low

The paper discusses nearby formalization projects well enough, but the mathematical literature discussion is shallow relative to the confidence of its historical claims. If the paper wants to say "Samuel does X; Matsumura/Kaplansky do Y; we follow this tradition," it should support that with page-level citations.

## 4. Language / exposition

### 4.1 The lessons section is too long for the amount of new information it carries

**Severity:** Low

The "Lessons from the formalization" section is useful, but it is longer and more repetitive than it needs to be. The multiset-induction story, the dual proof-chain story, and the localization-interface story have already been explained earlier. Tightening this section would improve the paper immediately.

### 4.2 The novelty claim is repeated too often

**Severity:** Low

The accompanying revision trims some of this repeated priority language; this
section records why that cleanup was warranted.

The "first public formalization known to us" claim is appropriately hedged, but it appears repeatedly in the abstract, introduction, novelty section, and conclusion. Repeating it that often weakens rather than strengthens it.

### 4.3 Some wording is sloppier than the rest of the paper

**Severity:** Low

The accompanying revision fixes the imprecise "collapses" wording and one of
the abrupt proof-sketch transitions; this section records why those edits were
needed.

Examples:

- "collapses" for the prime-or-unit hypothesis is rhetorically punchy but imprecise
- the AFM-publications paragraph reads more like venue signaling than problem-specific related work
- several proof-sketch transitions assume more background than the rest of the exposition

### 4.4 The original committed LaTeX build logs showed layout warnings

**Severity:** Low

At review time, the tracked `paper/build1.log` and `paper/build2.log` each
recorded **12** `Overfull \hbox` / `Underfull \hbox` warnings. That did not
make the paper incorrect, but it undercut any "submission-quality manuscript"
self-description. The accompanying revision rebuilds the tracked PDF and logs
without those box warnings.

## 5. Plagiarism / originality

### 5.1 Plagiarism

I did **not** find evidence of textual plagiarism in spot checks. The mathematical material is standard textbook algebra and is attributed as such.

### 5.2 Originality

The originality is in the **formalization engineering**:

- prime-generated packaging instead of the degenerate prime-or-unit formulation
- theorem-family/API design
- two Nagata-based polynomial applications
- reusable localization-side transfer lemmas

The paper is not presenting new commutative algebra, and to its credit it mostly does not pretend otherwise.

### 5.3 Novelty claim

The novelty claim is hedged in a defensible way. Public-code searches did not turn up another Lean/Coq/Isabelle formalization of Nagata's factoriality theorem beyond this repository and its companion materials. Keep the hedge; do not sharpen it.

## 6. Reference-by-reference audit

| Key | Manual check | Supports cited use? | Notes |
| --- | --- | --- | --- |
| `baanen-dedekind` | Opened DOI landing and Crossref metadata | Yes | Supports the claim about Dedekind domains/class groups in Lean. |
| `bordg-localization` | Opened AFP entry page | Yes | Good support for Isabelle localization infrastructure. |
| `brasca-flt` | Opened DOI landing and Crossref metadata | Yes | Valid venue-context example of a large Lean 4 formalization. |
| `divason-berlekamp` | Opened DOI landing and Crossref metadata | Yes | Supports the claim about substantial factorization infrastructure in Isabelle. |
| `kaplansky1970` | Verified existence via OpenLibrary metadata | Partly | Bibliography is real; the paper's specific "full generality" claim is not pinpointed. Add a page/theorem citation. |
| `loeffler-zeta` | Opened DOI landing and Crossref metadata | Yes | Valid recent Lean related-work citation. |
| `mathlib` | DOI landing blocked by ACM; Crossref metadata opened | Yes | Bibliographically correct. Crossref confirms CPP 2020 paper. |
| `mathcomp` | Opened Zenodo page | Mostly | Supports Mathematical Components as a library/book ecosystem, but this is an indirect citation for current library capabilities. |
| `matsumura1989` | Opened OpenLibrary edition metadata (`OL7738339M`) | Partly | Bibliography is fine; specific theorem-use claim needs a page/chapter pointer. |
| `moura-lean4` | Opened DOI landing | Yes | Standard Lean 4 citation; fine. |
| `nagata1957` | Opened Crossref metadata; Project Euclid page blocked by anti-bot | Partly | Existence confirmed, but I could not manually inspect the open text. Add a pinpoint citation if using it for a specific theorem statement. |
| `nagata1962` | Opened OpenLibrary metadata (`OL26791762M`) | Partly | Real source; specific historical claim needs a page pointer. |
| `riou-derived` | Opened DOI landing and Crossref metadata | Yes | Valid Lean related-work citation. |
| `samuel1964` | Opened OpenLibrary edition page and Stanford catalog | Partly | Bibliography line is fine; specific claim about the single-generator/polynomial treatment needs page support. |
| `stacks` | Tag `0AFU` confirmed via cited web search result; direct Stacks fetch failed | Mostly | Tag `0AFU` supports the Nagata criterion claim. It does **not** by itself justify bundling the separate class-group-triviality claim into the same sentence; that part should be split or separately pinpointed. |

## 7. Artifact / reproducibility / repository-facing issues

### 7.1 The pinned-dependency description is inaccurate

**Severity:** Low

This was resolved in the accompanying revision, which now cites
`lakefile.lean` as the checked-in Mathlib pin and explains that
`lake-manifest.json` is generated locally.

At `paper/main.tex` lines 1332-1333 the paper says Mathlib is pinned by `lean-toolchain` and `lake-manifest.json`. In the committed artifact:

- `.gitignore` explicitly ignores `/lake-manifest.json`
- a fresh clone does **not** contain `lake-manifest.json`
- the actual committed dependency pin is in `lakefile.lean`

This is a small but real reproducibility inaccuracy.

### 7.2 The repo shipped the manuscript PDF but did not surface it

**Severity:** Low (repo-facing, not a paper-content defect)

`paper/main.pdf` is tracked, but the root README did not link to it at review
time. That is a discoverability failure for reviewers and readers.

## 8. Priority fixes before treating the paper as submission-grade

1. **Make Section 5 honest.** Fix the displayed `_isLocalization` signatures and any other listings that are no longer verbatim. **Resolved in the accompanying revision.**
2. **Fix the stale proof-architecture prose.** If the abstract theorem is now direct, say so; do not describe the old `Localization S`/`algEquiv` path. **Resolved in the accompanying revision.**
3. **Resolve artifact scope.** State explicitly whether the Isabelle directory is part of the submission or out of scope. **Resolved in the accompanying revision.**
4. **Tighten citations.** Add page/theorem pointers for Nagata/Samuel/Matsumura/Kaplansky, and split the Stacks citation if it is meant to support two different results.
5. **Clean up the paper as a document.** Shorten the lessons section, remove repeated novelty claims, and eliminate the LaTeX overfull/underfull box warnings. The accompanying revision resolves the box warnings and trims some of the repeated novelty language.

## Bottom line

For the pre-fix draft, the strongest attack was **not** "the theorem is wrong."
It was: **the paper was not reliably synchronized with the artifact it
described**. The accompanying revision addresses most of that synchronization
drift. What remains is mainly citation-tightening and low-severity
presentation/discoverability cleanup, not evidence of fake mathematics or a
broken formal artifact.
