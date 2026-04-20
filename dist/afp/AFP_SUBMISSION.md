# AFP Submission Pack

## Status

- Isabelle session builds successfully with PDF documents.
- Submission bundle has been prepared from `isabelle/Nagata-Factoriality/`.
- Main proof document is available at `dist/afp/Nagata-Factoriality-document.pdf`.
- Outline document is available at `dist/afp/Nagata-Factoriality-outline.pdf`.

## Submission Metadata

- Title: `Nagata Factoriality`
- Authors:
  - Arthur Freitas Ramos
  - David Barros Hulak
  - Ruy J. G. B. de Queiroz
- Maintainer: `Arthur Freitas Ramos`
- Maintainer email: `arfreita@microsoft.com`
- Chosen AFP license: `BSD License`
- Suggested topic: `Mathematics/Algebra`
- AFP dependency: `Localization_Ring`

## Web Abstract

The ready-to-paste abstract is in `dist/afp/afp-web-abstract.txt`.

## Submission Bundle

- Clean directory copy:
  - `dist/afp/submission/Nagata-Factoriality/`
- Zip archive:
  - `dist/afp/Nagata-Factoriality-afp-submission.zip`
- Tarball:
  - `dist/afp/Nagata-Factoriality-afp-submission.tar.gz`

## Build Command Used

```powershell
$env:Path = 'C:\Tools\TinyTeX\bin\windows;C:\Tools\bin;' + $env:Path
isabelle build -v -d C:\src\isabelle-borel-determinacy\vendor\afp-2026-04-09\thys -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -D C:\src\NagataFactoriality\isabelle\Nagata-Factoriality Nagata-Factoriality
```

## Checks Completed

- `ROOT`, `document/root.tex`, and `document/root.bib` are present.
- No obvious `sorry`, `back`, `sledgehammer`, `smt_oracle`, `nitpick`, `quickcheck`, or `nunchaku` commands were found in the submitted Isabelle entry sources.
- PDF document build completed successfully.
- Bibliography entries were normalized and cited in the generated document.

## License Note

- The repository root license is currently Apache 2.0.
- For the AFP submission, the selected license is `BSD License`, which is the permissive option among AFP's accepted licenses.
- This does not by itself change the root repository license. It records the intended AFP submission choice.

## Practical Submission Checklist

1. Confirm that all three listed authors consent to the AFP submission.
2. Select `BSD License` in the AFP submission form.
3. Upload the prepared archive from `dist/afp/`.
4. Paste the abstract from `dist/afp/afp-web-abstract.txt`.
5. Enter the author list and maintainer email exactly as above.
