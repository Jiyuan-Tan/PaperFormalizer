# TheoremChecker annotations — demo

Annotated copy of `source/`; main file `main.tex`. Red (`\vsOriginal`, "Original:"): the paper's text that is wrong or ambiguous (kind `not determined`: it does not say enough to be checked, and nothing was shown false). Blue (`\vsCorrected` / `\vsClarified`: "Corrected:", "Clarified statement:"): the corrected text (a hypothesis a repair adds is written into it; the note says which). Proofs (kind `corrected proof`) are revised in place: each printed step a repair changes red (`\vsStep`, "Original:") with its replacement right after (`\vsCorrectedStep`, "Corrected:"); a repair without step edits (or a result whose proof was not located) gets one block per result (`\vsProof`, "Corrected proof (confirmed):"; a pending one `\vsProposedProof`) after the proof; when the paper prints none, right after the result, naming every lemma it uses and, by the paper's section numbers, where their corrections are marked; else right after the result, saying the proof could not be located. Red struck through (`\vsStruck`; `\vsStruckRed`, red alone, where a line cannot cross the text), kind `no longer used`: an assumption or definition no result uses after the repairs, with a note naming the results that now state the conditions they use. Orange (`\vsNote`, "TheoremChecker: …"): what is wrong, the proposed fix, and whether the fix weakens the result; `\vsReading` ("Clarification:", kind `clarification (reading)`): a reading pinned for formalization; `\vsReadingOwner` ("Clarification (author):"): the owner's reading of a finding the owner withdrew; `\vsReadingSymbol` ("Clarification (symbol …):"): the reading of a symbol; `\vsCondition` ("Bookkeeping condition:", kind `condition added`; the owner's `\vsConditionOwner`, "Bookkeeping condition:"): a condition the verified statement carries beyond the printed text, at the end of each result carrying it. Awaiting your decision (a halt only): `\vsProposed` (blue, "Proposed repair (awaiting your decision):"), `\vsProposedStep` / `\vsProposedProof` (blue, "Corrected (for the proposed statement):", "Proof of the proposed statement:" — the decision is on the statement, never on its proof), `\vsRewind` ("Proposed correction (awaiting your decision):"), `\vsCap` ("Repair not settled (awaiting your decision):"). Lines are the ORIGINAL source's.

**Awaiting your decision: 1 item(s)** (kind `awaiting decision` below).

Preamble: `\usepackage{xcolor}` added after `\documentclass`; colour macros defined before `\begin{document}`.

## Annotations (2)

| # | node | file:line | kind | located by | note |
|---|---|---|---|---|---|
| 1 | `thm:amgm` | main.tex:40 | awaiting decision | units | weakened repair proposed; gives up: The inequality is no longer claimed when $a$ or $b$ is negative. |
| 2 | `thm:amgm` | main.tex:50 | awaiting decision | after-proof | proposed proof of thm:amgm |

## Unlocated (0)

Every finding was placed at its passage.

## Compile

Compiled with pdflatex: `main.pdf`.
