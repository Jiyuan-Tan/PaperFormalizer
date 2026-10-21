# Corrected paper — demo

NOT ready to submit: 1 blocking item(s) — see `corrected_paper/TODO.md`.

- `corrected_paper/` — the paper as it reads after the corrections: the author's own source (class, preamble, bibliography, figures, file layout), with each corrected statement, proof step and proof written in place of the printed one. Main file `corrected_paper/main.tex`; compiled: `corrected_paper/main.pdf` (2 pages). A reading the statements rely on appears as a remark of the paper at the statement it concerns.
- `corrected_paper/TODO.md` — what remains before submitting, each item with its file and line.
- `REPORT.md` — what was wrong, what was done about it, and what was proved in Lean.
- `MATCH.md` — each result beside its Lean declaration, phrase by phrase.
- `page/page.json` — the paper's page as PaperFormalizer's reader draws it (the statements as corrected, the notes, each result's verdict and its Lean), as data.

What is checked is the paper's results: each corrected statement and proof, and every result that depends on one. The prose around them is the authors', as printed.
