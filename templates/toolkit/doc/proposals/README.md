Two checklists per verified paper: `<slug>.A.md`, the results the paper cites without proving,
proposed after its Lean plan (an accepted one is built and proved in this toolkit, and the paper
uses it instead of assuming it), and `<slug>.B.md`, the results the paper proved, proposed after
its report (an accepted one moves in, or its general form is built and the paper's result becomes
its corollary). Each entry is one main result written for a reader who does not read Lean (title,
reference, the statement in words, the evidence), with its Lean details below. Edit the `decision:`
line of each entry, then run `paperformalizer propose <slug> --round <A|B> --apply`: accepted
results enter the toolkit through its gate, every decision is recorded in `../ledger.json`, and
the run continues. `garden-<stamp>.md` is a gardening checklist: suggestions for reorganising what
the toolkit already holds, decided by the orchestrating agent (an item that would retire or remove
a result is put to the owner).
