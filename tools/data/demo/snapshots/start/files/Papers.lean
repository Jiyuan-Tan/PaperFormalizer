module

/-!
# Papers

Barrel of the per-paper Lean output. Each verified paper owns one module tree
`Papers.<Slug>.*`, written by PaperFormalizer's F stages. A paper module may import `Toolkit.*` and
the base libraries; nothing imports a paper module except its own run. Admitted reusable pieces
are moved out into `Toolkit` and re-imported here.
-/

public section
