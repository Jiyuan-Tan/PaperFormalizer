// The order of the symbol table.
//
// A symbol's `refs` name the symbols its `def` is written with. The table is kept with each symbol
// after those it refers to — the order every reader of the table meets it in — and that order is the
// runner's to give, not the transcriber's: a paper describes symbols through each other (a constant
// of a function, the function by its constant), so `refs` may form a cycle, which no order satisfies
// and no reader of `refs` needs broken (each closes over `refs` with a visited set).

interface Ordered {
  name: string;
  refs?: string[];
}

/** For each symbol of the table, the symbols of the table its `refs` lead to, transitively (itself
 * among them exactly when a cycle of `refs` returns to it). */
export function symbolRefsReach(symbols: readonly Ordered[]): Map<string, Set<string>> {
  const refsOf = new Map(symbols.map((s) => [s.name, (s.refs ?? []).filter((r) => r !== s.name)] as const));
  const reach = new Map<string, Set<string>>();
  for (const s of symbols) {
    const seen = new Set<string>();
    const todo = [...refsOf.get(s.name)!];
    while (todo.length > 0) {
      const r = todo.pop()!;
      if (seen.has(r) || !refsOf.has(r)) continue;
      seen.add(r);
      todo.push(...refsOf.get(r)!);
    }
    reach.set(s.name, seen);
  }
  return reach;
}

/**
 * The table with every symbol after the symbols its `refs` name, moving as little as that takes: a
 * symbol stays where the transcriber put it unless one it refers to comes later, which is then
 * brought up before it. Symbols that refer to each other in a cycle have no such order: they are
 * kept together, in the transcriber's order, after everything the cycle refers to. Deterministic,
 * and the identity on a table already in order (so a second pass moves nothing). A ref that names
 * no symbol of the table, or the symbol itself, orders nothing.
 */
export function orderSymbolsByRefs<T extends Ordered>(symbols: readonly T[]): T[] {
  const reach = symbolRefsReach(symbols);
  const out: T[] = [];
  const placed = new Set<string>();
  const place = (s: T): void => {
    if (placed.has(s.name)) return;
    const mine = reach.get(s.name)!;
    const cycle = symbols.filter((t) => t.name === s.name || (mine.has(t.name) && reach.get(t.name)!.has(s.name)));
    for (const t of cycle) placed.add(t.name);
    // What the cycle refers to lies outside it and never leads back: the recursion ends.
    const named = new Set(cycle.flatMap((t) => t.refs ?? []));
    for (const t of symbols) if (named.has(t.name)) place(t);
    out.push(...cycle);
  };
  for (const s of symbols) place(s);
  return out;
}
