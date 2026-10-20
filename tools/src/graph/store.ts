import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import { randomUUID } from "node:crypto";
import path from "node:path";
import { GraphSchema, type FormalizationGraph } from "./types.js";

/** The run's formalization graph: `<run>/graph.json`. */
export function graphPath(formalizationDir: string): string {
  return path.join(formalizationDir, "graph.json");
}

export function createEmptyGraph(qid: string): FormalizationGraph {
  return { qid, nodes: [], edges: [] };
}

export async function loadGraph(p: string): Promise<FormalizationGraph> {
  return GraphSchema.parse(JSON.parse(await readFile(p, "utf8")));
}

/** Atomic write: validate, write to a temp sibling, rename into place. */
export async function saveGraph(p: string, graph: FormalizationGraph): Promise<void> {
  const checked = GraphSchema.parse(graph);
  await mkdir(path.dirname(p), { recursive: true });
  const tmp = `${p}.${process.pid}.${randomUUID()}.tmp`; // why: parallel saves must not race one fixed tmp path.
  await writeFile(tmp, JSON.stringify(checked, null, 2) + "\n", "utf8");
  await rename(tmp, p);
}
