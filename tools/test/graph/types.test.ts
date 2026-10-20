import { describe, it, expect } from "vitest";
import { GraphSchema, type FormalizationGraph } from "../../src/graph/types.js";

const minimal: FormalizationGraph = {
  qid: "stat_demo",
  nodes: [
    {
      id: "t1",
      kind: "theorem",
      provenance: "from-note",
      nl: { statement: "the estimand is root-n estimable", tex_anchor: "tex:L10-20", frozen: true },
      lean: { decl_name: null, file: null },
      review: { status: "unreviewed", passed_hash: null },
      proof: { state: "sorry", sorry_count: 1 },
    },
  ],
  edges: [],
};

describe("GraphSchema", () => {
  it("accepts a minimal valid graph and rejects an unknown node kind", () => {
    expect(GraphSchema.parse(minimal)).toEqual(minimal);
    const bad = { ...minimal, nodes: [{ ...minimal.nodes[0], kind: "widget" }] };
    expect(() => GraphSchema.parse(bad)).toThrow();
    // the retired review status is no status: nothing coerces it
    expect(() => GraphSchema.parse({ ...minimal, nodes: [{ ...minimal.nodes[0], review: { status: "derived", passed_hash: null } }] })).toThrow();
  });

  it("loads a graph file carrying keys the schema no longer names", () => {
    const old = {
      ...minimal,
      nodes: [{
        ...minimal.nodes[0],
        nl: { ...minimal.nodes[0].nl, frozen_body: "x", frozen_title: null },
        lean: { ...minimal.nodes[0].lean, supporting_decls: ["Foo.bar"] },
      }],
    };
    expect(GraphSchema.parse(old)).toEqual(minimal);
  });

  it("allows undelivered only for secondary theorems or cited gates", () => {
    const secondary = {
      ...minimal,
      nodes: [{
        ...minimal.nodes[0],
        delivery: { status: "undelivered", role: "secondary", reason: "non-headline citation overflow" },
      }],
    };
    expect(GraphSchema.parse(secondary).nodes[0].delivery?.status).toBe("undelivered");
    const headline = {
      ...minimal,
      nodes: [{
        ...minimal.nodes[0],
        delivery: { status: "undelivered", role: "headline", reason: "too hard" },
      }],
    };
    expect(() => GraphSchema.parse(headline)).toThrow(/secondary theorem or a cited gate/);
  });

  it("rejects a delivered result that depends (directly or transitively) on an undelivered node", () => {
    const bad = {
      ...minimal,
      nodes: [
        minimal.nodes[0],
        {
          ...minimal.nodes[0], id: "t2",
          delivery: { status: "undelivered", role: "secondary", reason: "secondary overflow" },
        },
      ],
      edges: [{ kind: "proof-uses", from: "t1", to: "t2", source: "declared" }],
    };
    expect(() => GraphSchema.parse(bad)).toThrow(/depends on undelivered/);

    // …also through a two-hop dependency via a definition
    const twoHop = {
      ...minimal,
      nodes: [
        { ...minimal.nodes[0], delivery: { status: "deliver" as const, role: "headline" as const } },
        { ...minimal.nodes[0], id: "d1", kind: "definition" as const },
        { ...minimal.nodes[0], id: "t2", delivery: { status: "undelivered" as const, role: "secondary" as const, reason: "secondary overflow" } },
      ],
      edges: [
        { kind: "statement-uses" as const, from: "t1", to: "d1", source: "declared" as const },
        { kind: "proof-uses" as const, from: "d1", to: "t2", source: "declared" as const },
      ],
    };
    expect(() => GraphSchema.parse(twoHop)).toThrow(/transitively depends on undelivered/);
  });
});
