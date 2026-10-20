declare module "katex" {
  interface KatexOptions {
    displayMode?: boolean;
    throwOnError?: boolean;
    strict?: boolean | string;
    trust?: boolean;
    output?: "html" | "mathml" | "htmlAndMathml";
    macros?: Record<string, string>;
  }
  const katex: { renderToString(tex: string, options?: KatexOptions): string };
  export default katex;
}
