// The env var through which a launcher hands its shared lean-lsp HTTP server to every worker
// it spawns (`startSharedLeanLsp` → the URL → `leanLspCodexFlags` / the claude MCP config).
export const SHARED_LEAN_LSP_URL_ENV = "THEOREMCHECKER_SHARED_LEAN_LSP_URL";

/** The shared server URL a launcher exported, if any. */
export function sharedLeanLspUrl(env: NodeJS.ProcessEnv = process.env): string | undefined {
  return env[SHARED_LEAN_LSP_URL_ENV]?.trim() || undefined;
}

export function setSharedLeanLspUrl(url: string): void {
  process.env[SHARED_LEAN_LSP_URL_ENV] = url;
}

export function clearSharedLeanLspUrl(): void {
  delete process.env[SHARED_LEAN_LSP_URL_ENV];
}
