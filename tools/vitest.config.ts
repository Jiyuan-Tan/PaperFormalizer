import { defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    include: ["test/**/*.test.ts", "test/**/*.spec.ts"],
    exclude: ["node_modules/**"],
    setupFiles: ["./test/setup.ts"],
    // A render may perform several bounded TeX compilations. Windows startup/antivirus overhead
    // needs room for their combined time; one worker also avoids a burst of native compilers.
    testTimeout: process.platform === "win32" ? 120_000 : 30_000,
    ...(process.platform === "win32" ? { maxWorkers: 1, minWorkers: 1 } : {}),
    // The suite runs the claude roles on their default runner whatever this machine has: no test
    // asks the real `claude` CLI whether it is installed and logged in (`src/claude_roles.ts`).
    env: { LEANSMITH_CLAUDE_ROLES: "claude" },
  },
});
