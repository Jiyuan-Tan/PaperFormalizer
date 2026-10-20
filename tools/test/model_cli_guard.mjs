// Inherited by Node children too: a test must provide a fake instead of using an account.
import childProcess from "node:child_process";
import path from "node:path";
import { syncBuiltinESMExports } from "node:module";

const installed = Symbol.for("leansmith.test.model-cli-guard");
const modelToken = /(?:^|[\s"'&|/\\])(?:codex|claude)(?:\.(?:exe|cmd|bat))?(?=$|[\s"'&|])/i;
const shell = /^(?:cmd|bash|sh|powershell|pwsh)(?:\.exe)?$/i;
if (!globalThis[installed]) {
  globalThis[installed] = true;
  for (const method of ["spawn", "spawnSync", "execFile", "execFileSync", "exec", "execSync"]) {
    const original = childProcess[method];
    childProcess[method] = function (command, args, ...rest) {
      const name = path.basename(String(command)).replace(/\.(exe|cmd|bat)$/i, "");
      if (/^(codex|claude)$/i.test(name)) {
        const mock = name.toLowerCase() === "codex" && process.env.LEANSMITH_TEST_CODEX_MOCK;
        if (!mock) throw new Error(`Tests refuse to launch the model CLI: ${command}`);
        return original.call(this, process.execPath, [mock, ...(args ?? [])], ...rest);
      }
      const text = method === "exec" || method === "execSync" ? String(command)
        : shell.test(path.basename(String(command))) ? (args ?? []).join(" ") : "";
      if (modelToken.test(text)) {
        const options = rest.find((arg) => arg && typeof arg === "object") ?? {};
        const shim = options.env?.LEANSMITH_TEST_MODEL_SHIM;
        // Only the explicitly supplied test shim and its fixed version/help flags may use cmd.exe.
        const line = Array.isArray(args) ? String(args.at(-1)).replace(/["^]/g, "").trim() : "";
        const tail = shim && line.startsWith(shim + " ") ? line.slice(shim.length + 1) : "";
        if (!tail || !/^(?:--version|--help)(?: two words)?$/.test(tail)) {
          throw new Error(`Tests refuse to launch a model CLI through a shell: ${command}`);
        }
      }
      return original.call(this, command, args, ...rest);
    };
    if (method === "exec" || method === "execFile") {
      const guarded = childProcess[method];
      Object.defineProperty(guarded, Symbol.for("nodejs.util.promisify.custom"), {
        value: (...args) => {
          let child;
          const promise = new Promise((resolve, reject) => {
            child = guarded(...args, (error, stdout, stderr) => {
              if (error) reject(Object.assign(error, { stdout, stderr }));
              else resolve({ stdout, stderr });
            });
          });
          promise.child = child;
          return promise;
        },
      });
    }
  }
  syncBuiltinESMExports();
}
