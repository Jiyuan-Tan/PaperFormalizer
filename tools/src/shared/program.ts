import { accessSync, constants, statSync } from "node:fs";
import path from "node:path";
import { execaSync } from "execa";

/** Find a program on PATH, including Windows executable extensions and quoted directories. */
export function findExecutable(
  name: string,
  options: { env?: NodeJS.ProcessEnv; platform?: NodeJS.Platform; cwd?: string; nativeOnly?: boolean } = {},
): string | null {
  const { env = process.env, platform = process.platform, cwd = process.cwd(), nativeOnly = false } = options;
  const windows = platform === "win32";
  const paths = windows ? path.win32 : path.posix;
  const value = (key: string): string | undefined => env[windows ? Object.keys(env).find((k) => k.toUpperCase() === key) ?? key : key];
  const extensions = windows ? (value("PATHEXT") || ".COM;.EXE;.BAT;.CMD").split(";").filter(Boolean) : [""];
  const suffixes = windows && !extensions.some((ext) => name.toLowerCase().endsWith(ext.toLowerCase())) ? [...extensions, ""] : [""];
  const explicit = name.includes("/") || (windows && name.includes("\\"));
  const directories = explicit ? [""] : (value("PATH") ?? "").split(windows ? ";" : ":").filter(Boolean);
  for (const directory of directories) {
    for (const suffix of suffixes) {
      const candidate = paths.resolve(cwd, windows ? directory.replace(/^"(.*)"$/, "$1") : directory, name + suffix.toLowerCase());
      if (windows && nativeOnly && !/\.(exe|com)$/i.test(candidate)) continue;
      try {
        if (!statSync(candidate).isFile()) continue;
        if (!windows) accessSync(candidate, constants.X_OK);
        return candidate;
      } catch { /* try the next PATH entry */ }
    }
  }
  return null;
}

/** Version/login probes use the same Windows npm-shim handling as the async workers. */
export function probeProgram(bin: string, args: string[], env = process.env, cwd?: string) {
  const executable = process.platform === "win32" ? findExecutable(bin, { env, cwd }) : bin;
  const refused = (code: string, message: string) => ({ status: null, signal: null, error: Object.assign(new Error(message), { code }), stdout: "", stderr: "" });
  if (!executable) return refused("ENOENT", `program not found: ${bin}`);
  // Probes use fixed flags, never model text. A batch file parses arguments a second time:
  // reject shell syntax rather than relying on cmd.exe to preserve arbitrary input.
  if (/\.(cmd|bat)$/i.test(executable) && process.platform === "win32" && args.some((arg) => /[\r\n"%!^&|<>]/.test(arg))) {
    return refused("EINVAL", "shell syntax is not allowed in Windows batch probe arguments");
  }
  const r = execaSync(executable, args, { encoding: "utf8", timeout: 30_000, env, extendEnv: false, reject: false, ...(cwd ? { cwd } : {}) });
  return {
    status: r.exitCode ?? null,
    signal: r.signal ?? null,
    error: r.failed && (r.code !== undefined || r.timedOut || r.exitCode === undefined)
      ? Object.assign(new Error(r.shortMessage ?? `could not run ${bin}`), { code: r.code ?? (r.timedOut ? "ETIMEDOUT" : undefined) })
      : undefined,
    stdout: r.stdout,
    stderr: r.stderr,
  };
}
