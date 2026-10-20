import { mkdtempSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";

// Windows file symlinks need Developer Mode or a privilege. Junctions need neither.
export const FILE_SYMLINKS = (() => {
  const dir = mkdtempSync(path.join(tmpdir(), "tc-symlink-probe-"));
  try {
    writeFileSync(path.join(dir, "target"), "fixture");
    symlinkSync(path.join(dir, "target"), path.join(dir, "link"), "file");
    return true;
  } catch (error) {
    if (process.platform === "win32" && ["EPERM", "EACCES"].includes((error as NodeJS.ErrnoException).code ?? "")) return false;
    throw error;
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
})();
export const DIRECTORY_LINK = process.platform === "win32" ? "junction" : "dir";
