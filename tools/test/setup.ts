import "./model_cli_guard.mjs";

const guard = new URL("./model_cli_guard.mjs", import.meta.url).href;
const preload = `--import=${guard}`;
if (!process.env.NODE_OPTIONS?.includes(preload)) {
  process.env.NODE_OPTIONS = [process.env.NODE_OPTIONS, preload].filter(Boolean).join(" ");
}
