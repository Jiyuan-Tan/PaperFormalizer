#!/usr/bin/env python3
"""Idempotent module headers; distinguish real imports from docstring examples."""
from pathlib import Path
import re
import sys
from scan_names import uncomment

root = Path(sys.argv[1])
files = [root / 'StatLean.lean', *sorted((root / 'StatLean').rglob('*.lean'))]
changed = imports_changed = 0
for path in files:
    text = path.read_bytes().decode()
    code = uncomment(text)
    if re.search(r'^module[ \t]*$', code, re.M):
        continue
    imports = [i for i, line in enumerate(code.splitlines()) if re.match(r'^import\b', line)]
    if not imports:
        raise ValueError(f'No import header: {path}')
    lines = text.splitlines(keepends=True)
    for i in imports:
        lines[i] = lines[i].replace('import', 'public import', 1)
    end = imports[-1] + 1
    header = ''.join(lines[:end])
    if not header.endswith('\n'):
        header += '\n'
    path.write_bytes(('module\n' + header + '\n@[expose] public section\n' + ''.join(lines[end:])).encode())
    changed += 1
    imports_changed += len(imports)
print(f'Converted {changed} files ({len(files)} total), {imports_changed} actual imports.')
