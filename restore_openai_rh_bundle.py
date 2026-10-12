#!/usr/bin/env python3
"""Restore an Aristotle source bundle without flattening paths or overwriting conflicts."""
import argparse, base64, hashlib, json, pathlib, signal

def main():
    signal.alarm(180)
    p = argparse.ArgumentParser()
    p.add_argument('bundle', type=pathlib.Path)
    p.add_argument('--output', type=pathlib.Path, required=True)
    a = p.parse_args()
    bundle = json.loads(a.bundle.read_text(encoding='utf-8'))
    if bundle.get('format') != 'aristotle-source-bundle-v1':
        raise SystemExit('Unsupported bundle format')
    root = a.output.resolve()
    pending = []
    seen = set()
    for item in bundle['files']:
        path = pathlib.PurePosixPath(item['path'])
        if path.is_absolute() or '..' in path.parts or str(path) in seen:
            raise SystemExit('Unsafe or duplicate path: ' + str(path))
        seen.add(str(path))
        target = (root / path).resolve()
        if not target.is_relative_to(root):
            raise SystemExit('Path escapes output directory: ' + str(path))
        encoding = item['encoding']
        if encoding == 'utf8':
            data = item['content'].encode('utf-8')
        elif encoding == 'base64':
            data = base64.b64decode(item['content'], validate=True)
        else:
            raise SystemExit('Unknown file encoding')
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise SystemExit('Hash mismatch: ' + str(path))
        if target.exists() and (not target.is_file() or target.read_bytes() != data):
            raise SystemExit('Conflicting existing file: ' + str(target))
        pending.append((target, data))
    for target, data in pending:
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            target.write_bytes(data)
    print(f'Restored and SHA-256 verified {len(pending)} files in {root}')

if __name__ == '__main__':
    main()
