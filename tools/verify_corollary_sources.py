"""Verify the small public corollary source selection; this never runs Lean."""
from pathlib import Path
import hashlib
import json


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def contained(root, relative):
    candidate = (root / relative).resolve()
    candidate.relative_to(root.resolve())
    return candidate


def verify(root):
    manifest = json.loads((root / 'corollary/SOURCE_MANIFEST.json').read_text(encoding='utf-8'))
    paths = set()
    for row in manifest['files'] + manifest.get('support_files', []):
        path = contained(root, row['path'])
        if row['path'] in paths:
            raise ValueError('Duplicate selected path: ' + row['path'])
        paths.add(row['path'])
        if not path.is_file() or digest(path) != row['sha256']:
            raise ValueError('Missing or changed selected file: ' + row['path'])
        if path.stat().st_size != row['bytes']:
            raise ValueError('File size mismatch: ' + row['path'])
    selected = {row['path'] for row in manifest['files']}
    actual = {p.relative_to(root).as_posix() for p in (root / 'corollary/src').rglob('*.lean')}
    actual.update(p.relative_to(root).as_posix() for p in (root / 'tools').glob('MathlibFloor38*.lean'))
    if actual != selected:
        raise ValueError('Lean file selection differs from the manifest')
    if len(selected) != 7:
        raise ValueError('Expected exactly five ordinary modules and two native helpers')
    return len(selected), len(paths) - len(selected)


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    ordinary_and_native, support = verify(root)
    print(f'PASS: {ordinary_and_native} exact Lean sources and {support} support files.')
    print('This is source integrity checking, not Lean compilation or a fresh proof audit.')
