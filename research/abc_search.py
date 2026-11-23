"""Heuristic circuit search. A result is not an exhaustive certificate."""
import random
import subprocess
from pathlib import Path


def check(path):
    gates = []
    for line in path.read_text().splitlines():
        if line.startswith('.gate'):
            fields = line.split()
            gates.append((fields[1], dict(f.split('=') for f in fields[2:])))
    if not gates:
        raise ValueError('No mapped circuit was returned')
    size = sum(op not in ('buf', 'zero') for op, _ in gates)
    for row in range(64):
        values = {name: bool(row >> i & 1) for i, name in enumerate('abcdef')}
        pending = list(gates)
        while pending:
            ready = [(op, pins) for op, pins in pending
                     if all(net in values for pin, net in pins.items() if pin != 'Y')]
            if not ready:
                raise ValueError('Unexpected cyclic or undefined mapped wire')
            for op, pins in ready:
                a, b = values.get(pins.get('A')), values.get(pins.get('B'))
                result = {'zero': lambda: False, 'one': lambda: True,
                          'buf': lambda: a, 'inv': lambda: not a,
                          'and2': lambda: a and b, 'or2': lambda: a or b}[op]()
                values[pins['Y']] = result
                pending.remove((op, pins))
        x = [values[v] for v in 'abcdef']
        expected = [any(x[i] and x[3 + (i + k) % 3] for i in range(3)) for k in range(3)]
        assert [values[f'y{k}'] for k in range(3)] == expected, (path, row)
    return size


rng = random.Random(652)
commands = ['balance', 'rewrite', 'rewrite -z', 'refactor', 'refactor -z',
            'resub -K 6', 'resub -K 8', 'resub -K 8 -N 2', 'resub -K 12 -N 2']
best = 100
Path('results').mkdir(exist_ok=True)
for attempt in range(100):
    sequence = '; '.join(rng.choices(commands, k=6 + attempt % 10))
    output = Path(f'results/candidate_{attempt}.blif')
    script = (f'read_library research/and_or_not.genlib; read_blif research/matching.blif; '
              f'strash; {sequence}; map -a; print_stats; write_blif {output}')
    result = subprocess.run(['yosys-abc', '-c', script], capture_output=True, text=True, timeout=30)
    if result.returncode or not output.exists():
        print(result.stdout, result.stderr, flush=True)
        raise RuntimeError('ABC mapping failed')
    size = check(output)
    if size < best:
        best = size
        print({'attempt': attempt, 'best_gates': best, 'checked_inputs': 64,
               'commands': sequence, 'file': str(output)}, flush=True)
    if size <= 14:
        print('Candidate found; Lean verification is still required.', flush=True)
        break
print({'best_gates': best, 'exhaustive': False}, flush=True)
