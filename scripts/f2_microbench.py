#!/usr/bin/env python3
"""F2 – kernel cost model. For each (op, size): build a one-theorem export
containing `theorem check : Nat.<op> <a> <b> = <lit> := rfl`, measure it with
the official timer binary under icount (process-wide), and subtract the
parse-only baseline so what's left is roughly the judge-window cost."""
import json, os, re, subprocess, sys, shutil, statistics
from pathlib import Path

ROOT = Path('/home/gris96/.hermes/workspace/repos/SAIR/lean-kernel-challenge')
sys.path.insert(0, str(ROOT/'scripts'))
from measure import _load_judge, problem_dir, run, ICOUNT, TIMER

LEAN4EXPORT = ROOT.parent / 'repro/lean4export/.lake/build/bin/lean4export'
WORKROOT = ROOT / 'candidates' / 'F2-cost-model-probes'
WORKROOT.mkdir(parents=True, exist_ok=True)
OUT = ROOT / 'results/cost_model' / 'f2_kernel_costs.json'

judge = _load_judge()
pdir = problem_dir('partition')

def build_probe(a_expr, b_expr, op, expected_lit, probedir: Path):
    src = probedir / 'Probe.lean'
    src.write_text(f"""\
import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := {a_expr}
def big_1 : Nat := {b_expr}

theorem check : Nat.{op} big_0 big_1 = {expected_lit} := rfl
""")
    probe = pdir / 'F2Probe.lean'
    shutil.copy(src, probe)
    olean = pdir / '.lake/build/lib/lean/F2Probe.olean'
    if olean.exists(): olean.unlink()
    rc, out = run(['lake','env','lean','-o',str(olean), 'F2Probe.lean'], pdir)
    if rc != 0:
        probe.unlink(missing_ok=True)
        return None, f'build failed:\n{out[-800:]}'
    export = probedir / 'export.out'
    artifact_lib = pdir / '.lake' / 'build' / 'lib' / 'lean'
    pkg_libs = sorted(d for d in (pdir/'.lake'/'packages').glob('*/.lake/build/lib/lean') if d.is_dir())
    lean_path = os.pathsep.join([str(artifact_lib), *(str(d) for d in pkg_libs),
                                 str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean')])
    with export.open('wb') as fh:
        proc = subprocess.run([str(LEAN4EXPORT),'F2Probe','--','F2Probe.check'],
                              cwd=pdir, env={**os.environ,'LEAN_PATH':lean_path},
                              stdout=fh, stderr=subprocess.PIPE, text=True, timeout=600)
    probe.unlink(missing_ok=True)
    if proc.returncode != 0 or not export.exists() or export.stat().st_size == 0:
        return None, f'export failed:\n{(proc.stderr or "")[-800:]}'
    return export, None

def measure(export, theorem, reps=3):
    vals, parse_only = [], None
    for _ in range(reps):
        rc,out = run([str(ICOUNT), str(TIMER), '--target', theorem, str(export)], pdir)
        m = re.search(r'INSTR_TOTAL=(\d+)', out)
        if m: vals.append(int(m.group(1)))
    for _ in range(reps):
        rc,out = run([str(ICOUNT), str(TIMER), '--parse-only', str(export)], pdir)
        m = re.search(r'INSTR_TOTAL=(\d+)', out)
        if m:
            p = int(m.group(1))
            parse_only = p if parse_only is None else min(parse_only,p)
    return statistics.median(vals), vals, parse_only

results = {}
cases = []
for op, fn in [('add','add'), ('mul','mul'), ('div','div'), ('mod','mod'),
               ('gcd','gcd'), ('land','land'), ('lor','lor'), ('xor','xor'),
               ('shiftLeft','shiftLeft'), ('shiftRight','shiftRight'),
               ('pow','pow'), ('log2','log2'), ('beq','beq'), ('ble','ble'), ('testBit','testBit')]:
    for bits in (64, 1_000, 10_000, 100_000):
        cases.append((f'Nat.{op}', op, bits))

# For each op choose two operands with the target bit-width in a way that is
# meaningful (e.g. shift by a small constant, testBit at a large index, etc.)
def args(op, bits):
    if op == 'add': return ('(2^(bits-1))'.replace('bits',str(bits)),
                            '(2^(bits-1) - 1)'.replace('bits',str(bits)))
    if op == 'mul': return ('(2^(bits//2))'.replace('bits',str(bits)),
                            '(2^(bits//2) + 1)'.replace('bits',str(bits)))
    if op == 'div': return ('(2^(bits-1))'.replace('bits',str(bits)),
                            '(2^(bits//2) + 1)'.replace('bits',str(bits)))
    if op == 'mod': return ('(2^(bits-1) - 1)'.replace('bits',str(bits)),
                            '(2^(bits//2) + 1)'.replace('bits',str(bits)))
    if op == 'gcd': return ('(2^(bits-1) + 1)'.replace('bits',str(bits)),
                            '(2^(bits//2) + 1)'.replace('bits',str(bits)))
    if op in ('land','lor','xor','beq','ble'):
        return ('(2^(bits-1))'.replace('bits',str(bits)),
                '(2^(bits-1) + 1)'.replace('bits',str(bits)))
    if op == 'shiftLeft': return ('(2^(bits-1))'.replace('bits',str(bits)), '13')
    if op == 'shiftRight': return ('(2^bits - 1)'.replace('bits',str(bits)), '13')
    if op == 'pow':   return ('(2^10)', '13')  # small; pow scales with expo
    if op == 'log2':  return ('(2^bits - 1)'.replace('bits',str(bits)), '')
    if op == 'testBit': return ('(2^(bits-1))'.replace('bits',str(bits)),
                                '(bits//2)'.replace('bits',str(bits)))
    raise ValueError(op)

def expected(op, a_expr, b_expr):
    a = eval(a_expr.replace('^','**').replace('bits','bits'))
    if b_expr:
        b = eval(b_expr.replace('^','**'))
    if op=='add': return a+b
    if op=='mul': return a*b
    if op=='div': return a//b
    if op=='mod': return a%b
    if op=='gcd':
        import math; return math.gcd(a,b)
    if op=='land': return a & b
    if op=='lor':  return a | b
    if op=='xor':  return a ^ b
    if op=='shiftLeft': return a << b
    if op=='shiftRight': return a >> b
    if op=='pow': return a ** b
    if op=='log2': return a.bit_length()-1
    if op=='beq':  return 'true' if a==b else 'false'
    if op=='ble':  return 'true' if a<=b else 'false'
    if op=='testBit': return 'true' if (a>>b)&1 else 'false'

for label, op, bits in cases:
    a_expr, b_expr = args(op, bits)
    a_expr = a_expr.replace('bits', str(bits))
    b_expr = b_expr.replace('bits', str(bits)) if b_expr else b_expr
    expected_lit = str(expected(op, a_expr.replace('^','**'),
                                 b_expr.replace('^','**') if b_expr else b_expr))
    if op in ('log2',):
        # log2 has 1 arg in Lean
        probe_text = f"theorem check : Nat.log2 {a_expr} = {expected_lit} := rfl"
    elif op in ('beq','ble','testBit'):
        probe_text = f"theorem check : Nat.{op} {a_expr} {b_expr} = {expected_lit} := rfl"
    else:
        probe_text = f"theorem check : Nat.{op} {a_expr} {b_expr} = {expected_lit} := rfl"
    probedir = WORKROOT / f'{label.replace(".","_")}@{bits}'
    probedir.mkdir(exist_ok=True)
    src = probedir / 'Probe.lean'
    src.write_text(f"""\
import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := {a_expr}
{f'def big_1 : Nat := {b_expr}' if b_expr else ''}

{probe_text}
""")
    probe = pdir / 'F2Probe.lean'
    shutil.copy(src, probe)
    olean = pdir / '.lake/build/lib/lean/F2Probe.olean'
    if olean.exists(): olean.unlink()
    rc, out = run(['lake','env','lean','-o',str(olean), 'F2Probe.lean'], pdir)
    if rc != 0:
        results[f'{label}@{bits}'] = {'error': f'build: {out[-300:]}'}
        probe.unlink(missing_ok=True)
        continue
    export = probedir / 'export.out'
    artifact_lib = pdir / '.lake' / 'build' / 'lib' / 'lean'
    pkg_libs = sorted(d for d in (pdir/'.lake'/'packages').glob('*/.lake/build/lib/lean') if d.is_dir())
    lean_path = os.pathsep.join([str(artifact_lib), *(str(d) for d in pkg_libs),
                                 str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean')])
    with export.open('wb') as fh:
        proc = subprocess.run([str(LEAN4EXPORT),'F2Probe','--','F2Probe.check'],
                              cwd=pdir, env={**os.environ,'LEAN_PATH':lean_path},
                              stdout=fh, stderr=subprocess.PIPE, text=True, timeout=600)
    probe.unlink(missing_ok=True)
    if proc.returncode != 0 or not export.exists() or export.stat().st_size == 0:
        results[f'{label}@{bits}'] = {'error': f'export: {(proc.stderr or "")[-300:]}'}
        continue
    med, vals, parse_only = measure(export, 'F2Probe.check')
    work = med - (parse_only or 0)
    results[f'{label}@{bits}'] = {'total': med, 'parse_only': parse_only,
                                  'replay_minus_parse': work, 'raw': vals}
    print(f'{label}@{bits:>7}: total={med:>14,} parse={parse_only:>14,} work={work:>10,}', flush=True)

OUT.write_text(json.dumps(results, indent=1))
print('saved', OUT)
