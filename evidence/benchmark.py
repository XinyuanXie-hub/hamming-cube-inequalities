import json, os, pathlib, subprocess, time

root = pathlib.Path('/workspace/hamming-optimization-evidence')
runs = []
for name, project in [('candidate', '/workspace/hamming-cube-optimization'), ('baseline', '/workspace/hamming-cube-review')]:
    env = os.environ.copy()
    env['PATH'] = '/workspace/.local/lean/lean-4.35.0-linux/bin:' + env['PATH']
    env['MATHLIB_CACHE_DIR'] = project + '/.mathlib-cache'
    start = time.perf_counter()
    with (root / (name + '-comparator.log')).open('w') as log:
        result = subprocess.run(['bash', 'scripts/verify-comparator.sh'], cwd=project, env=env, stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.perf_counter() - start
    text = (root / (name + '-comparator.log')).read_text()
    passed = result.returncode == 0 and 'Your solution is okay!' in text
    record = dict(name=name, project=project, seconds=elapsed, exit_code=result.returncode, passed=passed)
    runs.append(record)
    (root / 'matched-runs.json').write_text(json.dumps(runs, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    if not passed:
        raise SystemExit(result.returncode or 1)
