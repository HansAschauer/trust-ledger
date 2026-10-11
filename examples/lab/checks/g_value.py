"""The paper states g = 9.80 +- 0.03 m/s^2. Check that the fit supports it: the stated value is within two
standard errors of the fitted one, and the stated uncertainty is not smaller than the fitted one."""
import json, sys

r = json.load(open("results/g.json"))
stated, stated_err = 9.80, 0.03
ok = abs(r["g"] - stated) <= 2 * r["g_err"] and r["g_err"] <= stated_err   # within 2 sigma, error not understated
print(f"fitted g = {r['g']} +- {r['g_err']} (n = {r['n']}); stated {stated} +- {stated_err}: {'consistent' if ok else 'NOT consistent'}")
sys.exit(0 if ok else 1)
