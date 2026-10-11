"""The paper reports: difference of means 1.19 points, n = 27 + 27 after excluding 4 participants who failed the
attention check, one-sided permutation test p < .001. Check these numbers against the confirmatory analysis."""
import json, sys

r = json.load(open("results/h1.json"))
ok = (abs(r["difference"] - 1.19) < 0.005 and (r["n_A"], r["n_B"], r["excluded"]) == (27, 27, 4)
      and r["p_one_sided"] < 0.001)
print(f"difference {r['difference']}, n = {r['n_A']} + {r['n_B']}, excluded {r['excluded']}, p = {r['p_one_sided']}: "
      + ("as reported" if ok else "NOT as reported"))
sys.exit(0 if ok else 1)
