"""Confirmatory analysis exactly as preregistered: exclusions, B - A, one-sided permutation test (10000, seed 1)."""
import csv, json, random

everyone = list(csv.DictReader(open("data/responses-anon.csv")))
rows = [r for r in everyone if r["attention_ok"] == "yes"]
a = [float(r["score"]) for r in rows if r["condition"] == "A"]
b = [float(r["score"]) for r in rows if r["condition"] == "B"]
mean = lambda x: sum(x) / len(x)
diff = mean(b) - mean(a)
rng, pooled, hits = random.Random(1), a + b, 0
for _ in range(10000):
    rng.shuffle(pooled)
    hits += mean(pooled[len(a):]) - mean(pooled[:len(a)]) >= diff
json.dump({"n_A": len(a), "n_B": len(b), "mean_A": round(mean(a), 3), "mean_B": round(mean(b), 3),
           "difference": round(diff, 3), "p_one_sided": round((hits + 1) / 10001, 4), "excluded": len(everyone) - len(rows)},
          open("results/h1.json", "w"), indent=1)
