"""Fit g from pendulum periods: T - latency = 2 pi sqrt(L / g), least squares in T^2 = (4 pi^2 / g) L."""
import json, math

latency = json.load(open("data/calibration.json"))["stopwatch_latency_s"]
rows = [tuple(map(float, l.split(","))) for l in open("data/raw.csv").read().split("\n")[1:] if l]
xs = [L for L, _ in rows]
ys = [(T - latency) ** 2 for _, T in rows]
n, sx, sy = len(xs), sum(xs), sum(ys)
sxx, sxy = sum(x * x for x in xs), sum(x * y for x, y in zip(xs, ys))
slope = (n * sxy - sx * sy) / (n * sxx - sx * sx)
icept = (sy - slope * sx) / n
res = [y - (slope * x + icept) for x, y in zip(xs, ys)]
se_slope = math.sqrt(sum(r * r for r in res) / (n - 2) / (sxx - sx * sx / n))
g = 4 * math.pi ** 2 / slope
json.dump({"g": round(g, 4), "g_err": round(g * se_slope / slope, 4), "n": n}, open("results/g.json", "w"), indent=1)
