"""Fit the thermal diffusivity of the egg to the probe readings (least squares over a grid), and read off
when the centre reached 85 C (linear interpolation between readings)."""
import json, math
from egg import centre, equivalent_radius

egg = json.load(open("data/egg.json"))
R = equivalent_radius(egg["a_mm"] / 1000, egg["b_mm"] / 1000)
Tb, T0 = egg["bath_C"], egg["start_C"]
rows = [tuple(map(float, l.split(","))) for l in open("data/probe.csv").read().split("\n")[1:] if l]


def sse(alpha):
    return sum((c - centre(t, R, alpha, Tb, T0)) ** 2 for t, c in rows)


alpha = min((a / 1000 * 1e-7 for a in range(1000, 2501)), key=sse)
done = next(t0 + (85 - c0) / (c1 - c0) * (t1 - t0)
            for (t0, c0), (t1, c1) in zip(rows, rows[1:]) if c0 < 85 <= c1)
first_order = R ** 2 / (math.pi ** 2 * alpha) * math.log(2 * (Tb - T0) / (Tb - 85))
json.dump({"R_mm": round(R * 1000, 2), "alpha": round(alpha, 10), "t85_s": round(done), "t85_first_order_s": round(first_order),
           "rms_C": round(math.sqrt(sse(alpha) / len(rows)), 2)}, open("results/fit.json", "w"), indent=1)
