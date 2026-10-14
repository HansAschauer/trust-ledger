"""Tests Observation obs:kitchen against the fit: the stated time (14.4 min) and diffusivity (1.60e-7 m^2/s),
the diffusivity inside the range Buay et al. found (1.5e-7 to 1.8e-7), and a fit within the probe's accuracy."""
import json

r = json.load(open("results/fit.json"))
assert abs(r["t85_s"] / 60 - 14.4) < 0.05, r["t85_s"]
assert abs(r["alpha"] - 1.60e-7) < 0.005e-7, r["alpha"]
assert 1.5e-7 <= r["alpha"] <= 1.8e-7, r["alpha"]
assert r["rms_C"] < 1.0, r["rms_C"]
print("obs:kitchen holds:", r)
