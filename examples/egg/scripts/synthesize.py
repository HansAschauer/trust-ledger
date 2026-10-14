"""Makes data/probe.csv. The kitchen of this example is fictitious: the probe readings are the model of
scripts/egg.py (alpha = 1.6e-7 m^2/s, the value Buay et al. fitted) plus Gaussian noise, with a fixed seed."""
import json, random
from egg import centre, equivalent_radius

egg = json.load(open("data/egg.json"))
R = equivalent_radius(egg["a_mm"] / 1000, egg["b_mm"] / 1000)
rng = random.Random(1)
with open("data/probe.csv", "w") as f:
    f.write("t_s,centre_C\n")
    for t in range(0, 961, 30):
        f.write(f"{t},{centre(t, R, 1.6e-7, egg['bath_C'], egg['start_C']) + rng.gauss(0, 0.4):.1f}\n")
