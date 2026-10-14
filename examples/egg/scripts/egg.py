"""The physics shared by the scripts: the centre temperature of a sphere in a bath (Buay et al. 2006, eq. (5)),
and the radius of the sphere equivalent to a prolate egg (their eq. (22))."""
import math


def centre(t, R, alpha, Tb, T0, terms=200):
    """Centre temperature at time t (s) of a sphere of radius R (m), diffusivity alpha (m^2/s)."""
    if t <= 0:
        return T0  # the series does not converge at t = 0
    lam = math.pi ** 2 * alpha / R ** 2
    s = sum((-1) ** (n + 1) * math.exp(-n * n * lam * t) for n in range(1, terms + 1))
    return Tb - 2 * (Tb - T0) * s


def equivalent_radius(a, b):
    """Semi-axes a > b (m) of a prolate spheroid -> radius with the same surface/volume ratio."""
    e = math.sqrt(1 - b * b / (a * a))
    beta = math.asin(e) / e
    return 2 * a * b / (b + beta * a)
