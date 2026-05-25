"""Closed-form safe radius for a cubic Taylor model.

Given three Taylor coefficients of the loss along a steering direction
(L, Q, C) and a tolerance eps, returns a nonnegative push radius at which
the quadratic-plus-cubic term is bounded by eps times the linear term.

The proof of the underlying inequality is in AlphaSafe.lean.
"""
from __future__ import annotations

import math


def alpha_safe(L: float, Q: float, C: float, epsilon: float = 0.5,
               ) -> float | None:
    """Compute a certified radius from finite ``(L, Q, C, epsilon)``.

    Returns ``None`` when both nonlinear coefficients are zero, since no
    finite upper bound is needed. ``epsilon`` must be nonnegative.
    """
    if not all(math.isfinite(x) for x in (L, Q, C, epsilon)):
        raise ValueError("L, Q, C, and epsilon must be finite")
    if epsilon < 0:
        raise ValueError("epsilon must be nonnegative")

    aL, aQ, aC = abs(L), abs(Q), abs(C)
    if aQ == 0 and aC == 0:
        return None

    budget = epsilon * aL
    if not math.isfinite(budget):
        raise OverflowError("epsilon * abs(L) is not representable")
    if budget == 0:
        return 0.0
    if aC == 0:
        radius = 2 * (budget / aQ)
    else:
        cross = math.sqrt(24.0) * math.sqrt(budget) * math.sqrt(aC)
        denominator = 3 * aQ + math.hypot(3 * aQ, cross)
        radius = 12 * budget / denominator

    if not math.isfinite(radius):
        raise OverflowError("the safe radius is not representable")

    # Round toward safety if evaluation lands just above the conservative
    # floating-point bound. Fail loudly for an unexpectedly unstable result.
    for _ in range(8):
        if radius * (aQ / 2 + radius * aC / 6) <= budget:
            return radius
        radius = math.nextafter(radius, 0.0)
    raise ArithmeticError("could not certify the radius in floating point")


if __name__ == "__main__":
    # one direction from the paper (Pythia-1.4B L12, SAE, text 41).
    # at eps=0.5 the formula gives ~0.428; the measured safe push on the
    # same direction sits between 0.5 and 0.75.
    L, Q, C, eps = 0.01748, 0.0389, 0.0139, 0.5
    print(f"alpha_safe({L}, {Q}, {C}, eps={eps}) = "
          f"{alpha_safe(L, Q, C, eps):.4f}")
