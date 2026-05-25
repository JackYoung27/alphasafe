# alphasafe

Closed-form safe radius for the cubic Taylor model of activation-space
steering edits.

For finite Taylor coefficients $L$, $Q$, and $C$, and tolerance
$\varepsilon \geq 0$, the nonzero-cubic case is:

$$\alpha_{\text{safe}} = \frac{-3|Q| + \sqrt{9Q^2 + 24\varepsilon|L||C|}}{2|C|}$$

For $0 \leq \alpha \leq \alpha_{\text{safe}}$, the quadratic-plus-cubic
term obeys:

$$\left|\frac{\alpha^2 Q}{2} + \frac{\alpha^3 C}{6}\right| \leq \varepsilon \cdot |\alpha L|$$

This is a bound for the Taylor-3 model. Applying it to a full loss requires
a separate bound on fourth- and higher-order remainder terms.

## Files

- `alpha_safe.py` - numerically stable, dependency-free Python implementation,
  including the zero-quadratic and zero-cubic cases.
- `test_alpha_safe.py` - regression tests for the numerical implementation.
- `AlphaSafe.lean` - exact-real proof for nonzero $C$, checked with Lean 4 and
  Mathlib.

## Verify

```sh
python3 -m unittest -v
lake build
```
