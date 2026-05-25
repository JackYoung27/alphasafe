import math
import unittest

from alpha_safe import alpha_safe


class AlphaSafeTest(unittest.TestCase):
    def assert_certified(self, L: float, Q: float, C: float,
                         epsilon: float) -> float:
        radius = alpha_safe(L, Q, C, epsilon)
        self.assertIsNotNone(radius)
        assert radius is not None
        envelope = radius * (abs(Q) / 2 + radius * abs(C) / 6)
        self.assertLessEqual(envelope, epsilon * abs(L))
        return radius

    def test_paper_example(self) -> None:
        radius = self.assert_certified(0.01748, 0.0389, 0.0139, 0.5)
        self.assertAlmostEqual(radius, 0.4276, places=4)

    def test_small_nonzero_cubic_term_is_not_discarded(self) -> None:
        self.assert_certified(1.0, 2e-15, 1e-16, 0.5)

    def test_cancellation_resistant_root(self) -> None:
        self.assert_certified(
            1.2592348820397273e-09,
            0.5353747835303845,
            7.134794128754058e-05,
            0.5,
        )

    def test_degenerate_cases(self) -> None:
        self.assertEqual(alpha_safe(0.0, 1.0, 1.0), 0.0)
        self.assertEqual(alpha_safe(1.0, 2.0, 0.0, 0.5), 0.5)
        self.assertIsNone(alpha_safe(1.0, 0.0, 0.0))

    def test_invalid_inputs(self) -> None:
        with self.assertRaises(ValueError):
            alpha_safe(1.0, 1.0, 1.0, -0.1)
        with self.assertRaises(ValueError):
            alpha_safe(math.nan, 1.0, 1.0)


if __name__ == "__main__":
    unittest.main()
