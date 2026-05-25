/-
  Closed-form trust-region radius for activation-space edits.

  This file proves an algebraic inequality over the reals: for every alpha in
  [0, alpha_safe(L, Q, C, ε)], the absolute value of the quadratic-plus-cubic
  term is at most ε times the absolute value of the linear term.

  Status: machine-verified, no `sorry`. Requires Mathlib4.

  Lean handle: `AlphaSafe.nonlin_share_le_eps_on_alphaSafe`.
-/

import Mathlib

namespace AlphaSafe

/-- Closed-form radius: positive root of `|C|·α² + 3|Q|·α = 6ε|L|`. -/
noncomputable def alphaSafe (L Q C ε : ℝ) : ℝ :=
  (-3 * |Q| + Real.sqrt (9 * Q ^ 2 + 24 * ε * |L| * |C|)) / (2 * |C|)

/-- Key identity: `α_safe` satisfies the defining quadratic
    `|C|·α² + 3|Q|·α = 6ε|L|`, when `ε ≥ 0` and `C ≠ 0`. -/
lemma alphaSafe_quadratic_id
    {L Q C ε : ℝ} (hC : C ≠ 0) (hε : 0 ≤ ε) :
    |C| * (alphaSafe L Q C ε) ^ 2 + 3 * |Q| * alphaSafe L Q C ε
      = 6 * ε * |L| := by
  set α := alphaSafe L Q C ε with hα
  have habsC_pos : 0 < |C| := abs_pos.mpr hC
  have habsL_nn : 0 ≤ |L| := abs_nonneg L
  have hQ_sq_nn : 0 ≤ Q ^ 2 := sq_nonneg Q
  have hD_nn : 0 ≤ 9 * Q ^ 2 + 24 * ε * |L| * |C| := by
    have : 0 ≤ 24 * ε * |L| * |C| := by positivity
    linarith
  have hsqrt_sq : Real.sqrt (9 * Q ^ 2 + 24 * ε * |L| * |C|) ^ 2 =
      9 * Q ^ 2 + 24 * ε * |L| * |C| := by
    rw [sq, Real.mul_self_sqrt hD_nn]
  have hkey : 2 * |C| * α + 3 * |Q| =
      Real.sqrt (9 * Q ^ 2 + 24 * ε * |L| * |C|) := by
    rw [hα]
    unfold alphaSafe
    have h2C_ne : (2 * |C|) ≠ 0 := by positivity
    field_simp
    ring
  have hsq : (2 * |C| * α + 3 * |Q|) ^ 2 = 9 * Q ^ 2 + 24 * ε * |L| * |C| := by
    rw [hkey, hsqrt_sq]
  have hQsq : Q ^ 2 = |Q| ^ 2 := (sq_abs Q).symm
  have hexpand : 4 * |C| ^ 2 * α ^ 2 + 12 * |C| * |Q| * α =
      24 * ε * |L| * |C| := by
    have := hsq
    rw [hQsq] at this
    nlinarith [this]
  have hfact : 4 * |C| * (|C| * α ^ 2 + 3 * |Q| * α) =
      4 * |C| * (6 * ε * |L|) := by
    nlinarith [hexpand]
  have h4C_ne : (4 * |C|) ≠ 0 := by positivity
  exact mul_left_cancel₀ h4C_ne hfact

/-- Monotonicity helper: `g(α) := α|Q|/2 + α²|C|/6` is increasing for `α ≥ 0`. -/
lemma alphaSafe_helper_mono {Q C : ℝ} :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      a * |Q| / 2 + a ^ 2 * |C| / 6 ≤ b * |Q| / 2 + b ^ 2 * |C| / 6 := by
  intro a b ha_nn hab
  have habsQ : 0 ≤ |Q| := abs_nonneg Q
  have habsC : 0 ≤ |C| := abs_nonneg C
  have hb_nn : 0 ≤ b := le_trans ha_nn hab
  have hba_nn : 0 ≤ b - a := by linarith
  have hba2_nn : 0 ≤ b + a := by linarith
  have h1 : 0 ≤ (b - a) * |Q| / 2 := by positivity
  have h2 : 0 ≤ (b - a) * (b + a) * |C| / 6 := by positivity
  nlinarith [h1, h2, sq_nonneg (b - a)]

/--
  **Central theorem.** For every `α ∈ [0, α_safe(L, Q, C, ε)]`,

      |α²Q/2 + α³C/6|  ≤  ε · |αL|.

  The right-hand side is `ε` times the absolute first-order term, so the
  absolute nonlinear share of the Taylor-3 model is at most an `ε` fraction
  of the absolute linear share throughout the interval. The bound is exact
  when the signed quadratic and cubic terms do not cancel, conservative
  otherwise. Side conditions: `C ≠ 0` and `ε ≥ 0`.
-/
theorem nonlin_share_le_eps_on_alphaSafe
    {L Q C ε : ℝ} (hC_ne : C ≠ 0) (hε : 0 ≤ ε) :
    ∀ α : ℝ, 0 ≤ α → α ≤ alphaSafe L Q C ε →
      |α ^ 2 * Q / 2 + α ^ 3 * C / 6| ≤ ε * |α * L| := by
  intro α hα_nn hα_le
  set α_safe := alphaSafe L Q C ε
  have hid : |C| * α_safe ^ 2 + 3 * |Q| * α_safe = 6 * ε * |L| :=
    alphaSafe_quadratic_id hC_ne hε
  have hα_safe_nn : 0 ≤ α_safe := le_trans hα_nn hα_le
  have hmono :=
    alphaSafe_helper_mono (Q := Q) (C := C) α α_safe hα_nn hα_le
  have hg_safe : α_safe * |Q| / 2 + α_safe ^ 2 * |C| / 6 = ε * |L| := by
    have : 3 * (α_safe * |Q| / 2 + α_safe ^ 2 * |C| / 6) * 2 =
        3 * |Q| * α_safe + |C| * α_safe ^ 2 := by ring
    linarith [hid]
  have hg_α : α * |Q| / 2 + α ^ 2 * |C| / 6 ≤ ε * |L| := by
    calc α * |Q| / 2 + α ^ 2 * |C| / 6
        ≤ α_safe * |Q| / 2 + α_safe ^ 2 * |C| / 6 := hmono
      _ = ε * |L| := hg_safe
  have habsL_nn : 0 ≤ |L| := abs_nonneg _
  have hα_abs : |α| = α := abs_of_nonneg hα_nn
  have htri : |α ^ 2 * Q / 2 + α ^ 3 * C / 6| ≤
      α ^ 2 * |Q| / 2 + α ^ 3 * |C| / 6 := by
    calc |α ^ 2 * Q / 2 + α ^ 3 * C / 6|
        ≤ |α ^ 2 * Q / 2| + |α ^ 3 * C / 6| := abs_add_le _ _
      _ = α ^ 2 * |Q| / 2 + α ^ 3 * |C| / 6 := by
          rw [abs_div, abs_div]
          rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
          rw [abs_of_pos (by norm_num : (0:ℝ) < 6)]
          rw [abs_mul, abs_mul]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 3)]
  have hexp : α ^ 2 * |Q| / 2 + α ^ 3 * |C| / 6 =
      α * (α * |Q| / 2 + α ^ 2 * |C| / 6) := by ring
  have habs_αL : |α * L| = α * |L| := by
    rw [abs_mul, hα_abs]
  calc |α ^ 2 * Q / 2 + α ^ 3 * C / 6|
      ≤ α ^ 2 * |Q| / 2 + α ^ 3 * |C| / 6 := htri
    _ = α * (α * |Q| / 2 + α ^ 2 * |C| / 6) := hexp
    _ ≤ α * (ε * |L|) := mul_le_mul_of_nonneg_left hg_α hα_nn
    _ = ε * (α * |L|) := by ring
    _ = ε * |α * L| := by rw [habs_αL]

end AlphaSafe
