import LeanClt.Transfer.Defs
import LeanClt.Renewal.Kernel

/-!
# Asymptotic helpers in `L = log x`

All the "for large `x`" steps of §5 reduce to: a power of `L` times `exp(-k L^b)` is eventually
below any negative power of `L`, and `log x → ∞`.
-/

open Real Filter Topology

namespace CollatzCLT

/-- `L^a e^{-k L^b} ≤ L^{-A}` for large `L`. -/
lemma ev_pow_mul_exp_le (a A : ℝ) {k b : ℝ} (hk : 0 < k) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, L ^ a * Real.exp (-(k * L ^ b)) ≤ L ^ (-A) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((a + A) / b) k hk).comp
    (tendsto_rpow_atTop hb)
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop (0 : ℝ)]
    with L hL hL0
  simp only [Function.comp_apply] at hL
  rw [← Real.rpow_mul hL0.le, show b * ((a + A) / b) = a + A by field_simp] at hL
  have hpos : 0 < L ^ (-A) := Real.rpow_pos_of_pos hL0 _
  have e : L ^ a = L ^ (a + A) * L ^ (-A) := by rw [← Real.rpow_add hL0]; ring_nf
  rw [e, mul_right_comm, neg_mul_eq_neg_mul]
  calc L ^ (a + A) * Real.exp (-k * L ^ b) * L ^ (-A) ≤ 1 * L ^ (-A) := by gcongr
    _ = L ^ (-A) := one_mul _

/-- Transfer an eventual statement in `L` to one in `x` through `L = log x`. -/
lemma ev_of_log {P : ℝ → Prop} (h : ∀ᶠ L : ℝ in atTop, P L) : ∀ᶠ x : ℝ in atTop, P (Lx x) :=
  Real.tendsto_log_atTop.eventually h

lemma Lx_pos_ev : ∀ᶠ x : ℝ in atTop, 1 ≤ Lx x :=
  ev_of_log (eventually_ge_atTop 1)

lemma n0_le (x : ℝ) (hx : 1 ≤ Lx x) : (n0 x : ℝ) ≤ Lx x / (10 * ell) :=
  Nat.floor_le (by have := ell_pos; positivity)

lemma n0_ge (x : ℝ) : Lx x / (10 * ell) - 1 ≤ (n0 x : ℝ) := by
  have := Nat.lt_floor_add_one (Lx x / (10 * ell)); unfold n0; linarith

lemma mT_le (x : ℝ) (hx : 1 ≤ Lx x) : (mT x : ℝ) ≤ (alpha - 1) * Lx x / 100 :=
  Nat.floor_le (by unfold alpha; norm_num; positivity)

lemma mT_ge (x : ℝ) : (alpha - 1) * Lx x / 100 - 1 ≤ (mT x : ℝ) := by
  have := Nat.lt_floor_add_one ((alpha - 1) * Lx x / 100); unfold mT; linarith

lemma rpow_eq_exp_Lx {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ a = Real.exp (a * Lx x) := by
  rw [Real.rpow_def_of_pos hx, Lx, mul_comm]

end CollatzCLT
