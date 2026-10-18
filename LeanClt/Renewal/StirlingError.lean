import Mathlib

/-!
# Stirling's formula with explicit error

`log n! = n log n - n + ½ log(2πn) + θ_n` with `0 ≤ θ_n ≤ 1/(12n)` for `n ≥ 1`.

Derived from Mathlib's Robbins stepwise bound `log s(n) - log s(n+1) ≤ 1/(12 n (n+1))` for the
Stirling sequence `s(n) = n!/(√(2n) (n/e)^n)`, telescoped and passed to the limit `s(n) → √π`,
together with Mathlib's lower bound `√(2πn)(n/e)^n ≤ n!`.
-/

open Real Filter Topology Stirling

namespace CollatzCLT

/-- The Stirling remainder `θ_n = log n! - (n log n - n + ½ log(2πn))`. -/
noncomputable def stirErr (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - (n * Real.log n - n + Real.log (2 * π * n) / 2)

/-- Telescoped Robbins bound. -/
lemma log_stirlingSeq_sub_le {n : ℕ} (hn : 1 ≤ n) : ∀ k : ℕ,
    Real.log (stirlingSeq n) - Real.log (stirlingSeq (n + k)) ≤ 1 / (12 * n) - 1 / (12 * (n + k)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := log_stirlingSeq_sdiff_le (n + k)
    push_cast at h ⊢
    have hstep : (1 : ℝ) / (12 * ((n : ℝ) + k) * ((n : ℝ) + k + 1)) =
        1 / (12 * ((n : ℝ) + k)) - 1 / (12 * ((n : ℝ) + k + 1)) := by
      field_simp; ring
    rw [hstep] at h
    have e : (n : ℝ) + ((k : ℝ) + 1) = n + k + 1 := by ring
    rw [e, ← Nat.add_assoc]
    linarith

/-- `log s(n) ≤ log √π + 1/(12n)`. -/
lemma log_stirlingSeq_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (stirlingSeq n) ≤ Real.log √π + 1 / (12 * n) := by
  have hlim : Tendsto (fun k : ℕ => Real.log (stirlingSeq (n + k))) atTop (𝓝 (Real.log √π)) :=
    ((Real.continuousAt_log (by positivity)).tendsto).comp
      (tendsto_stirlingSeq_sqrt_pi.comp (tendsto_atTop_atTop_of_monotone
        (fun a b h => by omega) (fun b => ⟨b, by omega⟩)))
  have : Real.log (stirlingSeq n) - Real.log √π ≤ 1 / (12 * n) := by
    refine le_of_tendsto (tendsto_const_nhds.sub hlim) (Eventually.of_forall fun k => ?_)
    have h := log_stirlingSeq_sub_le hn k
    have : (0 : ℝ) ≤ 1 / (12 * ((n : ℝ) + k)) := by positivity
    linarith
  linarith

/-- **Stirling with error.** `0 ≤ θ_n ≤ 1/(12n)` for `n ≥ 1`. -/
theorem stirErr_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ stirErr n ∧ stirErr n ≤ 1 / (12 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have := le_log_factorial_stirling (n := n) (by omega)
    unfold stirErr
    rw [Real.log_mul (by positivity) hn'.ne']
    linarith
  · have h := log_stirlingSeq_le hn
    have hs : Real.log (stirlingSeq n) = Real.log (n.factorial : ℝ) -
        (Real.log (2 * n) / 2 + n * (Real.log n - 1)) := by
      unfold stirlingSeq
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hn'.ne' (Real.exp_pos 1).ne',
        Real.log_exp]
    rw [hs, Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hn'.ne'] at h
    unfold stirErr
    rw [Real.log_mul (by positivity) hn'.ne', Real.log_mul (by norm_num) Real.pi_pos.ne']
    linarith

end CollatzCLT
