import Mathlib

/-!
# The chain estimate (6.7, `eq:chain`)

Abstract form of the telescoping argument in the proof of Proposition 6.2, in the
logarithmic variable `u = log Y`. Adjacent scales are `u ≤ u' ≤ α u`. If each adjacent
pair differs by at most `C u^{-δ}`, then any `u ≥ b` differs from `b` by at most
`C b^{-δ} / (1 - α^{-δ})`. There is no factor counting the number of scales.

The cap `u' ≤ umax` encodes the frequency restriction `|s| √(log Y') ≤ M₀` of Lemma 6.1.
It holds at every intermediate scale of the chain because all of them lie below the
top scale.
-/

open Real Finset

namespace CollatzCLT

/-- Chain estimate, finite version: within `J` adjacent steps of `b`. -/
lemma chain_bound_aux {E : Type*} [SeminormedAddCommGroup E] {g : ℝ → E}
    {α δ C u0 umax : ℝ} (hα : 1 < α) (hC : 0 ≤ C)
    (hadj : ∀ u u', u0 ≤ u → u ≤ u' → u' ≤ α * u → u' ≤ umax → ‖g u - g u'‖ ≤ C * u ^ (-δ))
    {b : ℝ} (hb0 : u0 ≤ b) (hbpos : 0 < b) :
    ∀ J : ℕ, ∀ u, b ≤ u → u ≤ α ^ J * b → u ≤ umax →
      ‖g u - g b‖ ≤ C * b ^ (-δ) * ∑ j ∈ range J, (α ^ (-δ)) ^ j := by
  have hα0 : 0 < α := by linarith
  intro J
  induction J with
  | zero =>
    intro u hbu hu _
    simp only [pow_zero, one_mul] at hu
    rw [le_antisymm hu hbu, sub_self, norm_zero]
    simp
  | succ J ih =>
    intro u hbu hu humax
    have hterm : 0 ≤ C * b ^ (-δ) * (α ^ (-δ)) ^ J := by positivity
    rw [sum_range_succ, mul_add]
    by_cases hJ : u ≤ α ^ J * b
    · linarith [ih u hbu hJ humax]
    · -- the last adjacent step goes from `v = α^J b` to `u`
      replace hJ := not_le.mp hJ
      set v := α ^ J * b with hv
      have hbv : b ≤ v := by
        have : (1 : ℝ) ≤ α ^ J := one_le_pow₀ hα.le
        nlinarith
      have h1 : ‖g v - g u‖ ≤ C * v ^ (-δ) :=
        hadj v u (hb0.trans hbv) hJ.le (by rw [pow_succ] at hu; nlinarith) humax
      have hvpow : v ^ (-δ) = b ^ (-δ) * (α ^ (-δ)) ^ J := by
        rw [hv, mul_rpow (by positivity) hbpos.le, mul_comm, ← rpow_natCast, ← rpow_natCast,
          ← rpow_mul hα0.le, ← rpow_mul hα0.le, mul_comm (J : ℝ)]
      have h2 := ih v hbv le_rfl (hJ.le.trans humax)
      calc ‖g u - g b‖ ≤ ‖g u - g v‖ + ‖g v - g b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C * v ^ (-δ) + C * b ^ (-δ) * ∑ j ∈ range J, (α ^ (-δ)) ^ j := by
          rw [norm_sub_rev]; exact add_le_add h1 h2
        _ = _ := by rw [hvpow]; ring

/-- **Chain estimate (6.7, `eq:chain`).** If adjacent scales differ by at most `C u^{-δ}`, then every
scale `u ≥ b` (up to the cap) differs from `b` by at most `C b^{-δ} / (1 - α^{-δ})`. -/
theorem chain_bound {E : Type*} [SeminormedAddCommGroup E] {g : ℝ → E}
    {α δ C u0 umax : ℝ} (hα : 1 < α) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hadj : ∀ u u', u0 ≤ u → u ≤ u' → u' ≤ α * u → u' ≤ umax → ‖g u - g u'‖ ≤ C * u ^ (-δ))
    {b u : ℝ} (hb0 : u0 ≤ b) (hbpos : 0 < b) (hbu : b ≤ u) (hu : u ≤ umax) :
    ‖g u - g b‖ ≤ C / (1 - α ^ (-δ)) * b ^ (-δ) := by
  have hα0 : 0 < α := by linarith
  -- the geometric ratio `r = α^{-δ}` lies in `(0, 1)`
  have hr0 : 0 ≤ α ^ (-δ) := by positivity
  have hr1 : α ^ (-δ) < 1 := rpow_lt_one_of_one_lt_of_neg hα (by linarith)
  -- choose `J` with `u ≤ α^J b`
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (u / b) hα
  have huJ : u ≤ α ^ J * b := by
    rw [div_lt_iff₀ hbpos] at hJ; exact hJ.le
  have h := chain_bound_aux hα hC hadj hb0 hbpos J u hbu huJ hu
  have hsum : ∑ j ∈ range J, (α ^ (-δ)) ^ j ≤ 1 / (1 - α ^ (-δ)) := by
    rw [one_div, ← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun j _ => by positivity)
  calc ‖g u - g b‖ ≤ C * b ^ (-δ) * ∑ j ∈ range J, (α ^ (-δ)) ^ j := h
    _ ≤ C * b ^ (-δ) * (1 / (1 - α ^ (-δ))) := by gcongr
    _ = C / (1 - α ^ (-δ)) * b ^ (-δ) := by ring

end CollatzCLT
