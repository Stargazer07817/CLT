import LeanClt.Transfer.Adjacent
import LeanClt.Main.Conditional
import LeanClt.Main.OddBridge

/-!
# Theorem 1.1 (i)–(iii), conditional on Theorem 3.1 and on positivity

Lemma 6.1 is now proved (`adjacent_of_transport`) from the transfer theorem, the twisted renewal
theorem and the transport property of each clock. What remains as hypotheses:

* `JointMixing`: Theorem 3.1 (§3, from Tao's imports);
* `IrrMeasure d ϰ`: Rhin's irrationality measure (Imported Theorem 2.6 [`imp:rhin`]);
* positive lower density of a raw predecessor set, the paper's Theorem 8.1: `P_T(b)` for the raw
  clock, `P_T(2b) ⊆ P_F(b)` for the shortcut clock, and `P_T(b)` (with `b` odd) for the odd clock.
  For the odd clock the bridge to `P_U(b)` is proved in `Main/OddBridge.lean`: the fixed-base limit
  gives a density `d_U` of `P_U(b)` without positivity, and `P_T(b) = {2^e u : u ∈ P_U(b)}` forces
  `c_T ≤ 2 d_U`.

The constants match: `κ_{1,1} = 3/c = κ_T`, `D_{1,1} = (β+ℓ)²/c³ = V_T/2`; `κ_{1,0} = κ_F`,
`D_{1,0} = V_F/2`; `κ_{0,1} = κ_U`, `D_{0,1} = V_U/2`.
-/

open Real Filter

namespace CollatzCLT

lemma alpha_gt_one : (1 : ℝ) < alpha := by unfold alpha; norm_num

/-- **Theorem 1.1 (i)+(ii), raw clock**, conditional on Theorem 3.1, Rhin's measure and
positivity. -/
theorem main_T_of_mixing (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : 0 < b)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred T b) d) ∧ CLTOn (Pred T b) (normalised (hit T b) κT VT) := by
  have h := adjacent_of_transport hJM hθ (transport_T b)
  have e1 : (2 * 1 + 1) / c = κT := by unfold κT; norm_num
  have e2 : (1 * bet + 1 * ell) ^ 2 / c ^ 3 = VT / 2 := by unfold VT bet ell; ring
  rw [e1, e2] at h
  exact main_T b hb alpha_gt_one h hpos

/-- **Theorem 1.1 (i)+(ii), shortcut clock**, conditional on Theorem 3.1, Rhin's measure and
positivity of `P_T(2b)`. -/
theorem main_F_of_mixing (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : 0 < b)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * X ≤ ((window (Pred T (2 * b)) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred F b) d) ∧ CLTOn (Pred F b) (normalised (hit F b) κF VF) := by
  have h := adjacent_of_transport hJM hθ (transport_F b)
  have e1 : (2 * 1 + 0) / c = κF := by unfold κF; norm_num
  have e2 : (1 * bet + 0 * ell) ^ 2 / c ^ 3 = VF / 2 := by unfold VF bet; ring
  rw [e1, e2] at h
  exact main_F' b hb alpha_gt_one h hposT

/-- **Theorem 1.1 (iii), odd clock**, conditional on Theorem 3.1, Rhin's measure and positivity
of the raw predecessor set `P_T(b)` (Theorem 8.1), for odd `b`. -/
theorem main_U_of_mixing (hJM : JointMixing) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (b : ℕ)
    (hb : Odd b)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (PredU b) d) ∧ CLTOn (PredU b) (normalised (hit U b) κU VU) := by
  have h := adjacent_of_transport hJM hθ (transport_U b)
  have e1 : (2 * 0 + 1) / c = κU := by unfold κU; norm_num
  have e2 : (0 * bet + 1 * ell) ^ 2 / c ^ 3 = VU / 2 := by unfold VU ell; ring
  rw [e1, e2] at h
  obtain ⟨dU, hdU⟩ := density_predU_of_adjacent b alpha_gt_one h
  exact main_U b alpha_gt_one h (predU_pos_of_predT_pos hb hdU hposT)

end CollatzCLT
