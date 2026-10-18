import LeanClt.Renewal.RotationJumps
import LeanClt.Renewal.Theorem41

/-!
# Proposition 4.5 [`prop:fixedfreq`]: fixed-frequency decay (stage 7 of the checkpoint-20 plan)

Using `IrrMeasure` only. For `s = 2πr/Q₀` with `gcd(r, Q₀) = 1`, `Q₀ ≥ 2`, and integer rewards
`(ρ, η)` with `gcd(ρ, η) = 1`, `R^{ρ,η}_s(u) = O(u^{-ε/2} log u)`, `ε = 1/(ϰ+1)`, uniformly in `r`.

The proof is that of Theorem 4.1 at the window `X = √u log u`, with the rotation step replaced.

* **Reused as they are:** the tail outside the window (`err_tail`), the extra endpoint
  (`err_extra`), the Gaussian replacement (`err_gauss`). After them,
  `R_s(u) = ∑_{t ∈ W} g_u(t) e^{-iηst} φ(h_t) + O(·)`, where `h_t = u/ℓ + θt` and
  `φ(x) = 2^{⌈x⌉-x} e^{-iρs⌈x⌉}` (`phiF`, `ph_wR_qv`).
* **Abel summation over the window** (`norm_window_sum_le`), with the sharp total-variation bound
  `∑ |g_u(t+1) - g_u(t)| ≤ 2 sup g_u ≤ 2u^{-1/2}` from the unimodality of `g_u`
  (`sum_abs_sub_le_two_mul`).
* **The partial sums** (`norm_partial_Yf_le`). Split by residue classes `t ≡ i (mod Q₀)`. On a class
  the phase `e^{-iηst}` is constant, and `φ(h_t) = ψ(γ_i + mθ)` with `ψ(y) = φ(Q₀y)` (`psiF`),
  `1`-periodic with `Q₀` equally spaced jumps per period, bounded by 2 and `4Q₀`-Lipschitz on each
  cell, so Lemma 2.7 with `J = Q₀` jumps (`rotation_discrepancy_jumps_explicit`) applies. The
  class means cancel: if `Q₀ ∤ ρ`, the mean of `ψ` is 0, because `ψ(y + 1/Q₀) = e^{-iρs} ψ(y)` and
  `e^{-iρs} ≠ 1` (`integral_psiF_eq_zero`); if `Q₀ | ρ`, then `Q₀ ∤ η` and the class phases are the
  `Q₀`-th roots of unity `e^{-iηs i}`, whose sum is 0.
* Nothing depends on `r` beyond `gcd(r, Q₀) = 1`, so the constant is uniform in `r`; the bounded
  range of `u` is absorbed into `C` through `renewalR_bounded`.
-/

open Real Finset Complex MeasureTheory intervalIntegral Filter Topology

noncomputable section

namespace CollatzCLT

/-! ## The kernel `φ` and its rescaling `ψ` -/

/-- `φ_a(x) = 2^{⌈x⌉-x} e^{-ia⌈x⌉}`, the kernel of the fixed-frequency proof (with `a = ρs`). -/
def phiF (a x : ℝ) : ℂ :=
  cexp ((ell : ℂ) * (((⌈x⌉ : ℝ) - x : ℝ) : ℂ)) * cexp (-((a * ⌈x⌉ : ℝ) : ℂ) * I)

/-- `ψ(y) = φ_a(Q y)`: `1`-periodic with `Q` equally spaced jumps per period when `aQ ∈ 2πℤ`. -/
def psiF (a : ℝ) (Q : ℕ) (y : ℝ) : ℂ := phiF a (Q * y)

lemma norm_cexp_ell_le {r : ℝ} (hr : r ≤ 1) : ‖cexp ((ell : ℂ) * (r : ℂ))‖ ≤ 2 := by
  rw [Complex.norm_exp]
  have : ((ell : ℂ) * (r : ℂ)).re = ell * r := by simp
  rw [this, ← exp_ell]
  exact Real.exp_le_exp.mpr (by nlinarith [ell_pos])

lemma norm_phiF_le (a x : ℝ) : ‖phiF a x‖ ≤ 2 := by
  unfold phiF
  rw [norm_mul, norm_cexp_neg_real_mul_I, mul_one]
  exact norm_cexp_ell_le (ceil_sub_mem x).2.le

lemma phiF_add_int (a x : ℝ) (n : ℤ) :
    phiF a (x + n) = cexp (-((a * n : ℝ) : ℂ) * I) * phiF a x := by
  unfold phiF
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Int.ceil_add_intCast]
  congr 1
  push_cast
  ring

/-- `ψ` is `1`-periodic when `e^{-iaQ} = 1`. -/
lemma psiF_add_one {a : ℝ} {Q : ℕ} (haQ : cexp (-((a * Q : ℝ) : ℂ) * I) = 1) (y : ℝ) :
    psiF a Q (y + 1) = psiF a Q y := by
  unfold psiF
  rw [show (Q : ℝ) * (y + 1) = Q * y + ((Q : ℤ) : ℝ) by push_cast; ring, phiF_add_int]
  rw [show (a * ((Q : ℤ) : ℝ) : ℝ) = a * Q by push_cast; ring, haQ, one_mul]

/-- `ψ(y + 1/Q) = e^{-ia} ψ(y)`. -/
lemma psiF_add_inv {a : ℝ} {Q : ℕ} (hQ : 1 ≤ Q) (y : ℝ) :
    psiF a Q (y + 1 / Q) = cexp (-((a : ℝ) : ℂ) * I) * psiF a Q y := by
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold psiF
  rw [show (Q : ℝ) * (y + 1 / Q) = Q * y + ((1 : ℤ) : ℝ) by push_cast; field_simp, phiF_add_int]
  push_cast
  rw [mul_one]

lemma norm_psiF_le (a : ℝ) (Q : ℕ) (y : ℝ) : ‖psiF a Q y‖ ≤ 2 := norm_phiF_le a _

/-- `ψ` is `4Q`-Lipschitz on each cell `(k/Q, (k+1)/Q]`. -/
lemma psiF_lip (a : ℝ) (Q : ℕ) (x y : ℝ) (h : ⌈(Q : ℝ) * (x - 0)⌉ = ⌈(Q : ℝ) * (y - 0)⌉) :
    ‖psiF a Q x - psiF a Q y‖ ≤ 4 * Q * |x - y| := by
  rw [sub_zero, sub_zero] at h
  unfold psiF phiF
  rw [h, ← sub_mul, norm_mul, norm_cexp_neg_real_mul_I, mul_one]
  have hx := ceil_sub_mem ((Q : ℝ) * x)
  have hy := ceil_sub_mem ((Q : ℝ) * y)
  rw [h] at hx
  have hz : ((ell : ℂ)).re = ell := Complex.ofReal_re ell
  have hb := norm_cexp_sub_cexp_le' (ell : ℂ) (a := (⌈(Q : ℝ) * y⌉ : ℝ) - Q * x)
    (b := (⌈(Q : ℝ) * y⌉ : ℝ) - Q * y) hx.1 hx.2.le hy.1 hy.2.le hz
  refine hb.trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ell_pos, exp_ell]
  have e : |(⌈(Q : ℝ) * y⌉ : ℝ) - Q * x - ((⌈(Q : ℝ) * y⌉ : ℝ) - Q * y)| = Q * |x - y| := by
    rw [show (⌈(Q : ℝ) * y⌉ : ℝ) - Q * x - ((⌈(Q : ℝ) * y⌉ : ℝ) - Q * y) = Q * (y - x) by ring,
      abs_mul, Nat.abs_cast, abs_sub_comm]
  rw [e]
  have hl := ell_lt_one
  have hl0 := ell_pos
  have : 0 ≤ (Q : ℝ) * |x - y| := by positivity
  nlinarith

/-- `ψ` satisfies the hypotheses of Lemma 2.7 with `J = Q` jumps, `x₀ = 0`, `M = 2`, `L = 4Q`. -/
lemma piecewiseLipJ_psiF {a : ℝ} {Q : ℕ} (haQ : cexp (-((a * Q : ℝ) : ℂ) * I) = 1) :
    PiecewiseLipJ (psiF a Q) 2 (4 * Q) 0 Q :=
  ⟨psiF_add_one haQ, norm_psiF_le a Q, psiF_lip a Q⟩

/-- **The mean of `ψ` vanishes when `e^{-ia} ≠ 1`**: `ψ(y + 1/Q) = e^{-ia} ψ(y)`, and the integral
over a period is translation invariant. -/
lemma integral_psiF_eq_zero {a : ℝ} {Q : ℕ} (hQ : 1 ≤ Q)
    (haQ : cexp (-((a * Q : ℝ) : ℂ) * I) = 1) (ha : cexp (-((a : ℝ) : ℂ) * I) ≠ 1) :
    ∫ x in (0 : ℝ)..1, psiF a Q x = 0 := by
  set μ := ∫ x in (0 : ℝ)..1, psiF a Q x with hμ
  have hper : Function.Periodic (psiF a Q) 1 := psiF_add_one haQ
  have h1 : ∫ x in (0 : ℝ)..1, psiF a Q (x + 1 / Q) = μ := by
    rw [intervalIntegral.integral_comp_add_right, zero_add,
      show (1 : ℝ) + 1 / Q = 1 / Q + 1 by ring, hper.intervalIntegral_add_eq (1 / Q) 0, zero_add]
  have h2 : ∫ x in (0 : ℝ)..1, psiF a Q (x + 1 / Q) = cexp (-((a : ℝ) : ℂ) * I) * μ := by
    simp_rw [psiF_add_inv hQ]
    rw [intervalIntegral.integral_const_mul]
  have h3 : (1 - cexp (-((a : ℝ) : ℂ) * I)) * μ = 0 := by
    rw [sub_mul, one_mul, ← h2, h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h).symm ha
  · exact h

/-! ## The main sum after the Gaussian replacement -/

/-- The phase and kernel of the main sum: `Y(t) = e^{-iηst} φ_{ρs}(h_t)`. -/
def Yf (ρ η s u : ℝ) (t : ℕ) : ℂ :=
  cexp (-((η * s * t : ℝ) : ℂ) * I) * phiF (ρ * s) (hT u t)

lemma norm_Yf_le (ρ η s u : ℝ) (t : ℕ) : ‖Yf ρ η s u t‖ ≤ 2 := by
  unfold Yf
  rw [norm_mul, norm_cexp_neg_real_mul_I, one_mul]
  exact norm_phiF_le _ _

/-- **The exterior phase, the weight phase and `q_{ρs}` combine into `e^{-iηst} φ_{ρs}(h_t)`.** -/
lemma ph_wR_qv (ρ η s u : ℝ) (t : ℕ) :
    cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) * (wR u (s * (ρ * θ + η)) t * qv (ρ * s) (hT u t)) =
      (gU u t : ℂ) * Yf ρ η s u t := by
  have hh : hT u t = u / ell + θ * t := by unfold hT; exact hT_eq u t
  unfold wR qv Yf phiF
  set H := hT u t
  have key : cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) *
      cexp (-((s * (ρ * θ + η) * t : ℝ) : ℂ) * I) *
      cexp (((ell : ℂ) - ((ρ * s : ℝ) : ℂ) * I) * (((⌈H⌉ : ℝ) - H : ℝ) : ℂ)) =
      cexp (-((η * s * t : ℝ) : ℂ) * I) * (cexp ((ell : ℂ) * (((⌈H⌉ : ℝ) - H : ℝ) : ℂ)) *
        cexp (-((ρ * s * ⌈H⌉ : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hl : (ell : ℂ) ≠ 0 := by exact_mod_cast ell_pos.ne'
    rw [hh]
    push_cast
    field_simp
    ring
  calc cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) * ((gU u t : ℂ) *
        cexp (-((s * (ρ * θ + η) * t : ℝ) : ℂ) * I) *
        cexp (((ell : ℂ) - ((ρ * s : ℝ) : ℂ) * I) * (((⌈H⌉ : ℝ) - H : ℝ) : ℂ)))
      = (gU u t : ℂ) * (cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) *
          cexp (-((s * (ρ * θ + η) * t : ℝ) : ℂ) * I) *
          cexp (((ell : ℂ) - ((ρ * s : ℝ) : ℂ) * I) * (((⌈H⌉ : ℝ) - H : ℝ) : ℂ))) := by ring
    _ = _ := by rw [key]

/-! ## The partial sums, by residue classes -/

/-- On the residue class `i` mod `Q`, `Y(a + mQ + i) = e^{-iηs(a+i)} ψ(γ_i + mθ)`. -/
lemma Yf_class (ρ η s u : ℝ) {Q : ℕ} (hQ : 1 ≤ Q) (hη : cexp (-((η * s * Q : ℝ) : ℂ) * I) = 1)
    (a i m : ℕ) :
    Yf ρ η s u (a + (m * Q + i)) = cexp (-((η * s * ((a + i : ℕ) : ℝ) : ℝ) : ℂ) * I) *
      psiF (ρ * s) Q ((u / ell + θ * ((a + i : ℕ) : ℝ)) / Q + m * θ) := by
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold Yf psiF
  have harg : hT u (a + (m * Q + i)) = (Q : ℝ) * ((u / ell + θ * ((a + i : ℕ) : ℝ)) / Q + m * θ) := by
    unfold hT; rw [hT_eq]; push_cast; field_simp; ring
  rw [harg]
  congr 1
  have e : -((η * s * ((a + (m * Q + i) : ℕ) : ℝ) : ℝ) : ℂ) * I =
      -((η * s * ((a + i : ℕ) : ℝ) : ℝ) : ℂ) * I + (m : ℂ) * (-((η * s * Q : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul, hη, one_pow, mul_one]

/-- A sum over `[0, qQ)` by residue classes mod `Q`. -/
lemma sum_range_classes (f : ℕ → ℂ) (Q q : ℕ) :
    ∑ k ∈ range (q * Q), f k = ∑ i ∈ range Q, ∑ m ∈ range q, f (m * Q + i) := by
  rw [sum_range_mul_blocks, Finset.sum_comm]

/-- Shifting a rotation sum from `[0, q)` to `[1, q]`. -/
lemma sum_range_eq_sum_Icc (g : ℝ → ℂ) (γ : ℝ) (q : ℕ) :
    ∑ m ∈ range q, g (γ + m * θ) = ∑ j ∈ Icc 1 q, g ((γ - θ) + j * θ) := by
  rw [show Icc 1 q = Ico 1 (q + 1) by ext; simp, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply sum_congr rfl
  intro m _
  congr 1
  push_cast
  ring

/-- **The partial sums of `Y`.** If the class means cancel (`μ ∑_i e^{-iηs i} = 0`, `μ` the mean of
`ψ`), every partial sum `∑_{k<n} Y(a + k)` is at most `Q · C_Q (2 + 4Q) n^{1-ε} + 2Q`, with
`C_Q = Q(12 d^{-1/ϰ} + 14)` the constant of Lemma 2.7 with `Q` jumps. -/
lemma norm_partial_Yf_le {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η s u : ℝ) {Q : ℕ} (hQ : 1 ≤ Q)
    (hρQ : cexp (-((ρ * s * Q : ℝ) : ℂ) * I) = 1) (hηQ : cexp (-((η * s * Q : ℝ) : ℂ) * I) = 1)
    (hcase : (∫ x in (0 : ℝ)..1, psiF (ρ * s) Q x) *
      ∑ i ∈ range Q, cexp (-((η * s * i : ℝ) : ℂ) * I) = 0)
    (a n : ℕ) :
    ‖∑ k ∈ range n, Yf ρ η s u (a + k)‖ ≤
      Q * (Q * (12 * d ^ (-(1 / ϰ)) + 14) * (2 + 4 * Q)) * (n : ℝ) ^ (1 - 1 / (ϰ + 1)) + 2 * Q := by
  have hd := hθ.1
  have hϰ : 1 ≤ ϰ := hθ.2.1
  have hexp : 0 ≤ 1 - 1 / (ϰ + 1) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  set CQ : ℝ := Q * (12 * d ^ (-(1 / ϰ)) + 14) * (2 + 4 * Q) with hCQ
  have hCQ0 : 0 ≤ CQ := by have := Real.rpow_nonneg hd.le (-(1 / ϰ)); positivity
  set μ := ∫ x in (0 : ℝ)..1, psiF (ρ * s) Q x with hμ
  have hpsi := piecewiseLipJ_psiF (a := ρ * s) (Q := Q) (by rw [show ρ * s * Q = (ρ * s) * Q by ring] at hρQ; exact hρQ)
  set q := n / Q with hq
  set r0 := n % Q with hr0
  have hn : n = q * Q + r0 := by rw [hq, hr0, mul_comm]; exact (Nat.div_add_mod n Q).symm
  have hr0Q : r0 < Q := Nat.mod_lt n (by omega)
  have hqn : (q : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n Q
  -- the remainder
  have hrem : ‖∑ k ∈ range r0, Yf ρ η s u (a + (q * Q + k))‖ ≤ 2 * Q := by
    calc _ ≤ ∑ k ∈ range r0, ‖Yf ρ η s u (a + (q * Q + k))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range r0, (2 : ℝ) := sum_le_sum fun k _ => norm_Yf_le _ _ _ _ _
      _ = 2 * r0 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ 2 * Q := by have : (r0 : ℝ) ≤ Q := by exact_mod_cast hr0Q.le
                      linarith
  -- the complete classes
  set ζ : ℕ → ℂ := fun i => cexp (-((η * s * ((a + i : ℕ) : ℝ) : ℝ) : ℂ) * I) with hζ
  set γ : ℕ → ℝ := fun i => (u / ell + θ * ((a + i : ℕ) : ℝ)) / Q with hγ
  have hblocks : ∑ k ∈ range (q * Q), Yf ρ η s u (a + k) =
      ∑ i ∈ range Q, ζ i * (∑ m ∈ range q, psiF (ρ * s) Q (γ i + m * θ) - q * μ) := by
    rw [sum_range_classes (fun k => Yf ρ η s u (a + k))]
    have hcancel : ∑ i ∈ range Q, ζ i * ((q : ℂ) * μ) = 0 := by
      have e : ∀ i, ζ i = cexp (-((η * s * a : ℝ) : ℂ) * I) * cexp (-((η * s * i : ℝ) : ℂ) * I) := by
        intro i; simp only [hζ]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp_rw [e]
      rw [← sum_mul, ← mul_sum]
      calc cexp (-((η * s * a : ℝ) : ℂ) * I) * (∑ i ∈ range Q, cexp (-((η * s * i : ℝ) : ℂ) * I)) *
            ((q : ℂ) * μ)
          = cexp (-((η * s * a : ℝ) : ℂ) * I) * q * (μ *
              ∑ i ∈ range Q, cexp (-((η * s * i : ℝ) : ℂ) * I)) := by ring
        _ = 0 := by rw [hcase, mul_zero]
    have : ∑ i ∈ range Q, ζ i * (∑ m ∈ range q, psiF (ρ * s) Q (γ i + m * θ) - q * μ) =
        ∑ i ∈ range Q, ζ i * ∑ m ∈ range q, psiF (ρ * s) Q (γ i + m * θ) := by
      rw [← sub_zero (∑ i ∈ range Q, ζ i * ∑ m ∈ range q, psiF (ρ * s) Q (γ i + m * θ)),
        ← hcancel, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => Yf_class ρ η s u hQ hηQ a i m
  have hclass : ∀ i, ‖∑ m ∈ range q, psiF (ρ * s) Q (γ i + m * θ) - q * μ‖ ≤
      CQ * (n : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
    intro i
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · rw [hq0]; simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul, sub_zero, norm_zero]
      positivity
    rw [sum_range_eq_sum_Icc]
    have h := rotation_discrepancy_jumps_explicit hθ Q hQ (psiF (ρ * s) Q) 2 (4 * Q) 0 hpsi
      (γ i - θ) q hqpos
    refine h.trans ?_
    rw [hCQ]
    have : (q : ℝ) ^ (1 - 1 / (ϰ + 1)) ≤ (n : ℝ) ^ (1 - 1 / (ϰ + 1)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hqn hexp
    have h0 : 0 ≤ (Q : ℝ) * (12 * d ^ (-(1 / ϰ)) + 14) * (2 + 4 * Q) := by
      have := Real.rpow_nonneg hd.le (-(1 / ϰ)); positivity
    calc (Q : ℝ) * (12 * d ^ (-(1 / ϰ)) + 14) * (2 + 4 * Q) * (q : ℝ) ^ (1 - 1 / (ϰ + 1))
        ≤ (Q : ℝ) * (12 * d ^ (-(1 / ϰ)) + 14) * (2 + 4 * Q) * (n : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
          gcongr
      _ = _ := rfl
  have hζ1 : ∀ i, ‖ζ i‖ = 1 := fun i => norm_cexp_neg_real_mul_I _
  have hmain : ‖∑ k ∈ range (q * Q), Yf ρ η s u (a + k)‖ ≤
      Q * (CQ * (n : ℝ) ^ (1 - 1 / (ϰ + 1))) := by
    rw [hblocks]
    calc _ ≤ ∑ i ∈ range Q, ‖ζ i * (∑ m ∈ range q, psiF (ρ * s) Q (γ i + m * θ) - q * μ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ range Q, CQ * (n : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
          refine sum_le_sum fun i _ => ?_
          rw [norm_mul, hζ1, one_mul]; exact hclass i
      _ = Q * (CQ * (n : ℝ) ^ (1 - 1 / (ϰ + 1))) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hsplit : ∑ k ∈ range n, Yf ρ η s u (a + k) = ∑ k ∈ range (q * Q), Yf ρ η s u (a + k) +
      ∑ k ∈ range r0, Yf ρ η s u (a + (q * Q + k)) := by
    conv_lhs => rw [hn]
    exact sum_range_add _ _ _
  rw [hsplit]
  calc _ ≤ ‖∑ k ∈ range (q * Q), Yf ρ η s u (a + k)‖ +
        ‖∑ k ∈ range r0, Yf ρ η s u (a + (q * Q + k))‖ := norm_add_le _ _
    _ ≤ Q * (CQ * (n : ℝ) ^ (1 - 1 / (ϰ + 1))) + 2 * Q := add_le_add hmain hrem
    _ = _ := by rw [hCQ]; ring

/-! ## The sharp total-variation bound for the Gaussian weights -/

/-- **Total variation of a unimodal nonnegative sequence** bounded by `G` is at most `2G`. -/
lemma sum_abs_sub_le_two_mul (f : ℕ → ℝ) (m N : ℕ) {G : ℝ} (h0 : ∀ j, 0 ≤ f j)
    (hG : ∀ j, f j ≤ G) (hinc : ∀ j, j < m → f j ≤ f (j + 1))
    (hdec : ∀ j, m ≤ j → f (j + 1) ≤ f j) :
    ∑ j ∈ range N, |f (j + 1) - f j| ≤ 2 * G := by
  have hG0 : 0 ≤ G := (h0 0).trans (hG 0)
  have hup : ∀ K, K ≤ m → ∑ j ∈ range K, |f (j + 1) - f j| = f K - f 0 := by
    intro K hK
    rw [← sum_range_sub f K]
    refine sum_congr rfl fun j hj => abs_of_nonneg (sub_nonneg.mpr (hinc j ?_))
    have := mem_range.mp hj; omega
  rcases le_or_gt N m with hNm | hmN
  · rw [hup N hNm]; linarith [hG N, h0 0]
  · rw [← sum_range_add_sum_Ico _ hmN.le, hup m le_rfl]
    have hdown : ∑ j ∈ Ico m N, |f (j + 1) - f j| = f m - f N := by
      rw [sum_Ico_eq_sum_range]
      have := sum_range_sub' (fun k => f (m + k)) (N - m)
      rw [Nat.add_sub_cancel' hmN.le, add_zero] at this
      rw [← this]
      refine sum_congr rfl fun k _ => ?_
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hdec (m + k) (by omega))), add_assoc]
    rw [hdown]
    linarith [hG m, h0 0, h0 N]

/-- `g_u` increases up to `t₀`. -/
lemma gU_le_succ {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : x + 1 / 2 ≤ t0 u) : gU u x ≤ gU u (x + 1) := by
  unfold gU
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hK := Kg_pos hu
  nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hx)]

/-- `g_u` decreases after `t₀`. -/
lemma gU_succ_le {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : t0 u ≤ x + 1 / 2) : gU u (x + 1) ≤ gU u x := by
  unfold gU
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hK := Kg_pos hu
  nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hx)]

/-- **The sharp total-variation bound:** along consecutive integers from `b`,
`∑_{j<N} |g_u(b+j+1) - g_u(b+j)| ≤ 2u^{-1/2}`. -/
lemma tv_gU_le {u : ℝ} (hu : 0 < u) (b N : ℕ) :
    ∑ j ∈ range N, |gU u ((b + (j + 1) : ℕ) : ℝ) - gU u ((b + j : ℕ) : ℝ)| ≤
      2 * (Real.sqrt u)⁻¹ := by
  set m := ⌈t0 u - b - 1 / 2⌉₊ with hm
  have h := sum_abs_sub_le_two_mul (fun j => gU u ((b + j : ℕ) : ℝ)) m N (G := (Real.sqrt u)⁻¹)
    (fun j => gU_nonneg _ _) (fun j => gU_le hu _) (fun j hj => ?_) (fun j hj => ?_)
  · simpa only [Nat.add_succ] using h
  · have hj' : (j : ℝ) < t0 u - b - 1 / 2 := Nat.lt_ceil.mp hj
    have := gU_le_succ hu (x := ((b + j : ℕ) : ℝ)) (by push_cast; linarith)
    rw [show b + (j + 1) = (b + j) + 1 by ring]
    push_cast at this ⊢
    exact this
  · have hj' : t0 u - b - 1 / 2 ≤ (j : ℝ) := Nat.ceil_le.mp hj
    have := gU_succ_le hu (x := ((b + j : ℕ) : ℝ)) (by push_cast; linarith)
    rw [show b + (j + 1) = (b + j) + 1 by ring]
    push_cast at this ⊢
    exact this

/-! ## Abel summation over the window -/

/-- **Abel summation of `g_u · Y` over the window**: if every partial sum of `Y` from the window's
left end is at most `B`, the window sum is at most `3B u^{-1/2}` (`‖g_u‖ ≤ u^{-1/2}` and the sharp
total-variation bound). -/
lemma norm_window_sum_le {u X : ℝ} (hR : Regime u X) (Y : ℕ → ℂ) {B : ℝ}
    (hY : ∀ n ≤ (Wset u X).card, ‖∑ k ∈ range n, Y (⌈t0 u - X⌉₊ + k)‖ ≤ B) :
    ‖∑ t ∈ Wset u X, (gU u t : ℂ) * Y t‖ ≤ B * (3 * (Real.sqrt u)⁻¹) := by
  have hu := hR.u_pos
  have hXu := hR.X_le_u
  have hT3 := hR.t0_ge
  set a := ⌈t0 u - X⌉₊ with ha
  set b := ⌊t0 u + X⌋₊ with hb
  set N := b + 1 - a with hN
  have hcard : (Wset u X).card = N := by rw [Wset, Nat.card_Icc]
  have ha1 : 1 ≤ a := by rw [ha, Nat.one_le_ceil_iff]; linarith
  have hB0 : 0 ≤ B := by simpa using hY 0 (Nat.zero_le _)
  set w : ℕ → ℂ := fun j => (gU u ((a + j - 1 : ℕ) : ℝ) : ℂ) with hw
  set y : ℕ → ℂ := fun j => Y (a + j - 1) with hy
  have hsum : ∑ t ∈ Wset u X, (gU u t : ℂ) * Y t = ∑ j ∈ Icc 1 N, w j * y j := by
    rw [Wset, sum_Icc_reindex]
  have hD : ∀ n ≤ N, ‖∑ i ∈ Icc 1 n, y i‖ ≤ B := by
    intro n hn
    have e : ∑ i ∈ Icc 1 n, y i = ∑ k ∈ range n, Y (a + k) := by
      rw [show Icc 1 n = Ico 1 (n + 1) by ext; simp, sum_Ico_eq_sum_range]
      simp only [hy, Nat.add_sub_cancel]
      exact sum_congr rfl fun k _ => by congr 1; omega
    rw [e]
    exact hY n (by rw [hcard]; exact hn)
  rw [hsum]
  refine (abel_bound w y N hD).trans ?_
  have hwN : ‖w N‖ ≤ (Real.sqrt u)⁻¹ := by
    simp only [hw]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gU_nonneg _ _)]
    exact gU_le hu _
  have htv : ∑ j ∈ range N, ‖w (j + 1) - w j‖ ≤ 2 * (Real.sqrt u)⁻¹ := by
    have h := tv_gU_le hu (a - 1) N
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl fun j _ => ?_
    simp only [hw]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    congr 4 <;> omega
  calc B * (‖w N‖ + ∑ j ∈ range N, ‖w (j + 1) - w j‖)
      ≤ B * ((Real.sqrt u)⁻¹ + 2 * (Real.sqrt u)⁻¹) := by gcongr
    _ = B * (3 * (Real.sqrt u)⁻¹) := by ring


/-! ## Assembly: the three reused error terms -/

/-- The kernel at any frequency after the three reused error terms of Theorem 4.1 (`err_tail`,
`err_extra`, `err_gauss`): what remains is the window sum `∑_W g_u(t) e^{-iηst} φ_{ρs}(h_t)`. -/
lemma norm_renewalR_le_window {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η s : ℝ) {u X : ℝ}
    (hR : Regime u X) (hX1 : 2 * ell / c ≤ X) :
    ‖renewalR ρ η s u‖ ≤
      8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) +
      50 * (Real.sqrt u)⁻¹ +
      ((Wset u X).card : ℝ) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) +
      ‖∑ t ∈ Wset u X, (gU u t : ℂ) * Yf ρ η s u t‖ := by
  classical
  have hu := hR.u_pos
  have hXT : X ≤ t0 u := by linarith [hR.X_le_u, hR.t0_ge]
  set W := Wset u X with hW
  set ph := cexp (-(((ρ * s * u / ell) : ℝ) : ℂ) * I) with hph
  set Etail := ∑' t : ℕ, (if t ∈ W then 0 else rinner ρ η s u t) with hEtail
  set Sex := ∑ t ∈ W, ∑ A ∈ Ioc ⌈hT u t⌉₊ (⌊hT u t⌋₊ + 1), rterm ρ η s u t A with hSex
  set Srt := ∑ t ∈ W, rterm ρ η s u t ⌈hT u t⌉₊ with hSrt
  set SwQ := ∑ t ∈ W, wR u (s * (ρ * θ + η)) t * qv (ρ * s) (hT u t) with hSwQ
  have e1 : renewalR ρ η s u = (Srt + Sex) + Etail := by
    rw [renewalR_eq, tsum_eq_sum_add_tsum_ite (summable_rinner ρ η s u) W]
    congr 1
    rw [hSrt, hSex, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => rinner_eq_add ρ η s u t
  have e2 : ph * SwQ = ∑ t ∈ W, (gU u t : ℂ) * Yf ρ η s u t := by
    rw [hSwQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => ph_wR_qv ρ η s u t
  have key : renewalR ρ η s u =
      Etail + Sex + (Srt - ph * SwQ) + ∑ t ∈ W, (gU u t : ℂ) * Yf ρ η s u t := by
    rw [e1, ← e2]; ring
  have b1 := err_tail ρ η s hu hX1 hR.X_le_u hXT
  have b2 := err_extra hθ ρ η s hR hXT
  have b3 := err_gauss ρ η s hR hXT
  rw [key]
  calc _ ≤ ‖Etail‖ + ‖Sex‖ + ‖Srt - ph * SwQ‖ + ‖∑ t ∈ W, (gU u t : ℂ) * Yf ρ η s u t‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ _ := by gcongr

/-! ## The window `X = √u log u` -/

/-- **The error terms at the window `X = √u log u`.** Eventually `Regime u X` and `2ℓ/c ≤ X`
hold, and the total of the three reused error terms and the Abel bound is at most
`C₂ u^{-ε/2} log u`, `ε = 1/(ϰ+1)`. -/
lemma fixedfreq_eventually {ϰ : ℝ} (hϰ : 1 ≤ ϰ) {A Q : ℝ} (hA : 0 ≤ A) (hQ : 0 ≤ Q) :
    ∀ᶠ u : ℝ in atTop,
      Regime u (Real.sqrt u * Real.log u) ∧ 2 * ell / c ≤ Real.sqrt u * Real.log u ∧
      8 * Real.exp (-(κW * (Real.sqrt u * Real.log u) / u * (Real.sqrt u * Real.log u) / 2)) *
          (1 + 2 / (κW * (Real.sqrt u * Real.log u) / u)) +
        50 * (Real.sqrt u)⁻¹ +
        (2 * (Real.sqrt u * Real.log u) + 1) *
          (66 * ((Real.sqrt u * Real.log u) ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) +
        (A * (2 * (Real.sqrt u * Real.log u) + 1) ^ (1 - 1 / (ϰ + 1)) + 2 * Q) *
          (3 * (Real.sqrt u)⁻¹) ≤
      (8 * (1 + 2 / κW) + 50 + 198 + 9 * A + 6 * Q) * u ^ (-(1 / (2 * (ϰ + 1)))) *
        Real.log u := by
  have hκ := κW_pos
  have hc := c_pos'
  have hl := ell_pos
  have e2 : ∀ᶠ u : ℝ in atTop, Real.log u ≤ u ^ ((1 : ℝ) / 10) := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (s := 1 / 10) 1 (by norm_num)).bound one_pos,
      eventually_ge_atTop 1] with u hu hu1
    rw [Real.rpow_one, one_mul, Real.norm_of_nonneg (Real.log_nonneg hu1),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hu
    exact hu
  have e3 : ∀ᶠ u : ℝ in atTop, Real.log u ^ 3 ≤ u ^ ((1 : ℝ) / 4) := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (s := 1 / 4) 3 (by norm_num)).bound one_pos,
      eventually_ge_atTop 1] with u hu hu1
    have hl0 := Real.log_nonneg hu1
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hl0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hu
    have e : Real.log u ^ (3 : ℝ) = Real.log u ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [← e]; exact hu
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 5), eventually_ge_atTop ((2 * ell / c) ^ 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (max (2 / κW) 1), e2, e3]
    with u hu8 hu2 hLk he2 he3
  have h85 : (1 : ℝ) ≤ 8 ^ 5 := by norm_num
  have hu0 : 0 < u := by linarith
  set s := Real.sqrt u with hs
  set L := Real.log u with hL
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
  have hss : s * s = u := Real.mul_self_sqrt hu0.le
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLk
  have hLk' : 2 / κW ≤ L := le_trans (le_max_left _ _) hLk
  have hkL : 2 ≤ κW * L := by rw [div_le_iff₀ hκ] at hLk'; linarith
  set ε := 1 / (ϰ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := by rw [hε, div_le_iff₀ (by linarith)]; linarith
  set P := s ^ (-ε) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hs0 _
  have hsrpow : s = u ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow u
  have hPu : u ^ (-(1 / (2 * (ϰ + 1)))) = P := by
    rw [hP, hsrpow, ← Real.rpow_mul hu0.le]
    congr 1
    rw [hε]
    field_simp
  have hsP : s⁻¹ ≤ P := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hs1e : s ^ (1 - ε) = s * P := by
    rw [hP, show 1 - ε = 1 + (-ε) by ring, Real.rpow_add hs0, Real.rpow_one]
  have hL3 : L ^ 3 ≤ s * P := by
    rw [← hs1e]
    calc L ^ 3 ≤ u ^ ((1 : ℝ) / 4) := he3
      _ = s ^ ((1 : ℝ) / 2) := by rw [hsrpow, ← Real.rpow_mul hu0.le]; norm_num
      _ ≤ s ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  -- `Regime` and the threshold
  have hreg : Regime u (s * L) := by
    refine ⟨hu8, le_mul_of_one_le_right hs0.le hL1, ?_⟩
    calc s * L ≤ u ^ ((1 : ℝ) / 2) * u ^ ((1 : ℝ) / 10) := by
          rw [← hsrpow]; exact mul_le_mul_of_nonneg_left he2 hs0.le
      _ = u ^ ((3 : ℝ) / 5) := by rw [← Real.rpow_add hu0]; norm_num
  have hX1 : 2 * ell / c ≤ s * L := by
    have : 2 * ell / c ≤ s := (Real.le_sqrt (by positivity) hu0.le).mpr hu2
    exact this.trans (le_mul_of_one_le_right hs0.le hL1)
  refine ⟨hreg, hX1, ?_⟩
  set X := s * L with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1' : 1 ≤ X := one_le_mul_of_one_le_of_one_le hs1 hL1
  -- the tail
  have hexpo : κW * X / u * X / 2 = κW * L ^ 2 / 2 := by
    rw [hX, ← hss]; field_simp
  have hexp1 : Real.exp (-(κW * X / u * X / 2)) ≤ (s * s)⁻¹ := by
    rw [hexpo, hss]
    have e : u⁻¹ = Real.exp (-L) := by rw [hL, Real.exp_neg, Real.exp_log hu0]
    rw [e]
    apply Real.exp_le_exp.mpr
    have hLL : L ≤ κW * L ^ 2 / 2 := by
      calc L = L * 2 / 2 := by ring
        _ ≤ L * (κW * L) / 2 := by gcongr
        _ = κW * L ^ 2 / 2 := by ring
    linarith
  have hfrac : 2 / (κW * X / u) ≤ 2 / κW * s := by
    have e : 2 / (κW * X / u) = 2 / κW * s / L := by
      rw [hX, ← hss]; field_simp
    rw [e]
    exact div_le_self (by positivity) hL1
  have hinv2 : (s * s)⁻¹ ≤ s⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hs0]; exact le_mul_of_one_le_right hs0.le hs1
  have hfr0 : 0 ≤ 2 / (κW * X / u) := div_nonneg (by norm_num) (div_nonneg (by positivity) hu0.le)
  have hk0 : 0 ≤ 2 / κW := div_nonneg (by norm_num) hκ.le
  have hT1 : 8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) ≤
      8 * (1 + 2 / κW) * s⁻¹ := by
    calc 8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u))
        ≤ 8 * (s * s)⁻¹ * (1 + 2 / κW * s) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp1 (by norm_num)) (by linarith [hfrac])
            (by linarith) (by positivity)
      _ = 8 * ((s * s)⁻¹ + 2 / κW * s⁻¹) := by field_simp
      _ ≤ 8 * (s⁻¹ + 2 / κW * s⁻¹) := by gcongr
      _ = 8 * (1 + 2 / κW) * s⁻¹ := by ring
  -- the Gaussian replacement
  have hX3 : X ^ 3 / u ^ 2 = L ^ 3 / s := by rw [hX, ← hss]; field_simp
  have hT3 : (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * s⁻¹) ≤ 198 * (L ^ 4 * s⁻¹) := by
    rw [hX3]
    calc (2 * X + 1) * (66 * (L ^ 3 / s) * s⁻¹) ≤ 3 * X * (66 * (L ^ 3 / s) * s⁻¹) := by
          gcongr; linarith
      _ = 198 * (L ^ 4 * s⁻¹) := by rw [hX]; field_simp; norm_num
  -- the Abel term
  have hpow : (2 * X + 1) ^ (1 - ε) ≤ 3 * (s * P) * L := by
    have h1 : (2 * X + 1) ^ (1 - ε) ≤ (3 * X) ^ (1 - ε) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h2 : (3 * X) ^ (1 - ε) = (3 : ℝ) ^ (1 - ε) * s ^ (1 - ε) * L ^ (1 - ε) := by
      rw [hX, ← mul_assoc, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 3 * s) (by linarith : (0 : ℝ) ≤ L),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hs0.le]
    have h3 : (3 : ℝ) ^ (1 - ε) ≤ 3 := by
      calc (3 : ℝ) ^ (1 - ε) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    have h4 : L ^ (1 - ε) ≤ L := by
      calc L ^ (1 - ε) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
        _ = L := Real.rpow_one L
    rw [h2, hs1e] at h1
    calc (2 * X + 1) ^ (1 - ε) ≤ (3 : ℝ) ^ (1 - ε) * (s * P) * L ^ (1 - ε) := h1
      _ ≤ 3 * (s * P) * L := by
          have : 0 ≤ (3 : ℝ) ^ (1 - ε) := by positivity
          have : 0 ≤ L ^ (1 - ε) := by positivity
          gcongr
  have hT4 : (A * (2 * X + 1) ^ (1 - ε) + 2 * Q) * (3 * s⁻¹) ≤ 9 * A * (P * L) + 6 * Q * s⁻¹ := by
    calc (A * (2 * X + 1) ^ (1 - ε) + 2 * Q) * (3 * s⁻¹)
        ≤ (A * (3 * (s * P) * L) + 2 * Q) * (3 * s⁻¹) := by gcongr
      _ = 9 * A * (P * L) + 6 * Q * s⁻¹ := by field_simp; ring
  -- collecting
  have hPL : P ≤ P * L := le_mul_of_one_le_right hP0.le hL1
  have hsPL : s⁻¹ ≤ P * L := hsP.trans hPL
  have hL4 : L ^ 4 * s⁻¹ ≤ P * L := by
    calc L ^ 4 * s⁻¹ = L * (L ^ 3 * s⁻¹) := by ring
      _ ≤ L * (s * P * s⁻¹) := by gcongr
      _ = P * L := by field_simp
  have hc1 : 0 ≤ 8 * (1 + 2 / κW) := by positivity
  have f1 : 8 * (1 + 2 / κW) * s⁻¹ ≤ 8 * (1 + 2 / κW) * (P * L) :=
    mul_le_mul_of_nonneg_left hsPL hc1
  have f4 : 6 * Q * s⁻¹ ≤ 6 * Q * (P * L) := mul_le_mul_of_nonneg_left hsPL (by positivity)
  rw [hPu]
  linarith only [hT1, hT3, hT4, f1, f4, hsPL, hL4]

/-! ## Roots of unity -/

/-- `e^{-2πik/Q} = 1` forces `Q ∣ k`. -/
lemma dvd_of_cexp_eq_one {k : ℤ} {Q : ℕ} (hQ : 0 < Q)
    (h : cexp (-((2 * π * k / Q : ℝ) : ℂ) * I) = 1) : (Q : ℤ) ∣ k := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have h1 : ((-(2 * π * k / Q) : ℝ) : ℂ) = ((2 * π * n : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast at hn ⊢
    linear_combination hn
  have h2 : -(2 * π * k / Q) = 2 * π * n := by exact_mod_cast h1
  have h4 : (k : ℝ) = -(n * Q) := by
    field_simp at h2
    linarith
  have h5 : k = -(n * Q) := by exact_mod_cast h4
  exact ⟨-n, by rw [h5]; ring⟩

/-- `e^{-i (2πm/Q) Q} = 1` for an integer `m`. -/
lemma cexp_mul_eq_one (m : ℤ) {Q : ℕ} (hQ : 0 < Q) :
    cexp (-((2 * π * m / Q * Q : ℝ) : ℂ) * I) = 1 := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [show (-((2 * π * m / Q * Q : ℝ) : ℂ) * I) = ((-m : ℤ) : ℂ) * (2 * π * I) by
    rw [div_mul_cancel₀ _ hQ']; push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-! ## Proposition 4.5 -/

/-- **Proposition 4.5 [`prop:fixedfreq`] (fixed-frequency decay).** For nonnegative integers
`ρ, η` with `gcd(ρ, η) = 1`, `Q₀ ≥ 2` and `s = 2πr/Q₀` with `gcd(r, Q₀) = 1`:
`R^{ρ,η}_s(u) = O_{Q₀,ρ,η}(u^{-ε/2} log u)` for `u ≥ 2`, `ε = 1/(ϰ+1)`. The constant depends on
`d, ϰ, ρ, η, Q₀` and is uniform in `r`. -/
theorem fixedfreq {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η : ℕ) (hco : Nat.Coprime ρ η)
    (Q₀ : ℕ) (hQ : 2 ≤ Q₀) :
    ∃ C : ℝ, ∀ r : ℤ, Int.gcd r Q₀ = 1 → ∀ u : ℝ, 2 ≤ u →
      ‖renewalR ρ η (2 * π * r / Q₀) u‖ ≤ C * u ^ (-(1 / (2 * (ϰ + 1)))) * Real.log u := by
  have hd := hθ.1
  have hϰ : 1 ≤ ϰ := hθ.2.1
  have hQ1 : 1 ≤ Q₀ := by omega
  have hQpos : 0 < Q₀ := by omega
  have hQ0 : (0 : ℝ) < Q₀ := by exact_mod_cast hQpos
  have hexp : 0 ≤ 1 - 1 / (ϰ + 1) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  obtain ⟨B₀, hB₀⟩ := renewalR_bounded
  set A : ℝ := Q₀ * (Q₀ * (12 * d ^ (-(1 / ϰ)) + 14) * (2 + 4 * Q₀)) with hA
  have hA0 : 0 ≤ A := by have := Real.rpow_nonneg hd.le (-(1 / ϰ)); positivity
  set C₂ : ℝ := 8 * (1 + 2 / κW) + 50 + 198 + 9 * A + 6 * Q₀ with hC₂
  have hC₂0 : 0 ≤ C₂ := by have := κW_pos; positivity
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (fixedfreq_eventually hϰ hA0 hQ0.le)
  set u₁ := max u₀ 2 with hu₁
  set e : ℝ := 1 / (2 * (ϰ + 1)) with he
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C₂ (|B₀| * u₁ ^ e / Real.log 2), fun r hr u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hlog : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hpow0 : 0 < u ^ (-e) := Real.rpow_pos_of_pos hu0 _
  by_cases hbig : u₁ ≤ u
  · -- the main range: the window `X = √u log u`
    obtain ⟨hR, hX1, hE⟩ := hu₀ u (le_trans (le_max_left _ _) hbig)
    set s : ℝ := 2 * π * r / Q₀ with hs
    set X := Real.sqrt u * Real.log u with hX
    have hXT : X ≤ t0 u := by linarith [hR.X_le_u, hR.t0_ge]
    -- `e^{-iρsQ₀} = e^{-iηsQ₀} = 1`
    have hρQ : cexp (-(((ρ : ℝ) * s * Q₀ : ℝ) : ℂ) * I) = 1 := by
      rw [show ((ρ : ℝ) * s * Q₀ : ℝ) = 2 * π * ((ρ * r : ℤ) : ℝ) / Q₀ * Q₀ by
        rw [hs]; push_cast; ring]
      exact cexp_mul_eq_one _ hQpos
    have hηQ : cexp (-(((η : ℝ) * s * Q₀ : ℝ) : ℂ) * I) = 1 := by
      rw [show ((η : ℝ) * s * Q₀ : ℝ) = 2 * π * ((η * r : ℤ) : ℝ) / Q₀ * Q₀ by
        rw [hs]; push_cast; ring]
      exact cexp_mul_eq_one _ hQpos
    have hrQ : Int.gcd (Q₀ : ℤ) r = 1 := by rw [Int.gcd_comm]; exact hr
    -- the class means cancel
    have hcase : (∫ x in (0 : ℝ)..1, psiF ((ρ : ℝ) * s) Q₀ x) *
        ∑ i ∈ range Q₀, cexp (-(((η : ℝ) * s * i : ℝ) : ℂ) * I) = 0 := by
      by_cases hdiv : Q₀ ∣ ρ
      · -- `Q₀ ∣ ρ`, so `Q₀ ∤ η`, and the phases are nontrivial `Q₀`-th roots of unity
        set ζ := cexp (-(((η : ℝ) * s : ℝ) : ℂ) * I) with hζ
        have hζ1 : ζ ≠ 1 := by
          intro h
          have h' : cexp (-((2 * π * ((η * r : ℤ) : ℝ) / Q₀ : ℝ) : ℂ) * I) = 1 := by
            rw [show (2 * π * ((η * r : ℤ) : ℝ) / Q₀ : ℝ) = (η : ℝ) * s by rw [hs]; push_cast; ring]
            exact h
          have hηd : (Q₀ : ℤ) ∣ (η : ℤ) :=
            Int.dvd_of_dvd_mul_left_of_gcd_one (dvd_of_cexp_eq_one hQpos h') hrQ
          have hη : Q₀ ∣ η := Int.natCast_dvd_natCast.mp hηd
          have h1 : Q₀ ∣ 1 := by rw [← hco]; exact Nat.dvd_gcd hdiv hη
          have := Nat.le_of_dvd one_pos h1
          omega
        have hpow : ∀ i : ℕ, cexp (-(((η : ℝ) * s * i : ℝ) : ℂ) * I) = ζ ^ i := by
          intro i
          rw [hζ, ← Complex.exp_nat_mul]
          congr 1
          push_cast; ring
        have hζQ : ζ ^ Q₀ = 1 := by rw [← hpow]; exact hηQ
        rw [Finset.sum_congr rfl fun i _ => hpow i, geom_sum_eq hζ1, hζQ, sub_self, zero_div,
          mul_zero]
      · -- `Q₀ ∤ ρ`: the mean of `ψ` vanishes
        have hρ1 : cexp (-(((ρ : ℝ) * s : ℝ) : ℂ) * I) ≠ 1 := by
          intro h
          have h' : cexp (-((2 * π * ((ρ * r : ℤ) : ℝ) / Q₀ : ℝ) : ℂ) * I) = 1 := by
            rw [show (2 * π * ((ρ * r : ℤ) : ℝ) / Q₀ : ℝ) = (ρ : ℝ) * s by rw [hs]; push_cast; ring]
            exact h
          exact hdiv (Int.natCast_dvd_natCast.mp
            (Int.dvd_of_dvd_mul_left_of_gcd_one (dvd_of_cexp_eq_one hQpos h') hrQ))
        rw [integral_psiF_eq_zero hQ1 hρQ hρ1, zero_mul]
    -- the partial sums and the window sum
    have hcard : ((Wset u X).card : ℝ) ≤ 2 * X + 1 := card_Wset_le hR.X_pos.le hXT
    have hpart : ∀ n ≤ (Wset u X).card, ‖∑ k ∈ range n, Yf ρ η s u (⌈t0 u - X⌉₊ + k)‖ ≤
        A * (2 * X + 1) ^ (1 - 1 / (ϰ + 1)) + 2 * Q₀ := by
      intro n hn
      refine (norm_partial_Yf_le hθ ρ η s u hQ1 hρQ hηQ hcase _ n).trans ?_
      have hn' : (n : ℝ) ≤ 2 * X + 1 := le_trans (by exact_mod_cast hn) hcard
      have : (n : ℝ) ^ (1 - 1 / (ϰ + 1)) ≤ (2 * X + 1) ^ (1 - 1 / (ϰ + 1)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hn' hexp
      rw [← hA]
      have := mul_le_mul_of_nonneg_left this hA0
      linarith
    have hwin := norm_window_sum_le hR (Yf ρ η s u) hpart
    have hmain := norm_renewalR_le_window hθ ρ η s hR hX1
    have h66 : 0 ≤ 66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹ := by
      have := hR.X_pos; positivity
    calc ‖renewalR ρ η s u‖
        ≤ 8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) +
          50 * (Real.sqrt u)⁻¹ +
          ((Wset u X).card : ℝ) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) +
          ‖∑ t ∈ Wset u X, (gU u t : ℂ) * Yf ρ η s u t‖ := hmain
      _ ≤ 8 * Real.exp (-(κW * X / u * X / 2)) * (1 + 2 / (κW * X / u)) +
          50 * (Real.sqrt u)⁻¹ +
          (2 * X + 1) * (66 * (X ^ 3 / u ^ 2) * (Real.sqrt u)⁻¹) +
          (A * (2 * X + 1) ^ (1 - 1 / (ϰ + 1)) + 2 * Q₀) * (3 * (Real.sqrt u)⁻¹) := by
          have := mul_le_mul_of_nonneg_right hcard h66
          linarith
      _ ≤ C₂ * u ^ (-e) * Real.log u := hE
      _ ≤ max C₂ (|B₀| * u₁ ^ e / Real.log 2) * u ^ (-e) * Real.log u := by
          have : 0 ≤ Real.log u := by linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0.le) this
  · -- the bounded range `2 ≤ u < u₁`
    push Not at hbig
    have hu₁0 : 0 < u₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have h1 : u₁ ^ (-e) ≤ u ^ (-e) :=
      Real.rpow_le_rpow_of_nonpos hu0 hbig.le (by rw [he]; have : 0 < ϰ + 1 := by linarith
                                                  have : 0 ≤ 1 / (2 * (ϰ + 1)) := by positivity
                                                  linarith)
    have h2 : |B₀| = |B₀| * u₁ ^ e / Real.log 2 * (u₁ ^ (-e) * Real.log 2) := by
      rw [Real.rpow_neg hu₁0.le]
      have : 0 < u₁ ^ e := Real.rpow_pos_of_pos hu₁0 _
      field_simp
    have hnn : 0 ≤ |B₀| * u₁ ^ e / Real.log 2 := by
      have : 0 < u₁ ^ e := Real.rpow_pos_of_pos hu₁0 _
      positivity
    calc ‖renewalR ρ η (2 * π * r / Q₀) u‖ ≤ |B₀| := (hB₀ _ _ _ _).trans (le_abs_self _)
      _ = |B₀| * u₁ ^ e / Real.log 2 * (u₁ ^ (-e) * Real.log 2) := h2
      _ ≤ max C₂ (|B₀| * u₁ ^ e / Real.log 2) * (u ^ (-e) * Real.log u) := by
          apply mul_le_mul (le_max_right _ _) _ (by positivity) (le_trans hnn (le_max_right _ _))
          exact mul_le_mul h1 hlog hlog2.le hpow0.le
      _ = max C₂ (|B₀| * u₁ ^ e / Real.log 2) * u ^ (-e) * Real.log u := by ring

end CollatzCLT
