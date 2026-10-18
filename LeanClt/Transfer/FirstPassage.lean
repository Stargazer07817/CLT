import LeanClt.Transfer.Large
import LeanClt.Transfer.Transport

/-!
# Lemma 5.2 (orbit approximation) and Lemma 5.4 (converse)

* `orbit_window` (Lemma 5.2): for `N_Y` typical, the first crossing `h = T_x(N)` satisfies
  `m ≤ h ≤ n₀`, the early depth `r = h - m` lies in `J_Y`, and the backtracked point
  `M = U^r(N)` lies in `𝓜_x`.
* `converse` (Lemma 5.4): if `r ≤ n₀`, the prefix of length `r` is typical, and `U^r(N) ∈ 𝓜_x`,
  then `T_x(N) = r + m`.
-/

open Real Finset Function

namespace CollatzCLT

lemma passT_spec {x : ℝ} {N : ℕ} (h : crosses x N) : (U^[passT x N] N : ℝ) ≤ x :=
  Nat.sInf_mem (s := {r : ℕ | (U^[r] N : ℝ) ≤ x}) h

lemma passT_le {x : ℝ} {N k : ℕ} (hk : (U^[k] N : ℝ) ≤ x) : passT x N ≤ k :=
  Nat.sInf_le (show k ∈ {r : ℕ | (U^[r] N : ℝ) ≤ x} from hk)

lemma passT_eq {x : ℝ} {N k : ℕ} (hk : (U^[k] N : ℝ) ≤ x) (hlt : ∀ j < k, x < U^[j] N) :
    crosses x N ∧ passT x N = k := by
  refine ⟨⟨k, hk⟩, le_antisymm (passT_le hk) ?_⟩
  by_contra h
  push Not at h
  have := hlt _ h
  have := passT_spec ⟨k, hk⟩
  linarith

lemma mem_oddClosed {Y : ℝ} {N : ℕ} (hY : 0 ≤ Y) (hN : N ∈ oddClosed Y) :
    Odd N ∧ Y ≤ N ∧ (N : ℝ) ≤ 2 * Y := by
  unfold oddClosed at hN
  rw [Finset.mem_filter, Finset.mem_Icc] at hN
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN
  refine ⟨h3, (Nat.ceil_le.mp h1), ?_⟩
  exact (Nat.le_floor_iff (by linarith)).mp h2

/-- The orbit error is at most `1` along a typical prefix. -/
lemma orbit_err_le {x : ℝ} (hL : Large x) {N : ℕ} (hNx : x ^ alpha ≤ N) {j : ℕ}
    (hj : j ≤ n0 x) (hS : (Swd N j : ℝ) ≤ 2 * j + Lx x ^ (0.6 : ℝ)) :
    (2 : ℝ) ^ Swd N j / (2 ^ j * N) ≤ 1 := by
  have hx0 : 0 < x := by linarith [hL.x_gt]
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hNx
  have h2 : ∀ k : ℕ, (2 : ℝ) ^ k = Real.exp (k * ell) := by
    intro k; rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]; rfl
  rw [div_le_one (by positivity), h2, h2]
  calc Real.exp (Swd N j * ell) ≤ Real.exp ((j + Lx x ^ (0.6 : ℝ)) * ell + j * ell) := by
        apply Real.exp_le_exp.mpr
        nlinarith [ell_pos]
    _ = Real.exp (j * ell + Lx x ^ (0.6 : ℝ) * ell) * Real.exp (j * ell) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (alpha * Lx x) * Real.exp (j * ell) := by
        gcongr
        have hjn : (j : ℝ) ≤ n0 x := by exact_mod_cast hj
        have := hL.err
        nlinarith [ell_pos]
    _ ≤ N * Real.exp (j * ell) := by
        gcongr
        rw [← rpow_eq_exp_Lx hx0]; exact hNx
    _ = Real.exp (j * ell) * N := by ring

/-- **Logarithmic orbit bounds along a typical prefix.** -/
lemma log_U_bounds {x : ℝ} (hL : Large x) {N : ℕ} (hN : Odd N) (hNx : x ^ alpha ≤ N) {j : ℕ}
    (hj : j ≤ n0 x) (hS : |(Swd N j : ℝ) - 2 * j| ≤ Lx x ^ (0.6 : ℝ)) :
    Real.log N - c * j - ell * Lx x ^ (0.6 : ℝ) ≤ Real.log (U^[j] N) ∧
      Real.log (U^[j] N) ≤ Real.log N - c * j + ell * Lx x ^ (0.6 : ℝ) + 1 := by
  obtain ⟨h0, h1⟩ := orbit_log hN j
  have herr := orbit_err_le hL hNx hj (by linarith [(abs_le.mp hS).2])
  have hl := ell_pos
  have habs := abs_le.mp hS
  constructor
  · nlinarith
  · nlinarith

lemma x_lt_rpow_alpha {x : ℝ} (hx : 1 < x) : x < x ^ alpha := by
  calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ < x ^ alpha := Real.rpow_lt_rpow_of_exponent_lt hx (by unfold alpha; norm_num)

lemma log_rpow_Lx {x : ℝ} (hx : 0 < x) (a : ℝ) : Real.log (x ^ a) = a * Lx x := by
  rw [Real.log_rpow hx]; rfl

/-- **Lemma 5.2 (orbit approximation).** For a typical source `N ∈ [Y, 2Y]`: the first crossing
`h = T_x(N)` is finite with `m ≤ h ≤ n₀`, the depth `r = h - m` lies in `J_Y`, and the backtracked
point `U^r(N)` lies in `𝓜_x`. -/
theorem orbit_window {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    {N : ℕ} (hN : N ∈ oddClosed Y) (hG : Good x N) :
    crosses x N ∧ mT x ≤ passT x N ∧ passT x N ≤ n0 x ∧ passT x N - mT x ∈ JY x Y ∧
      U^[passT x N - mT x] N ∈ Mset x := by
  have hx1 := hL.x_gt
  have hx0 : 0 < x := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hY1
  obtain ⟨hNo, hNY, hN2Y⟩ := mem_oddClosed hY0.le hN
  have hNx : x ^ alpha ≤ N := hY1.trans hNY
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hY0 hNY
  set L := Lx x with hLdef
  have hc := c_pos'; have hl := ell_pos
  have hbd : ∀ j ≤ n0 x, Real.log N - c * j - ell * L ^ (0.6 : ℝ) ≤ Real.log (U^[j] N) ∧
      Real.log (U^[j] N) ≤ Real.log N - c * j + ell * L ^ (0.6 : ℝ) + 1 :=
    fun j hj => log_U_bounds hL hNo hNx hj (hG j hj)
  have hlogY : Real.log Y ≤ Real.log N := Real.log_le_log hY0 hNY
  have hlogN2 : Real.log N ≤ ell + Real.log Y := by
    have := Real.log_le_log hN0 hN2Y
    rw [Real.log_mul (by norm_num) hY0.ne'] at this; unfold ell; linarith
  have hlogYa : alpha * L ≤ Real.log Y := by
    rw [← log_rpow_Lx hx0]; exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hY1
  have hlogYb : Real.log Y ≤ alpha ^ 2 * L := by
    rw [← log_rpow_Lx hx0]; exact Real.log_le_log hY0 hY2
  have hUpos : ∀ j, (0 : ℝ) < U^[j] N := fun j => by exact_mod_cast (odd_U_iterate hNo j).pos
  have hlogx : Real.log x = L := rfl
  -- (i) the orbit is below `x` at time `n₀`
  have hcross_n : (U^[n0 x] N : ℝ) ≤ x := by
    have h := (hbd (n0 x) le_rfl).2
    have := hL.cross
    have hlt : Real.log (U^[n0 x] N) < Real.log x := by rw [hlogx]; linarith
    exact ((Real.log_lt_log_iff (hUpos _) hx0).mp hlt).le
  have hcr : crosses x N := ⟨n0 x, hcross_n⟩
  set h := passT x N with hh
  have hhn : h ≤ n0 x := passT_le hcross_n
  have hUh : (U^[h] N : ℝ) ≤ x := passT_spec hcr
  -- (ii) `h ≥ 1` and the two-sided bound on `c h`
  have hh1 : 1 ≤ h := by
    by_contra h0
    push Not at h0
    have : h = 0 := by omega
    rw [this] at hUh
    simp only [iterate_zero, id_eq] at hUh
    have := x_lt_rpow_alpha hx1
    linarith
  have hlo : Real.log N - c * h - ell * L ^ (0.6 : ℝ) ≤ L := by
    have := (hbd h hhn).1
    have : Real.log (U^[h] N) ≤ Real.log x := Real.log_le_log (hUpos _) hUh
    linarith
  have hhi : L < Real.log N - c * h + ell * L ^ (0.6 : ℝ) + 1 + c := by
    have hlt : x < U^[h - 1] N := lt_of_lt_passT (by omega)
    have h1 := Real.log_lt_log hx0 hlt
    have h2 := (hbd (h - 1) (by omega)).2
    have hcast : ((h - 1 : ℕ) : ℝ) = h - 1 := by rw [Nat.cast_sub hh1]; simp
    rw [hcast] at h2
    linarith
  -- (iii) the window
  have hrY : rY x Y = (Real.log Y - L) / c - mT x := by
    unfold rY; rw [Real.log_div hY0.ne' hx0.ne']; rfl
  have hwin : |(h : ℝ) - mT x - rY x Y| ≤ 2 * L ^ (0.8 : ℝ) := by
    rw [hrY]
    have hw := hL.hwin
    rw [← hLdef] at hw
    have hB := (div_le_iff₀ hc).mp hw
    rw [show (h : ℝ) - mT x - ((Real.log Y - L) / c - mT x) = (c * h - (Real.log Y - L)) / c by
      field_simp; ring, abs_le]
    have h06 : 0 ≤ L ^ (0.6 : ℝ) := Real.rpow_nonneg (by linarith [hL.L_ge]) _
    constructor
    · rw [le_div_iff₀ hc]; nlinarith
    · rw [div_le_iff₀ hc]; nlinarith
  have hhm : mT x ≤ h := by
    have h1 : rY x Y ≥ (alpha - 1) * L / c - mT x := by
      rw [hrY]; gcongr; linarith
    have := hL.jlow
    have := (abs_le.mp hwin).1
    have : (mT x : ℝ) ≤ h := by linarith
    exact_mod_cast this
  set r := h - mT x with hr
  have hrc : (r : ℝ) = h - mT x := by rw [hr, Nat.cast_sub hhm]
  have hrJ : r ∈ JY x Y := by
    unfold JY
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [hrc]; exact hwin⟩
  refine ⟨hcr, hhm, hhn, hrJ, ?_⟩
  -- (iv) the backtracked point
  have hrh : r + mT x = h := by omega
  have hUm : (U^[mT x] (U^[r] N) : ℝ) ≤ x := by
    rw [← iterate_add_apply, add_comm, hrh]; exact hUh
  have hpass : crosses x (U^[r] N) ∧ passT x (U^[r] N) = mT x := by
    refine passT_eq hUm (fun j hj => ?_)
    rw [← iterate_add_apply]
    exact lt_of_lt_passT (by omega)
  refine ⟨odd_U_iterate hNo r, hpass.1, hpass.2, ?_⟩
  have hbr := hbd r (by omega)
  rw [hrc] at hbr
  have hmw := hL.mwin
  rw [abs_le]
  constructor <;> nlinarith [hbr.1, hbr.2, hlo, hhi]

/-- **Lemma 5.4 (converse).** If `r ≤ n₀`, the prefix of length `r` of `N ≥ x^α` is typical, and
`U^r(N) ∈ 𝓜_x`, then every `U^j(N)`, `j < r + m`, exceeds `x`, so `T_x(N) = r + m`. -/
theorem converse {x : ℝ} (hL : Large x) {N : ℕ} (hNo : Odd N) (hNx : x ^ alpha ≤ N) {r : ℕ}
    (hr : r ≤ n0 x) (hG : ∀ j ≤ r, |(Swd N j : ℝ) - 2 * j| ≤ Lx x ^ (0.6 : ℝ))
    (hM : U^[r] N ∈ Mset x) : crosses x N ∧ passT x N = r + mT x := by
  have hx0 : 0 < x := by linarith [hL.x_gt]
  have hc := c_pos'; have hl := ell_pos
  obtain ⟨-, hMcr, hMpass, hMwin⟩ := hM
  have hUpos : ∀ j, (0 : ℝ) < U^[j] N := fun j => by exact_mod_cast (odd_U_iterate hNo j).pos
  have hbd : ∀ j ≤ r, Real.log N - c * j - ell * Lx x ^ (0.6 : ℝ) ≤ Real.log (U^[j] N) ∧
      Real.log (U^[j] N) ≤ Real.log N - c * j + ell * Lx x ^ (0.6 : ℝ) + 1 :=
    fun j hj => log_U_bounds hL hNo hNx (hj.trans hr) (hG j hj)
  have hMlow := (abs_le.mp hMwin).1
  have hconv := hL.conv
  refine passT_eq (by rw [add_comm, iterate_add_apply, ← hMpass]; exact passT_spec hMcr)
    (fun j hj => ?_)
  by_cases hjr : j ≤ r
  · -- along the early segment the orbit stays above `M`'s level minus `O(L^{0.6})`
    have h1 := (hbd j hjr).1
    have h2 := (hbd r le_rfl).2
    have hjr' : (j : ℝ) ≤ r := by exact_mod_cast hjr
    have hlog : Real.log x < Real.log (U^[j] N) := by
      change Lx x < _
      nlinarith
    exact (Real.log_lt_log_iff hx0 (hUpos _)).mp hlog
  · push Not at hjr
    have : U^[j] N = U^[j - r] (U^[r] N) := by rw [← iterate_add_apply]; congr 1; omega
    rw [this]
    exact lt_of_lt_passT (by omega)

end CollatzCLT
