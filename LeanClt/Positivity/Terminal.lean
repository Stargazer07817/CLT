import LeanClt.Positivity.Cauchy

/-!
# §8.4: terminal blocks, the terminal marked mass and Lemma 8.8

At scale `b` and endpoint `R`, `L_b(R) = (4/3)^b R/(4·2^{r_b})` and `U_b(R) = 2^{2r_b} L_b(R)`
(`Lb`, `Ub`); for `L_b(R) < X ≤ U_b(R)` the selected shift `u = shiftOf b R X` is the least `u` with
`2^u L_b(R) ≥ X`, so `1 ≤ u ≤ 2r_b` and `X ≤ 2^u L_b(R) < 2X` (`shiftOf_spec`). `X` is
**admissible** at generation `n` if `L_{b_n}(R) < X ≤ U_{b_n}(R)` for every generation-`n` endpoint
`R` (`Admissible`). Terminal blocks with shift `u` (`IsTerminal`, `terminal`, §8.4) first cross the
shifted barrier `H_b(s) + u - r_b` (`tbar`) at a depth in `(ℓ_b, h_b]`, with overshoot `≤ K`.

* **The terminal rejection bound** `terminal_rejection`: for `b ≥ 200`, `u ≤ 2r_b` and every `K`,
  `1 - p(terminal b K u) ≤ 4 exp(-e_b²/(6b)) + 2^{-K-1}`. As in the paper: at depth `ℓ_b` the shifted
  barrier is exactly `2e_b + u` above the mean `2ℓ_b`, at depth `h_b` exactly `2e_b + 2r_b - u` below
  the mean `2h_b`; Lemma 2.2(i) at these two depths, and the first-crossing split
  (`prob_overshoot`) for the overshoot, summed over the disjoint first-crossing depths. The
  first-crossing events are restated for an arbitrary barrier (`CrossAtG`, `OverAtG`).
* **(8.5) for terminal blocks** `phi_bounds_terminal`: `2^u L_b(R) ≤ Φ_w(R) ≤ 2^{u+K+3} L_b(R)` for
  `R ≥ 2^{b+1}`; with `X ≤ 2^u L_b(R) < 2X` this gives `X ≤ Φ_w(R) < 2^{K+4} X`, the source of (8.10)
  once the overshoot is reduced to at most `1` (§8.5).
* **The spread bound** `endpt_bounds`, `spread_bound`: every generation-`n` endpoint lies in
  `[lo_n M, hi_n M]` with `lo_n = ∏_{j<n} (4/3)^{b_j}/4`, `hi_n = ∏_{j<n} 2^{K_j+1}(4/3)^{b_j}`
  (by (8.5)), so mutual ratios are at most `2^{σ_n}`, `σ_n = ∑_{j<n} (K_j + 3)`.
* **The terminal marked mass** (the unlabelled paragraph of §8.4) `terminal_mass`, and
  **Lemma 8.8 [`lem:allscales`]** `allscales`; its proof does not use the nonemptiness hypothesis,
  and `allscales_of_bounds` is the same statement without it.
-/

open Finset Real Filter

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Definitions -/

/-- `L_b(R) = (4/3)^b R/(4·2^{r_b})`. -/
def Lb (b R : ℕ) : ℝ := (4 / 3 : ℝ) ^ b * R / (4 * 2 ^ rB b)

/-- `U_b(R) = 2^{2 r_b} L_b(R)`. -/
def Ub (b R : ℕ) : ℝ := 2 ^ (2 * rB b) * Lb b R

/-- The selected shift: the least `u` with `2^u L_b(R) ≥ X`. -/
def shiftOf (b R : ℕ) (X : ℝ) : ℕ := ⌈Real.logb 2 (X / Lb b R)⌉₊

/-- `X` is admissible for every generation-`n` endpoint. -/
def Admissible (b0 M n : ℕ) (X : ℝ) : Prop :=
  ∀ H ∈ hist b0 M n, Lb (bseq b0 n) (endpt M H) < X ∧ X ≤ Ub (bseq b0 n) (endpt M H)

open Classical in
/-- The terminal marked mass at generation `n` and scale `X`: each history continues with the
terminal blocks of its selected shift, marked by `ρ_{k_n}` at the terminal source. -/
def termMass (b0 M n : ℕ) (X : ℝ) : ℝ :=
  ∑ H ∈ hist b0 M n, wt H.flatten *
    ∑ w ∈ terminal (bseq b0 n) (Kseq n) (shiftOf (bseq b0 n) (endpt M H) X),
      if Realizes w (endpt M H) then wt w * rhoX (kseq b0 n) (src w (endpt M H)) else 0

/-- The shifted barrier `H_b(s) + u - r_b`. -/
def tbar (b u s : ℕ) : ℤ := barrier b s + u - rB b

lemma isTerminal_iff {b K u : ℕ} {w : Word} :
    IsTerminal b K u w ↔ FirstCross (lB b) (tbar b u) K w ∧ w.length ≤ hB b := Iff.rfl

/-! ## Numerical facts -/

/-- `r_b` is exact (the truncated subtraction never truncates): `r_b + B(w_b) + 2e_b = 2w_b`. -/
lemma rB_add (b : ℕ) : rB b + Bc (wB b) + 2 * eB b = 2 * wB b := by
  have := five_mul_Bc_le (wB b)
  unfold rB wB eB at *
  omega

/-- `41 B(t) ≤ 65 t + 40`, from `3^{41} ≤ 2^{65}`. -/
lemma forty_one_mul_Bc_le (t : ℕ) : 41 * Bc t ≤ 65 * t + 40 := by
  set c := (65 * t + 40) / 41 with hc
  have hc' : 65 * t ≤ 41 * c := by omega
  have h : 3 ^ t ≤ 2 ^ c := by
    have h41 : (3 ^ t) ^ 41 ≤ (2 ^ c) ^ 41 := by
      calc (3 ^ t) ^ 41 = (3 ^ 41) ^ t := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 ^ 65) ^ t := Nat.pow_le_pow_left (by norm_num) t
        _ = 2 ^ (65 * t) := by rw [← pow_mul]
        _ ≤ 2 ^ (41 * c) := Nat.pow_le_pow_right (by norm_num) hc'
        _ = (2 ^ c) ^ 41 := by rw [← pow_mul, mul_comm]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h41
  have := Bc_le_of_le h
  omega

/-- `19 t ≤ 12 B(t)`, from `2^{19} ≤ 3^{12}`. -/
lemma nineteen_mul_le_Bc (t : ℕ) : 19 * t ≤ 12 * Bc t := by
  have h1 : 2 ^ (19 * t) ≤ 2 ^ (12 * Bc t) := by
    calc 2 ^ (19 * t) = (2 ^ 19) ^ t := by rw [← pow_mul]
      _ ≤ (3 ^ 12) ^ t := Nat.pow_le_pow_left (by norm_num) t
      _ = (3 ^ t) ^ 12 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ Bc t) ^ 12 := Nat.pow_le_pow_left (three_pow_le_two_pow_Bc t) 12
      _ = 2 ^ (12 * Bc t) := by rw [← pow_mul, mul_comm]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

lemma barrier_nonneg (b s : ℕ) : 0 ≤ barrier b s := by
  unfold barrier
  have := Bc_le_two_mul (b - s)
  omega

lemma tbar_mono (b u : ℕ) {j s : ℕ} (h : j ≤ s) : tbar b u j ≤ tbar b u s := by
  unfold tbar; have := barrier_mono b h; omega

/-! ## First crossings of an arbitrary barrier -/

/-- Below the barrier `Hs` at every depth `l ≤ j ≤ k`. -/
def BelowG (l : ℕ) (Hs : ℕ → ℤ) (k : ℕ) (u : Word) : Prop :=
  l ≤ k ∧ ∀ j ∈ Icc l k, (pre u j : ℤ) < Hs j

/-- The gap `Hs(k+1) - A_k` to the barrier at depth `k + 1`. -/
def gapG (Hs : ℕ → ℤ) (k : ℕ) (u : Word) : ℤ := Hs (k + 1) - tot u

/-- First crossing of `Hs` (after depth `l`) at depth `k + 1`. -/
def CrossAtG (l : ℕ) (Hs : ℕ → ℤ) (k : ℕ) (w : Word) : Prop :=
  BelowG l Hs k (w.take k) ∧ gapG Hs k (w.take k) ≤ (w.getD k 0 : ℤ)

/-- First crossing of `Hs` at depth `k + 1` with overshoot `> K`. -/
def OverAtG (l : ℕ) (Hs : ℕ → ℤ) (K k : ℕ) (w : Word) : Prop :=
  BelowG l Hs k (w.take k) ∧ gapG Hs k (w.take k) + K < (w.getD k 0 : ℤ)

lemma one_le_gapG {l : ℕ} {Hs : ℕ → ℤ} (hmono : ∀ k, Hs k ≤ Hs (k + 1)) {k : ℕ} {u : Word}
    (hu : u.length = k) (h : BelowG l Hs k u) : 1 ≤ gapG Hs k u := by
  unfold gapG
  have h1 := h.2 k (Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩)
  have h2 := hmono k
  have h3 : pre u k = tot u := by rw [← hu, pre_length]
  rw [h3] at h1
  omega

lemma prob_overAtG (l : ℕ) {Hs : ℕ → ℤ} (hmono : ∀ k, Hs k ≤ Hs (k + 1)) (K k : ℕ) :
    prob (k + 1) (OverAtG l Hs K k) = (1 / 2) ^ (K + 1) * prob (k + 1) (CrossAtG l Hs k) :=
  prob_overshoot k K (BelowG l Hs k) (gapG Hs k) (fun _ hu _ h => one_le_gapG hmono hu h)

lemma crossAtG_take_iff {l : ℕ} {Hs : ℕ → ℤ} {k : ℕ} {x : Word} (hk : k < x.length) :
    CrossAtG l Hs k (x.take (k + 1)) ↔ BelowG l Hs k (x.take k) ∧ Hs (k + 1) ≤ pre x (k + 1) := by
  unfold CrossAtG gapG
  rw [take_take_succ, getD_take_succ hk, pre_succ hk]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma overAtG_take_iff {l : ℕ} {Hs : ℕ → ℤ} {K k : ℕ} {x : Word} (hk : k < x.length) :
    OverAtG l Hs K k (x.take (k + 1)) ↔
      BelowG l Hs k (x.take k) ∧ Hs (k + 1) + K < pre x (k + 1) := by
  unfold OverAtG gapG
  rw [take_take_succ, getD_take_succ hk, pre_succ hk]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma belowG_take {l : ℕ} {Hs : ℕ → ℤ} {k : ℕ} {x : Word} :
    BelowG l Hs k (x.take k) ↔ l ≤ k ∧ ∀ j ∈ Icc l k, (pre x j : ℤ) < Hs j := by
  unfold BelowG
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by rw [← pre_take (Finset.mem_Icc.mp hj).2]; exact h2 j hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by rw [pre_take (Finset.mem_Icc.mp hj).2]; exact h2 j hj⟩

/-- A word first crosses a barrier at one depth only. -/
lemma crossAtG_disjoint {l : ℕ} {Hs : ℕ → ℤ} {x : Word} {k k' : ℕ} (hk : k < x.length)
    (hk' : k' < x.length) (h : CrossAtG l Hs k (x.take (k + 1)))
    (h' : CrossAtG l Hs k' (x.take (k' + 1))) : k = k' := by
  rw [crossAtG_take_iff hk, belowG_take] at h
  rw [crossAtG_take_iff hk', belowG_take] at h'
  obtain ⟨⟨hl, hb⟩, hc⟩ := h
  obtain ⟨⟨hl', hb'⟩, hc'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hb' (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    omega
  · have := hb (k' + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    omega

/-- **Overshoot**, for a nondecreasing barrier: overshooting by more than `K` at the first
crossing has probability at most `2^{-K-1}`. -/
lemma prob_overshootG_le (l : ℕ) {Hs : ℕ → ℤ} (hmono : ∀ k, Hs k ≤ Hs (k + 1)) (K n : ℕ) :
    prob n (fun x => ∃ k ∈ range n, OverAtG l Hs K k (x.take (k + 1))) ≤ (1 / 2) ^ (K + 1) := by
  refine (prob_exists_le n (range n) (fun k x => OverAtG l Hs K k (x.take (k + 1)))).trans ?_
  have e : ∀ k ∈ range n, prob n (fun x => OverAtG l Hs K k (x.take (k + 1))) =
      (1 / 2) ^ (K + 1) * prob n (fun x => CrossAtG l Hs k (x.take (k + 1))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [prob_take (by omega) (OverAtG l Hs K k), prob_overAtG l hmono,
      prob_take (by omega) (CrossAtG l Hs k)]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have hd := sum_prob_le_one (n := n) (range n) (fun k x => CrossAtG l Hs k (x.take (k + 1)))
    (fun x hx _ k hk k' hk' h h' => crossAtG_disjoint (by rw [Finset.mem_range] at hk; omega)
      (by rw [Finset.mem_range] at hk'; omega) h h')
  calc (1 / 2 : ℝ) ^ (K + 1) * ∑ k ∈ range n, prob n (fun x => CrossAtG l Hs k (x.take (k + 1)))
      ≤ (1 / 2) ^ (K + 1) * 1 := by gcongr
    _ = (1 / 2) ^ (K + 1) := mul_one _

/-! ## The terminal rejection bound -/

/-- A deviation `|A_s - 2s| ≥ 2e_b` at depth `s`. -/
def DevT (b s : ℕ) (x : Word) : Prop := (2 * eB b : ℝ) ≤ |((tot (x.take s) : ℕ) : ℝ) - 2 * s|

/-- **Deviation at one depth** (Lemma 2.2(i), `lawS_chernoff` at `x = 2e_b`). -/
lemma prob_devT_le {b s : ℕ} (hb : 200 ≤ b) (hs1 : 1 ≤ s) (hs : s ≤ hB b) :
    prob (hB b) (DevT b s) ≤ 2 * Real.exp (-((eB b : ℝ) ^ 2) / (6 * b)) := by
  have e1 : prob (hB b) (DevT b s) =
      prob s (fun w => (2 * eB b : ℝ) ≤ |((tot w : ℕ) : ℝ) - 2 * s|) :=
    prob_take hs (fun w => (2 * eB b : ℝ) ≤ |((tot w : ℕ) : ℝ) - 2 * s|)
  rw [e1, prob_tot s (fun A => (2 * eB b : ℝ) ≤ |(A : ℝ) - 2 * s|)]
  refine (lawS_chernoff hs1 (x := (2 * eB b : ℝ)) (by positivity)).trans ?_
  have hb' : (200 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hs2 : (s : ℝ) ≤ 2 * b := by
    have := hs.trans (hB_le b); exact_mod_cast this
  have he : (eB b : ℝ) * 100 ≤ b := by
    have : eB b * 100 ≤ b := by unfold eB; omega
    exact_mod_cast this
  have he0 : (0 : ℝ) ≤ eB b := Nat.cast_nonneg _
  gcongr
  rw [neg_div, neg_le_neg_iff]
  apply le_min
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- **The deterministic core of the terminal rejection bound.** A word of length `h_b` with no
terminal prefix of shift `u ≤ 2r_b` deviates by `2e_b` from its mean at depth `ℓ_b` or at depth
`h_b`, or first crosses the shifted barrier with overshoot `> K`. -/
lemma terminal_or_bad {b K u : ℕ} (hb : 200 ≤ b) (hu : u ≤ 2 * rB b) {x : Word}
    (hx : x.length = hB b) (hpos : x.Pos) (hnot : ¬ ∃ w ∈ terminal b K u, w <+: x) :
    DevT b (lB b) x ∨ DevT b (hB b) x ∨
      ∃ k ∈ range (hB b), OverAtG (lB b) (tbar b u) K k (x.take (k + 1)) := by
  classical
  by_cases h1 : DevT b (lB b) x
  · exact Or.inl h1
  by_cases h2 : DevT b (hB b) x
  · exact Or.inr (Or.inl h2)
  right; right
  have hr := rB_add b
  have hwb := wB_lt (b := b) (by omega)
  have hw1 : 1 ≤ wB b := by unfold wB; omega
  have hl1 : 1 ≤ lB b := by unfold lB; omega
  have hlb : lB b + wB b = b := by unfold lB; omega
  -- no deviation, in `ℤ`
  have hdev : ∀ s, ¬ DevT b s x → (pre x s : ℤ) < 2 * s + 2 * eB b ∧ 2 * (s : ℤ) < pre x s + 2 * eB b := by
    intro s h
    unfold DevT at h
    push_neg at h
    rw [abs_lt] at h
    have e : ((tot (x.take s) : ℕ) : ℝ) = ((pre x s : ℕ) : ℝ) := rfl
    rw [e] at h
    obtain ⟨h3, h4⟩ := h
    constructor
    · have : (((pre x s : ℤ)) : ℝ) < ((2 * s + 2 * eB b : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((2 * (s : ℤ) : ℤ) : ℝ) < ((pre x s + 2 * eB b : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  -- below at `ℓ_b`
  have hlow : (pre x (lB b) : ℤ) < tbar b u (lB b) := by
    have h := (hdev (lB b) h1).1
    unfold tbar
    rw [barrier_of_le (by omega), show b - lB b = wB b by omega]
    omega
  -- crossed by `h_b`
  have hc : tbar b u (hB b) ≤ pre x (hB b) := by
    have h := (hdev (hB b) h2).2
    unfold tbar
    rw [barrier_of_ge (by unfold hB; omega), show hB b - b = wB b by unfold hB; omega]
    unfold hB at h ⊢
    push_cast at h ⊢
    omega
  have hlh : lB b < hB b := by unfold lB hB; omega
  have hex : ∃ s, lB b < s ∧ tbar b u s ≤ pre x s := ⟨hB b, hlh, hc⟩
  obtain ⟨hls, hcs⟩ : lB b < Nat.find hex ∧ tbar b u (Nat.find hex) ≤ pre x (Nat.find hex) :=
    Nat.find_spec hex
  have hsle : Nat.find hex ≤ hB b := Nat.find_min' hex ⟨hlh, hc⟩
  have hsmin : ∀ j, lB b < j → j < Nat.find hex → (pre x j : ℤ) < tbar b u j := by
    intro j hj1 hj2
    have := Nat.find_min hex hj2
    push_neg at this
    exact this hj1
  set s := Nat.find hex with hs_def
  have hbelow : ∀ j ∈ Icc (lB b) (s - 1), (pre x j : ℤ) < tbar b u j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases Nat.eq_or_lt_of_le hj.1 with h | h
    · rw [← h]; exact hlow
    · exact hsmin j h (by omega)
  by_cases hK : (pre x s : ℤ) ≤ tbar b u s + K
  · exfalso
    apply hnot
    refine ⟨x.take s, ?_, List.take_prefix s x⟩
    rw [mem_terminal, isTerminal_iff]
    have hlen : (x.take s).length = s := by rw [List.length_take]; omega
    unfold FirstCross
    rw [hlen, pre_take le_rfl]
    refine ⟨⟨fun a ha => hpos a (List.mem_of_mem_take ha), hls, fun j hj => ?_, hcs, hK⟩, hsle⟩
    rw [pre_take ((Finset.mem_Icc.mp hj).2.trans (Nat.sub_le s 1))]
    exact hbelow j hj
  · refine ⟨s - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have hs1 : s - 1 + 1 = s := by omega
    rw [overAtG_take_iff (k := s - 1) (x := x) (by omega), belowG_take, hs1]
    exact ⟨⟨by omega, fun j hj => hbelow j hj⟩, by push_neg at hK; exact hK⟩

/-- The rejection bound for terminal blocks at one scale `b ≥ 200` and shift `u ≤ 2r_b`. -/
theorem one_sub_pmass_terminal_le {b : ℕ} (hb : 200 ≤ b) (K : ℕ) {u : ℕ} (hu : u ≤ 2 * rB b) :
    1 - pmass (terminal b K u) ≤
      4 * Real.exp (-((eB b : ℝ) ^ 2) / (6 * b)) + (1 / 2) ^ (K + 1) := by
  have hmono : ∀ k, tbar b u k ≤ tbar b u (k + 1) := fun k => tbar_mono b u (Nat.le_succ k)
  have h1 : prob (hB b) (fun x => ∃ w ∈ terminal b K u, w <+: x) ≤ pmass (terminal b K u) := by
    refine (prob_exists_le (hB b) (terminal b K u) (fun w x => w <+: x)).trans (le_of_eq ?_)
    unfold pmass
    exact Finset.sum_congr rfl fun w hw =>
      prob_prefix (mem_terminal.mp hw).1.1 (mem_terminal.mp hw).2
  have h2 := prob_add_not (hB b) (fun x => ∃ w ∈ terminal b K u, w <+: x)
  have h3 : prob (hB b) (fun x => ¬ ∃ w ∈ terminal b K u, w <+: x) ≤
      prob (hB b) (fun x => DevT b (lB b) x ∨ (DevT b (hB b) x ∨
        ∃ k ∈ range (hB b), OverAtG (lB b) (tbar b u) K k (x.take (k + 1)))) :=
    prob_mono fun x hx hp hnot => terminal_or_bad hb hu hx hp hnot
  have h4 := prob_or_le (hB b) (fun x => DevT b (lB b) x)
    (fun x => DevT b (hB b) x ∨ ∃ k ∈ range (hB b), OverAtG (lB b) (tbar b u) K k (x.take (k + 1)))
  have h5 := prob_or_le (hB b) (fun x => DevT b (hB b) x)
    (fun x => ∃ k ∈ range (hB b), OverAtG (lB b) (tbar b u) K k (x.take (k + 1)))
  have hl1 : 1 ≤ lB b := by unfold lB wB; omega
  have hlh : lB b ≤ hB b := by unfold lB hB; omega
  have h6 := prob_devT_le hb hl1 hlh
  have h7 := prob_devT_le hb (by unfold hB; omega) (le_refl (hB b))
  have h8 := prob_overshootG_le (lB b) hmono K (hB b)
  linarith

/-- **The terminal rejection bound** (§8.4): for `b ≥ 200`, every `K` and every shift
`u ≤ 2r_b`, the terminal family is prefix-free and
`1 - p(terminal b K u) ≤ 4 exp(-e_b²/(6b)) + 2^{-K-1}`, which is `O(e^{-cb}) + 2^{-K-1}`
(`e_b ≥ b/200`). -/
theorem terminal_rejection {b : ℕ} (hb : 200 ≤ b) (K : ℕ) {u : ℕ} (hu : u ≤ 2 * rB b) :
    PrefixFree (terminal b K u) ∧ 1 - pmass (terminal b K u) ≤
      4 * Real.exp (-((eB b : ℝ) ^ 2) / (6 * b)) + (1 / 2) ^ (K + 1) :=
  ⟨terminal_prefixFree b K u, one_sub_pmass_terminal_le hb K hu⟩

/-! ## (8.5) for terminal blocks -/

/-- `4^b 3^s ≤ 2·3^b 2^A` and `2^A 3^b ≤ 2^{K+1} 4^b 3^s` when `H_b(s) ≤ A ≤ H_b(s) + K` (from
`3^t ≤ 2^{B(t)} ≤ 2·3^t`; the computation of `block_pow_bounds`, for any depth and total). -/
lemma pow_bounds_of_barrier {b s A K : ℕ} (hA1 : barrier b s ≤ A)
    (hA2 : (A : ℤ) ≤ barrier b s + K) :
    4 ^ b * 3 ^ s ≤ 2 * 3 ^ b * 2 ^ A ∧ 2 ^ A * 3 ^ b ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ s := by
  have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := by rw [pow_mul]; norm_num
  rcases le_total s b with h | h
  · rw [barrier_of_le h] at hA1 hA2
    have hb3 : 3 ^ b = 3 ^ s * 3 ^ (b - s) := by rw [← pow_add]; congr 1; omega
    have hB1 := two_pow_Bc_le (b - s)
    have hB2 := three_pow_le_two_pow_Bc (b - s)
    constructor
    · have e1 : 2 * b ≤ A + Bc (b - s) := by omega
      have : 4 ^ b ≤ 2 ^ A * (2 * 3 ^ (b - s)) := by
        calc 4 ^ b = 2 ^ (2 * b) := h4
          _ ≤ 2 ^ (A + Bc (b - s)) := Nat.pow_le_pow_right (by norm_num) e1
          _ = 2 ^ A * 2 ^ Bc (b - s) := pow_add _ _ _
          _ ≤ 2 ^ A * (2 * 3 ^ (b - s)) := Nat.mul_le_mul_left _ hB1
      calc 4 ^ b * 3 ^ s ≤ 2 ^ A * (2 * 3 ^ (b - s)) * 3 ^ s := Nat.mul_le_mul_right _ this
        _ = 2 * 3 ^ b * 2 ^ A := by rw [hb3]; ring
    · have e2 : A + Bc (b - s) ≤ 2 * b + K := by omega
      have : 2 ^ A * 3 ^ (b - s) ≤ 2 ^ K * 4 ^ b := by
        calc 2 ^ A * 3 ^ (b - s) ≤ 2 ^ A * 2 ^ Bc (b - s) := Nat.mul_le_mul_left _ hB2
          _ = 2 ^ (A + Bc (b - s)) := (pow_add _ _ _).symm
          _ ≤ 2 ^ (2 * b + K) := Nat.pow_le_pow_right (by norm_num) e2
          _ = 2 ^ K * 4 ^ b := by rw [pow_add, h4]; ring
      calc 2 ^ A * 3 ^ b = (2 ^ A * 3 ^ (b - s)) * 3 ^ s := by rw [hb3]; ring
        _ ≤ (2 ^ K * 4 ^ b) * 3 ^ s := Nat.mul_le_mul_right _ this
        _ ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ s := by
            rw [pow_succ]; nlinarith [Nat.zero_le (2 ^ K * 4 ^ b * 3 ^ s)]
  · rw [barrier_of_ge h] at hA1 hA2
    have hd3 : 3 ^ s = 3 ^ b * 3 ^ (s - b) := by rw [← pow_add]; congr 1; omega
    have hB1 := two_pow_Bc_le (s - b)
    have hB2 := three_pow_le_two_pow_Bc (s - b)
    constructor
    · have e1 : 2 * b + Bc (s - b) ≤ A := by omega
      have : 4 ^ b * 3 ^ (s - b) ≤ 2 ^ A := by
        calc 4 ^ b * 3 ^ (s - b) ≤ 2 ^ (2 * b) * 2 ^ Bc (s - b) := by
              rw [← h4]; exact Nat.mul_le_mul_left _ hB2
          _ = 2 ^ (2 * b + Bc (s - b)) := (pow_add _ _ _).symm
          _ ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) e1
      calc 4 ^ b * 3 ^ s = (4 ^ b * 3 ^ (s - b)) * 3 ^ b := by rw [hd3]; ring
        _ ≤ 2 ^ A * 3 ^ b := Nat.mul_le_mul_right _ this
        _ ≤ 2 * 3 ^ b * 2 ^ A := by nlinarith [Nat.zero_le (2 ^ A * 3 ^ b)]
    · have e2 : A ≤ 2 * b + Bc (s - b) + K := by omega
      calc 2 ^ A * 3 ^ b ≤ 2 ^ (2 * b + Bc (s - b) + K) * 3 ^ b :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) e2)
        _ = 2 ^ K * 4 ^ b * 2 ^ Bc (s - b) * 3 ^ b := by rw [pow_add, pow_add, h4]; ring
        _ ≤ 2 ^ K * 4 ^ b * (2 * 3 ^ (s - b)) * 3 ^ b :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB1)
        _ = 2 ^ (K + 1) * 4 ^ b * 3 ^ s := by rw [hd3, pow_succ]; ring

/-- The weight of a terminal block with shift `u`: `4^b 3^d 2^u ≤ 2·3^b 2^{A + r_b}` and
`2^{A + r_b} 3^b ≤ 2^{K+1} 4^b 3^d 2^u`. -/
lemma terminal_pow_bounds {b K u : ℕ} {w : Word} (hw : w ∈ terminal b K u) :
    4 ^ b * 3 ^ w.length * 2 ^ u ≤ 2 * 3 ^ b * 2 ^ (tot w + rB b) ∧
      2 ^ (tot w + rB b) * 3 ^ b ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ w.length * 2 ^ u := by
  have hfc := (isTerminal_iff.mp (mem_terminal.mp hw)).1
  have hA1 : tbar b u w.length ≤ tot w := by rw [← pre_length]; exact hfc.2.2.2.1
  have hA2 : (tot w : ℤ) ≤ tbar b u w.length + K := by rw [← pre_length]; exact hfc.2.2.2.2
  unfold tbar at hA1 hA2
  have hbn := barrier_nonneg b w.length
  have hge : u ≤ tot w + rB b := by omega
  obtain ⟨hl, hu'⟩ := pow_bounds_of_barrier (b := b) (s := w.length) (A := tot w + rB b - u)
    (K := K) (by omega) (by omega)
  have e : 2 ^ (tot w + rB b) = 2 ^ (tot w + rB b - u) * 2 ^ u := by
    rw [← pow_add]; congr 1; omega
  constructor
  · rw [e]
    calc 4 ^ b * 3 ^ w.length * 2 ^ u ≤ (2 * 3 ^ b * 2 ^ (tot w + rB b - u)) * 2 ^ u :=
          Nat.mul_le_mul_right _ hl
      _ = 2 * 3 ^ b * (2 ^ (tot w + rB b - u) * 2 ^ u) := by ring
  · rw [e]
    calc 2 ^ (tot w + rB b - u) * 2 ^ u * 3 ^ b = (2 ^ (tot w + rB b - u) * 3 ^ b) * 2 ^ u := by
          ring
      _ ≤ (2 ^ (K + 1) * 4 ^ b * 3 ^ w.length) * 2 ^ u := Nat.mul_le_mul_right _ hu'

/-- `ϑ_w ≤ (3/2)^{|w|} - 1 ≤ 2^b` for a word of depth `≤ 8b/5`. -/
lemma theta_le_of_len {b : ℕ} {w : Word} (hw : w.Pos) (h5 : 5 * w.length ≤ 8 * b) :
    (thetaW w : ℝ) ≤ 2 ^ b := by
  have h1 := thetaW_le_pow hw
  have h2 : ((3 / 2 : ℚ) ^ w.length) ≤ 2 ^ b := by
    have h0 : (0 : ℚ) ≤ (3 / 2) ^ w.length := by positivity
    have : ((3 / 2 : ℚ) ^ w.length) ^ 5 ≤ (2 ^ b) ^ 5 := by
      rw [← pow_mul, ← pow_mul]
      calc (3 / 2 : ℚ) ^ (w.length * 5) ≤ (3 / 2) ^ (8 * b) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ = ((3 / 2) ^ 8) ^ b := by rw [pow_mul]
        _ ≤ (2 ^ 5) ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
        _ = 2 ^ (b * 5) := by rw [← pow_mul, mul_comm]
    exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp this
  have : thetaW w ≤ 2 ^ b := by linarith
  exact_mod_cast this

/-- **(8.5, `eq:C2`) for terminal blocks**: a terminal block `w` with shift `u` and overshoot
`≤ K` at scale `b`, applied to `R ≥ 2^{b+1}`, gives `2^u L_b(R) ≤ Φ_w(R) ≤ 2^{u+K+3} L_b(R)`. -/
theorem phi_bounds_terminal {b K u : ℕ} {w : Word} (hw : w ∈ terminal b K u) {R : ℕ}
    (hR : (2 : ℝ) ^ (b + 1) ≤ R) :
    (2 : ℝ) ^ u * Lb b R ≤ ((Phi w R : ℚ) : ℝ) ∧ ((Phi w R : ℚ) : ℝ) ≤ 2 ^ (u + K + 3) * Lb b R := by
  have hT := mem_terminal.mp hw
  obtain ⟨hl, hu⟩ := terminal_pow_bounds hw
  have hl' : (4 : ℝ) ^ b * 3 ^ w.length * 2 ^ u ≤ 2 * 3 ^ b * (2 ^ tot w * 2 ^ rB b) := by
    rw [← pow_add]; exact_mod_cast hl
  have hu' : (2 ^ tot w * 2 ^ rB b : ℝ) * 3 ^ b ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ w.length * 2 ^ u := by
    rw [← pow_add]; exact_mod_cast hu
  have h5 : 5 * w.length ≤ 8 * b := by have := hT.2; unfold hB wB at this; omega
  have hth := theta_le_of_len hT.1.1 h5
  have hth0 : (0 : ℝ) ≤ thetaW w := by exact_mod_cast thetaW_nonneg w
  have hPhi : ((Phi w R : ℚ) : ℝ) = 2 ^ tot w * ((R : ℝ) - thetaW w) / 3 ^ w.length := by
    unfold Phi; push_cast; ring
  have h2b : (2 : ℝ) ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hd : (0 : ℝ) < 3 ^ w.length := by positivity
  have h3b : (0 : ℝ) < 3 ^ b := by positivity
  have hA : (0 : ℝ) < 2 ^ tot w := by positivity
  have hr : (0 : ℝ) < 2 ^ rB b := by positivity
  rw [hPhi]
  unfold Lb
  rw [div_pow]
  constructor
  · rw [le_div_iff₀ hd]
    have e : 2 ^ u * (4 ^ b / 3 ^ b * (R : ℝ) / (4 * 2 ^ rB b)) * 3 ^ w.length =
        (4 ^ b * 3 ^ w.length * 2 ^ u) * R / (4 * 3 ^ b * 2 ^ rB b) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : (R : ℝ) ≤ 2 * ((R : ℝ) - thetaW w) := by linarith
    calc 4 ^ b * 3 ^ w.length * 2 ^ u * (R : ℝ) ≤ 2 * 3 ^ b * (2 ^ tot w * 2 ^ rB b) * R :=
          mul_le_mul_of_nonneg_right hl' hR0
      _ ≤ 2 * 3 ^ b * (2 ^ tot w * 2 ^ rB b) * (2 * ((R : ℝ) - thetaW w)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ tot w * ((R : ℝ) - thetaW w) * (4 * 3 ^ b * 2 ^ rB b) := by ring
  · rw [div_le_iff₀ hd]
    have e : 2 ^ (u + K + 3) * (4 ^ b / 3 ^ b * (R : ℝ) / (4 * 2 ^ rB b)) * 3 ^ w.length =
        (2 ^ (K + 1) * 4 ^ b * 3 ^ w.length * 2 ^ u) * R / (3 ^ b * 2 ^ rB b) := by
      rw [show u + K + 3 = (K + 1) + u + 2 by omega, pow_add, pow_add]
      field_simp
      ring
    rw [e, le_div_iff₀ (by positivity)]
    have h1 : (R : ℝ) - thetaW w ≤ R := by linarith
    calc 2 ^ tot w * ((R : ℝ) - thetaW w) * (3 ^ b * 2 ^ rB b)
        ≤ 2 ^ tot w * (R : ℝ) * (3 ^ b * 2 ^ rB b) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA.le) (by positivity)
      _ = ((2 ^ tot w * 2 ^ rB b) * 3 ^ b) * R := by ring
      _ ≤ (2 ^ (K + 1) * 4 ^ b * 3 ^ w.length * 2 ^ u) * R := mul_le_mul_of_nonneg_right hu' hR0

/-! ## The selected shift -/

lemma Lb_pos {b R : ℕ} (hR : 0 < R) : 0 < Lb b R := by
  unfold Lb
  have : (0 : ℝ) < R := by exact_mod_cast hR
  positivity

/-- For `L_b(R) < X ≤ U_b(R)`, the selected shift `u` satisfies `1 ≤ u ≤ 2r_b` and
`X ≤ 2^u L_b(R) < 2X` (§8.4). -/
lemma shiftOf_spec {b R : ℕ} (hR : 0 < R) {X : ℝ} (h1 : Lb b R < X) (h2 : X ≤ Ub b R) :
    1 ≤ shiftOf b R X ∧ shiftOf b R X ≤ 2 * rB b ∧ X ≤ 2 ^ shiftOf b R X * Lb b R ∧
      2 ^ shiftOf b R X * Lb b R < 2 * X := by
  have hL := Lb_pos (b := b) hR
  have hX : 0 < X / Lb b R := div_pos (hL.trans h1) hL
  have hX1 : 1 < X / Lb b R := (one_lt_div hL).mpr h1
  have hlog0 : 0 < Real.logb 2 (X / Lb b R) := Real.logb_pos (by norm_num) hX1
  have hceil1 : Real.logb 2 (X / Lb b R) ≤ shiftOf b R X := Nat.le_ceil _
  have hceil2 : (shiftOf b R X : ℝ) < Real.logb 2 (X / Lb b R) + 1 :=
    Nat.ceil_lt_add_one hlog0.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, Nat.cast_zero] at hceil1
    linarith
  · apply Nat.ceil_le.mpr
    rw [Real.logb_le_iff_le_rpow (by norm_num) hX, Real.rpow_natCast, div_le_iff₀ hL]
    unfold Ub at h2
    linarith
  · have := (Real.logb_le_iff_le_rpow (by norm_num) hX).mp hceil1
    rw [Real.rpow_natCast, div_le_iff₀ hL] at this
    linarith
  · have h3 : (shiftOf b R X : ℝ) - 1 < Real.logb 2 (X / Lb b R) := by linarith
    have h4 := (Real.lt_logb_iff_rpow_lt (by norm_num) hX).mp h3
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one, lt_div_iff₀ hL] at h4
    have e : (2 : ℝ) ^ shiftOf b R X / 2 * Lb b R = (2 ^ shiftOf b R X * Lb b R) / 2 := by ring
    linarith

/-! ## The spread bound -/

/-- `lo_n = ∏_{j<n} (4/3)^{b_j}/4`. -/
def loP (b0 n : ℕ) : ℝ := ∏ j ∈ range n, ((4 / 3 : ℝ) ^ bseq b0 j / 4)

/-- `hi_n = ∏_{j<n} 2^{K_j+1} (4/3)^{b_j}`. -/
def hiP (b0 n : ℕ) : ℝ := ∏ j ∈ range n, ((2 : ℝ) ^ (Kseq j + 1) * (4 / 3 : ℝ) ^ bseq b0 j)

/-- `σ_n = ∑_{j<n} (K_j + 3)`. -/
def sigmaN (n : ℕ) : ℕ := ∑ j ∈ range n, (Kseq j + 3)

lemma loP_succ (b0 n : ℕ) : loP b0 (n + 1) = loP b0 n * ((4 / 3 : ℝ) ^ bseq b0 n / 4) :=
  Finset.prod_range_succ _ _

lemma hiP_succ (b0 n : ℕ) :
    hiP b0 (n + 1) = hiP b0 n * ((2 : ℝ) ^ (Kseq n + 1) * (4 / 3 : ℝ) ^ bseq b0 n) :=
  Finset.prod_range_succ _ _

lemma sigmaN_succ (n : ℕ) : sigmaN (n + 1) = sigmaN n + (Kseq n + 3) := Finset.sum_range_succ _ _

lemma hiP_eq (b0 n : ℕ) : hiP b0 n = 2 ^ sigmaN n * loP b0 n := by
  induction n with
  | zero => simp [hiP, loP, sigmaN]
  | succ n ih =>
    rw [hiP_succ, loP_succ, sigmaN_succ, ih, pow_add]
    ring

lemma loP_nonneg (b0 n : ℕ) : 0 ≤ loP b0 n := Finset.prod_nonneg fun j _ => by positivity

lemma endpt_nil (M : ℕ) : endpt M [] = M := by
  simp [endpt, src, Phi, thetaW, tot]

/-- **The endpoint bounds** behind the spread bound: by (8.5), every generation-`n` endpoint from
an odd seed `M ≥ 16^{b_0}` lies in `[lo_n M, hi_n M]`. -/
theorem endpt_bounds {b0 : ℕ} (hb0 : 100 ≤ b0) {M : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M) :
    ∀ n, ∀ H ∈ hist b0 M n, loP b0 n * M ≤ endpt M H ∧ (endpt M H : ℝ) ≤ hiP b0 n * M := by
  classical
  intro n
  induction n with
  | zero =>
    intro H hH
    obtain ⟨hb, -⟩ := mem_hist.mp hH
    simp only [blocks, Finset.mem_singleton] at hb
    subst hb
    simp [loP, hiP, endpt_nil]
  | succ n ih =>
    intro H hH
    rw [hist_succ b0 M n hM, Finset.mem_image] at hH
    obtain ⟨⟨H', w⟩, hp, rfl⟩ := hH
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hH', hw⟩, hr⟩ := hp
    dsimp only at hr hw hH' ⊢
    have hwp := central_pos hw
    have hRo := endpt_odd hM hH'
    rw [endpt_append hM hH' hwp hr]
    have hsrc := (realisable_of_realizes hwp hRo hr).1
    have hbn : 100 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
    have hge := endpt_ge hb0 hM hM16 hH'
    have h2R : (2 : ℚ) ^ (bseq b0 n + 1) ≤ (endpt M H' : ℚ) := by
      have h1 : (2 : ℝ) ^ (bseq b0 n + 1) ≤ 16 ^ bseq b0 n / 2 := by
        rw [le_div_iff₀ (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : (2 : ℝ) ^ (bseq b0 n + 1) ≤ endpt M H' := h1.trans hge
      exact_mod_cast this
    obtain ⟨hlo, hhi⟩ := phi_bounds (by omega) hw h2R
    rw [← hsrc] at hlo hhi
    have hlo' : 1 / 4 * (4 / 3 : ℝ) ^ bseq b0 n * (endpt M H' : ℝ) ≤ (src w (endpt M H') : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hlo
      push_cast at this
      linarith
    have hhi' : (src w (endpt M H') : ℝ) ≤
        2 ^ (Kseq n + 1) * (4 / 3 : ℝ) ^ bseq b0 n * (endpt M H' : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hhi
      push_cast at this
      linarith
    obtain ⟨ih1, ih2⟩ := ih H' hH'
    rw [loP_succ, hiP_succ]
    constructor
    · have hc : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ bseq b0 n / 4 := by positivity
      calc loP b0 n * ((4 / 3 : ℝ) ^ bseq b0 n / 4) * M
          = ((4 / 3 : ℝ) ^ bseq b0 n / 4) * (loP b0 n * M) := by ring
        _ ≤ ((4 / 3 : ℝ) ^ bseq b0 n / 4) * endpt M H' := mul_le_mul_of_nonneg_left ih1 hc
        _ = 1 / 4 * (4 / 3 : ℝ) ^ bseq b0 n * (endpt M H' : ℝ) := by ring
        _ ≤ _ := hlo'
    · have hc : (0 : ℝ) ≤ 2 ^ (Kseq n + 1) * (4 / 3 : ℝ) ^ bseq b0 n := by positivity
      calc (src w (endpt M H') : ℝ) ≤ 2 ^ (Kseq n + 1) * (4 / 3 : ℝ) ^ bseq b0 n * endpt M H' :=
            hhi'
        _ ≤ 2 ^ (Kseq n + 1) * (4 / 3 : ℝ) ^ bseq b0 n * (hiP b0 n * M) :=
            mul_le_mul_of_nonneg_left ih2 hc
        _ = _ := by ring

/-- **The spread bound** (§8.4): generation-`n` endpoints from an odd seed `M ≥ 16^{b_0}` have
mutual ratios at most `2^{σ_n}`, `σ_n = ∑_{j<n} (K_j + 3)`. -/
theorem spread_bound {b0 : ℕ} (hb0 : 100 ≤ b0) {M : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M) {n : ℕ}
    {H H' : List Word} (hH : H ∈ hist b0 M n) (hH' : H' ∈ hist b0 M n) :
    (endpt M H : ℝ) ≤ 2 ^ sigmaN n * endpt M H' := by
  have h1 := (endpt_bounds hb0 hM hM16 n H hH).2
  have h2 := (endpt_bounds hb0 hM hM16 n H' hH').1
  rw [hiP_eq] at h1
  have : (0 : ℝ) ≤ 2 ^ sigmaN n := by positivity
  calc (endpt M H : ℝ) ≤ 2 ^ sigmaN n * loP b0 n * M := h1
    _ = 2 ^ sigmaN n * (loP b0 n * M) := by ring
    _ ≤ 2 ^ sigmaN n * endpt M H' := mul_le_mul_of_nonneg_left h2 this

/-! ## Lemma 8.8 -/

/-- `b_n ≥ 10^6 + 10^4 n` once `b_0 ≥ 10^6`. -/
lemma bseq_ge_lin {b0 : ℕ} (hb0 : 1000000 ≤ b0) (n : ℕ) : 1000000 + 10000 * n ≤ bseq b0 n := by
  induction n with
  | zero => exact hb0
  | succ n ih => rw [bseq_succ]; clear hb0; omega

/-- `50 (σ_n + K_n + 5) ≤ b_n` once `b_0 ≥ 10^6`. -/
lemma sigma_le_bseq {b0 : ℕ} (hb0 : 1000000 ≤ b0) (n : ℕ) :
    50 * (sigmaN n + Kseq n + 5) ≤ bseq b0 n := by
  induction n with
  | zero => simp only [sigmaN, Kseq, bseq, Finset.range_zero, Finset.sum_empty]; omega
  | succ n ih =>
    have h := bseq_ge_lin hb0 n
    rw [sigmaN_succ, bseq_succ]
    unfold Kseq at ih ⊢
    clear hb0
    omega

/-- **The exponent count of Lemma 8.8:**
`2 b_{n+1} + σ_n + K_n + 2 ≤ B(b_{n+1}) + r_{b_n} + r_{b_{n+1}}`, i.e. the paper's
`λ b' - r_{b'} - r_b + σ_n + K_n + 1 < 0`, with `1.01 λ - 2.01 λ₀ ≈ -0.041` replaced by the integer
bounds `41 B(t) ≤ 65t + 40` and `19t ≤ 12 B(t)` and `σ_n + K_n ≤ b_n/50`. -/
lemma allscales_exponent {b0 : ℕ} (hb0 : 1000000 ≤ b0) (n : ℕ) :
    2 * bseq b0 (n + 1) + sigmaN n + Kseq n + 2 ≤
      Bc (bseq b0 (n + 1)) + rB (bseq b0 n) + rB (bseq b0 (n + 1)) := by
  have hs := sigma_le_bseq hb0 n
  have hb := bseq_ge_lin hb0 n
  have hsucc := bseq_succ b0 n
  have hr1 := rB_add (bseq b0 n)
  have hr2 := rB_add (bseq b0 (n + 1))
  have h1 := forty_one_mul_Bc_le (wB (bseq b0 n))
  have h2 := forty_one_mul_Bc_le (wB (bseq b0 (n + 1)))
  have h3 := nineteen_mul_le_Bc (bseq b0 (n + 1))
  unfold wB at h1 h2
  unfold wB eB at hr1 hr2
  clear hb0
  omega

lemma loP_ge_one {b0 : ℕ} (hb0 : 5 ≤ b0) (n : ℕ) : 1 ≤ loP b0 n := by
  induction n with
  | zero => simp [loP]
  | succ n ih =>
    rw [loP_succ]
    have h5 : 5 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
    have h1 : (4 / 3 : ℝ) ^ 5 ≤ (4 / 3) ^ bseq b0 n := pow_le_pow_right₀ (by norm_num) h5
    have h2 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ bseq b0 n / 4 := by
      rw [le_div_iff₀ (by norm_num)]; norm_num at h1 ⊢; linarith
    nlinarith

/-- The lower admissibility threshold at generation `n`: `L_{b_n}` at `hi_n M`. -/
def alphaN (b0 M n : ℕ) : ℝ :=
  (4 / 3 : ℝ) ^ bseq b0 n * (hiP b0 n * M) / (4 * 2 ^ rB (bseq b0 n))

/-- The upper admissibility threshold at generation `n`: `U_{b_n}` at `lo_n M`. -/
def betaN (b0 M n : ℕ) : ℝ :=
  2 ^ (2 * rB (bseq b0 n)) * ((4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M) / (4 * 2 ^ rB (bseq b0 n)))

/-- `α_n < X ≤ β_n` makes `X` admissible at generation `n` (by `endpt_bounds`). -/
lemma admissible_of_between {b0 : ℕ} (hb0 : 100 ≤ b0) {M : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M)
    {n : ℕ} {X : ℝ} (h1 : alphaN b0 M n < X) (h2 : X ≤ betaN b0 M n) : Admissible b0 M n X := by
  intro H hH
  obtain ⟨hlo, hhi⟩ := endpt_bounds hb0 hM hM16 n H hH
  have hc : 0 < (4 * 2 ^ rB (bseq b0 n) : ℝ) := by positivity
  have hp : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ bseq b0 n := by positivity
  constructor
  · unfold Lb
    refine lt_of_le_of_lt ?_ h1
    unfold alphaN
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hp) hc.le
  · unfold Ub Lb
    refine h2.trans ?_
    unfold betaN
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo hp) hc.le) (by positivity)

/-- **Every next lower endpoint lies below every current upper endpoint:** `α_{n+1} < β_n`. -/
lemma alpha_succ_lt_beta {b0 : ℕ} (hb0 : 1000000 ≤ b0) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    alphaN b0 M (n + 1) < betaN b0 M n := by
  have hexp := allscales_exponent hb0 n
  have hb1 : 1 ≤ bseq b0 (n + 1) := by have := le_bseq b0 (n + 1); omega
  have hB1 := one_le_Bc hb1
  have hlt := two_pow_Bc_sub_one_lt hb1
  have hN : 4 ^ bseq b0 (n + 1) * 2 ^ (sigmaN n + Kseq n + 1) <
      3 ^ bseq b0 (n + 1) * 2 ^ (rB (bseq b0 n) + rB (bseq b0 (n + 1))) := by
    calc 4 ^ bseq b0 (n + 1) * 2 ^ (sigmaN n + Kseq n + 1)
        = 2 ^ (2 * bseq b0 (n + 1)) * 2 ^ (sigmaN n + Kseq n + 1) := by rw [pow_mul]; norm_num
      _ = 2 ^ (2 * bseq b0 (n + 1) + (sigmaN n + Kseq n + 1)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (Bc (bseq b0 (n + 1)) - 1 + (rB (bseq b0 n) + rB (bseq b0 (n + 1)))) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ (Bc (bseq b0 (n + 1)) - 1) * 2 ^ (rB (bseq b0 n) + rB (bseq b0 (n + 1))) :=
          pow_add _ _ _
      _ < 3 ^ bseq b0 (n + 1) * 2 ^ (rB (bseq b0 n) + rB (bseq b0 (n + 1))) :=
          Nat.mul_lt_mul_of_pos_right hlt (by positivity)
  have key : (4 : ℝ) ^ bseq b0 (n + 1) * 2 ^ (sigmaN n + Kseq n + 1) <
      3 ^ bseq b0 (n + 1) * 2 ^ (rB (bseq b0 n) + rB (bseq b0 (n + 1))) := by exact_mod_cast hN
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hP : 0 < (4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M) := by
    have := loP_ge_one (b0 := b0) (by omega) n
    have : 0 < loP b0 n := by linarith
    positivity
  unfold alphaN betaN
  rw [hiP_succ, hiP_eq]
  have eL : (4 / 3 : ℝ) ^ bseq b0 (n + 1) * (2 ^ sigmaN n * loP b0 n *
      (2 ^ (Kseq n + 1) * (4 / 3 : ℝ) ^ bseq b0 n) * M) / (4 * 2 ^ rB (bseq b0 (n + 1))) =
      ((4 : ℝ) ^ bseq b0 (n + 1) * 2 ^ (sigmaN n + Kseq n + 1)) *
        ((4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M)) /
          (4 * 2 ^ rB (bseq b0 (n + 1)) * 3 ^ bseq b0 (n + 1)) := by
    rw [div_pow (4 : ℝ) 3 (bseq b0 (n + 1)), pow_add (2 : ℝ) (sigmaN n + Kseq n) 1,
      pow_add (2 : ℝ) (sigmaN n) (Kseq n), pow_add (2 : ℝ) (Kseq n) 1]
    field_simp
  have eR : (2 : ℝ) ^ (2 * rB (bseq b0 n)) * ((4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M) /
      (4 * 2 ^ rB (bseq b0 n))) =
      ((3 : ℝ) ^ bseq b0 (n + 1) * 2 ^ (rB (bseq b0 n) + rB (bseq b0 (n + 1)))) *
        ((4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M)) /
          (4 * 2 ^ rB (bseq b0 (n + 1)) * 3 ^ bseq b0 (n + 1)) := by
    rw [pow_add (2 : ℝ) (rB (bseq b0 n)) (rB (bseq b0 (n + 1))), two_mul, pow_add (2 : ℝ)]
    field_simp
  rw [eL, eR]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right key hP) (by positivity)

/-- `β_n ≥ 2^n/4`: the upper thresholds tend to infinity. -/
lemma betaN_ge {b0 : ℕ} (hb0 : 1000000 ≤ b0) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    (2 : ℝ) ^ n / 4 ≤ betaN b0 M n := by
  have hb := bseq_ge_lin hb0 n
  have hr := rB_add (bseq b0 n)
  have h5 := five_mul_Bc_le (wB (bseq b0 n))
  have hrn : n ≤ rB (bseq b0 n) := by unfold wB at h5; unfold wB eB at hr; clear hb0; omega
  have hlo := loP_ge_one (b0 := b0) (by omega) n
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h43 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ bseq b0 n := one_le_pow₀ (by norm_num)
  have hP : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M) := by
    have : (1 : ℝ) ≤ loP b0 n * M := by nlinarith
    nlinarith
  have e : betaN b0 M n = 2 ^ rB (bseq b0 n) * ((4 / 3 : ℝ) ^ bseq b0 n * (loP b0 n * M)) / 4 := by
    unfold betaN
    rw [two_mul, pow_add]
    field_simp
  rw [e]
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ rB (bseq b0 n) := pow_le_pow_right₀ (by norm_num) hrn
  have h2' : (0 : ℝ) ≤ 2 ^ n := by positivity
  apply div_le_div_of_nonneg_right _ (by norm_num)
  nlinarith

/-- **Lemma 8.8, without the nonemptiness hypothesis**: for every sufficiently large `X` there is a
generation `n ≥ n₁` such that `L_{b_n}(R) < X ≤ U_{b_n}(R)` for every generation-`n` endpoint `R`.
The thresholds come from the deterministic endpoint bounds `lo_n M ≤ R ≤ hi_n M`, so nonempty
generations are not needed. -/
theorem allscales_of_bounds : ∃ b₁ : ℕ, ∀ b0 ≥ b₁, ∀ M : ℕ, Odd M → 16 ^ b0 ≤ M →
    ∀ n₁ : ℕ, ∀ᶠ X : ℝ in atTop, ∃ n ≥ n₁, Admissible b0 M n X := by
  refine ⟨1000000, fun b0 hb0 M hM hM16 n₁ => ?_⟩
  classical
  have hM0 : 0 < M := hM.pos
  rw [Filter.eventually_atTop]
  refine ⟨betaN b0 M n₁ + 1, fun X hX => ?_⟩
  have hex : ∃ m, n₁ ≤ m ∧ X ≤ betaN b0 M m := by
    obtain ⟨m0, hm0⟩ := pow_unbounded_of_one_lt (4 * X) (by norm_num : (1 : ℝ) < 2)
    refine ⟨max m0 n₁, le_max_right _ _, ?_⟩
    have h1 := betaN_ge hb0 hM0 (max m0 n₁)
    have h2 : (2 : ℝ) ^ m0 ≤ 2 ^ (max m0 n₁) := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    linarith
  obtain ⟨hm1, hm2⟩ := Nat.find_spec hex
  have hne : Nat.find hex ≠ n₁ := by
    intro h
    rw [h] at hm2
    linarith
  have hprev : betaN b0 M (Nat.find hex - 1) < X := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at this
    exact this (by omega)
  have halpha := alpha_succ_lt_beta hb0 hM0 (Nat.find hex - 1)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at halpha
  exact ⟨Nat.find hex, hm1,
    admissible_of_between (by omega) hM hM16 (halpha.trans hprev) hm2⟩

/-! ## The terminal marked mass -/

/-- The function paired with the histogram at shift `u`:
`g_u = ∑_{w ∈ terminal b_n K_n u} T_{w,Q} ρ_{k_n} - lift(ρ_{k_n})` on `G_Q`, `Q = h_{b_n} + k_n`. -/
def termDiff (b0 n u : ℕ) (y : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 n))) : ℝ :=
  ∑ w ∈ terminal (bseq b0 n) (Kseq n) u,
    TwQ (hB (bseq b0 n) + kseq b0 n) (kseq b0 n) w (rhoX (kseq b0 n)) y -
      rhoX (kseq b0 n) (ZMod.cast y)

/-- The terminal marked mass minus `Z_n(M)`: each history contributes `W` times `g_u` at its
endpoint, `u` its selected shift. -/
theorem termMass_sub (b0 : ℕ) {M : ℕ} (hM : Odd M) (n : ℕ) (X : ℝ) :
    termMass b0 M n X - Zmark b0 M n = ∑ H ∈ hist b0 M n, wt H.flatten *
      termDiff b0 n (shiftOf (bseq b0 n) (endpt M H) X)
        ((endpt M H : ℕ) : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 n))) := by
  unfold termMass Zmark termDiff
  rw [← Finset.sum_sub_distrib]
  have hk : kseq b0 n ≤ hB (bseq b0 n) + kseq b0 n := Nat.le_add_left _ _
  refine Finset.sum_congr rfl fun H hH => ?_
  have hRo := endpt_odd hM hH
  rw [← mul_sub]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hT := mem_terminal.mp hw
    have hwp : w.Pos := hT.1.1
    rw [TwQ_natCast (Q := hB (bseq b0 n) + kseq b0 n) (t := kseq b0 n) (w := w)
      (by have := hT.2; omega)]
    split_ifs with hr
    · rw [Tw_natCast_of_realizes hwp hRo hr]
    · rw [Tw_natCast_of_not_realizes hwp hRo hr]
  · rw [ZMod.cast_natCast (pow_dvd_pow 3 hk)]

/-- One shift class: (8.8) and Lemma 8.3 for the terminal family of shift `u ≤ 2r_{b_n}`, with
the terminal rejection bound. -/
lemma sum_histo_abs_termDiff_le {b0 : ℕ} (hb0 : 200 ≤ b0) {CH C6 : ℝ}
    (hCH : ∀ M n q : ℕ, Odd M → 16 ^ b0 ≤ M → q ≤ 2 * bseq b0 n → ∀ f : ZMod (3 ^ q) → ℝ,
      |∑ y, histo b0 M n q y * f y| ≤ CH * (n + 1) ^ 3 * Gc ^ n * normL1 q f)
    (hTC : ∀ (V : Finset Word) (h k l : ℕ), PrefixFree V → (∀ w ∈ V, w.Pos ∧ w.length ≤ h) →
      1 ≤ k → 1 ≤ l → l ≤ h + k →
      normL1 (h + k) (fun y => ∑ w ∈ V, TwQ (h + k) k w (rhoX k) y - rhoX l (ZMod.cast y)) ≤
        2 / 3 * (C6 * (k : ℝ) ^ (-(6 : ℝ)) + C6 * (l : ℝ) ^ (-(6 : ℝ)) + (1 - pmass V)))
    {M : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M) (n : ℕ) {u : ℕ} (hu : u ≤ 2 * rB (bseq b0 n)) :
    ∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 n) y * |termDiff b0 n u y| ≤
      max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n * (2 / 3 *
        (2 * max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
          4 * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) +
            (1 / 2) ^ (Kseq n + 1))))) := by
  have hbn : 200 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
  have hq : hB (bseq b0 n) + kseq b0 n ≤ 2 * bseq b0 n := by unfold hB wB kseq; omega
  have h1 : |(∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 n) y * |termDiff b0 n u y|)| ≤
      CH * (n + 1) ^ 3 * Gc ^ n *
        normL1 (hB (bseq b0 n) + kseq b0 n) (fun y => |termDiff b0 n u y|) :=
    hCH M n _ hM hM16 hq (fun y => |termDiff b0 n u y|)
  have hnn : 0 ≤ ∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 n) y * |termDiff b0 n u y| :=
    Finset.sum_nonneg fun y _ => mul_nonneg (histo_nonneg _ _ _ _ _) (abs_nonneg _)
  rw [abs_of_nonneg hnn] at h1
  have hnorm : normL1 (hB (bseq b0 n) + kseq b0 n) (fun y => |termDiff b0 n u y|) =
      normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u) := by
    unfold normL1; simp only [abs_abs]
  rw [hnorm] at h1
  have hk1 : 1 ≤ kseq b0 n := by unfold kseq; omega
  have h2 : normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u) ≤
      2 / 3 * (C6 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) + C6 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
        (1 - pmass (terminal (bseq b0 n) (Kseq n) u))) :=
    hTC (terminal (bseq b0 n) (Kseq n) u) (hB (bseq b0 n)) (kseq b0 n) (kseq b0 n)
      (terminal_prefixFree _ _ _) (fun w hw => ⟨(mem_terminal.mp hw).1.1, (mem_terminal.mp hw).2⟩)
      hk1 hk1 (by omega)
  have h3 := one_sub_pmass_terminal_le hbn (Kseq n) hu
  have hk0 : 0 ≤ (kseq b0 n : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC6 : C6 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) ≤ max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
  have hN : normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u) ≤ 2 / 3 *
      (2 * max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
        4 * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) + (1 / 2) ^ (Kseq n + 1)) := by
    linarith
  have hN0 := normL1_nonneg _ (termDiff b0 n u)
  have hGn : 0 ≤ Gc ^ n := by unfold Gc; positivity
  have hn3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  have hX0 : 0 ≤ ((n : ℝ) + 1) ^ 3 * (Gc ^ n *
      normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u)) := by positivity
  calc ∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 n) y * |termDiff b0 n u y|
      ≤ CH * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
          normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u))) := by
        rw [show CH * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
          normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u))) = CH * (n + 1) ^ 3 * Gc ^ n *
            normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u) by ring]
        exact h1
    _ ≤ max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
          normL1 (hB (bseq b0 n) + kseq b0 n) (termDiff b0 n u))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hN hGn) hn3) (le_max_right _ _)

/-- The error of the terminal stage at generation `n`: `2r_{b_n} + 1` shift classes, each bounded
by (8.8), Lemma 8.3 and the terminal rejection bound. -/
def termErr (b0 : ℕ) (CH C6 : ℝ) (n : ℕ) : ℝ :=
  ((2 * rB (bseq b0 n) + 1 : ℕ) : ℝ) * (max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n * (2 / 3 *
    (2 * max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
      4 * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) +
        (1 / 2) ^ (Kseq n + 1))))))

/-- **The terminal mass is close to the marked mass:** for admissible `X`,
`|termMass - Z_n(M)| ≤ termErr`, summing the shift classes `u ≤ 2r_{b_n}` (point G9 of
checkpoint 06: the number of selected shifts is bounded by `2r_{b_n} + 1` rather than `σ_n + 1`). -/
theorem termMass_sub_le {b0 : ℕ} (hb0 : 200 ≤ b0) {CH C6 : ℝ}
    (hCH : ∀ M n q : ℕ, Odd M → 16 ^ b0 ≤ M → q ≤ 2 * bseq b0 n → ∀ f : ZMod (3 ^ q) → ℝ,
      |∑ y, histo b0 M n q y * f y| ≤ CH * (n + 1) ^ 3 * Gc ^ n * normL1 q f)
    (hTC : ∀ (V : Finset Word) (h k l : ℕ), PrefixFree V → (∀ w ∈ V, w.Pos ∧ w.length ≤ h) →
      1 ≤ k → 1 ≤ l → l ≤ h + k →
      normL1 (h + k) (fun y => ∑ w ∈ V, TwQ (h + k) k w (rhoX k) y - rhoX l (ZMod.cast y)) ≤
        2 / 3 * (C6 * (k : ℝ) ^ (-(6 : ℝ)) + C6 * (l : ℝ) ^ (-(6 : ℝ)) + (1 - pmass V)))
    {M : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M) {n : ℕ} {X : ℝ} (hX : Admissible b0 M n X) :
    |termMass b0 M n X - Zmark b0 M n| ≤ termErr b0 CH C6 n := by
  rw [termMass_sub b0 hM n X]
  have hr : ∀ H ∈ hist b0 M n,
      shiftOf (bseq b0 n) (endpt M H) X ∈ range (2 * rB (bseq b0 n) + 1) := by
    intro H hH
    have hR0 : 0 < endpt M H := (endpt_odd hM hH).pos
    obtain ⟨h1, h2⟩ := hX H hH
    have := (shiftOf_spec hR0 h1 h2).2.1
    rw [Finset.mem_range]; omega
  calc |∑ H ∈ hist b0 M n, wt H.flatten * termDiff b0 n (shiftOf (bseq b0 n) (endpt M H) X)
        ((endpt M H : ℕ) : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 n)))|
      ≤ ∑ H ∈ hist b0 M n, wt H.flatten * |termDiff b0 n (shiftOf (bseq b0 n) (endpt M H) X)
          ((endpt M H : ℕ) : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 n)))| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun H _ => ?_
        rw [abs_mul, abs_of_pos (wt_pos _)]
    _ ≤ ∑ H ∈ hist b0 M n, wt H.flatten * ∑ u ∈ range (2 * rB (bseq b0 n) + 1),
          |termDiff b0 n u ((endpt M H : ℕ) : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 n)))| :=
        Finset.sum_le_sum fun H hH => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun u => |termDiff b0 n u
            ((endpt M H : ℕ) : ZMod (3 ^ (hB (bseq b0 n) + kseq b0 n)))|)
            (fun u _ => abs_nonneg _) (hr H hH)) (wt_pos _).le
    _ = ∑ u ∈ range (2 * rB (bseq b0 n) + 1),
          ∑ y, histo b0 M n (hB (bseq b0 n) + kseq b0 n) y * |termDiff b0 n u y| := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        exact (sum_histo_mul b0 M n _ (fun y => |termDiff b0 n u y|)).symm
    _ ≤ ∑ _u ∈ range (2 * rB (bseq b0 n) + 1), max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n *
          (2 / 3 * (2 * max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
            4 * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) +
              (1 / 2) ^ (Kseq n + 1))))) :=
        Finset.sum_le_sum fun u hu => sum_histo_abs_termDiff_le hb0 hCH hTC hM hM16 n
          (by rw [Finset.mem_range] at hu; omega)
    _ = termErr b0 CH C6 n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl

/-- `b_n^{-e} ≤ ((200/201)^e)^n` once `b_0 ≥ 200`. -/
lemma inv_bseq_pow_le {b0 : ℕ} (hb0 : 200 ≤ b0) (e n : ℕ) :
    1 / (bseq b0 n : ℝ) ^ e ≤ ((200 / 201 : ℝ) ^ e) ^ n := by
  have hl := bseq_lower hb0 n
  have hb : (1 : ℝ) ≤ b0 := by exact_mod_cast (show 1 ≤ b0 by omega)
  have h1 : (201 / 200 : ℝ) ^ n ≤ bseq b0 n :=
    le_trans (le_mul_of_one_le_left (by positivity) hb) hl
  have h2 : ((201 / 200 : ℝ) ^ n) ^ e ≤ (bseq b0 n : ℝ) ^ e := pow_le_pow_left₀ (by positivity) h1 e
  have ee : ((200 / 201 : ℝ) ^ e) ^ n * ((201 / 200 : ℝ) ^ n) ^ e = 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm e n, ← mul_pow]; norm_num
  have hbpos : (0 : ℝ) < (bseq b0 n : ℝ) ^ e := by
    have : (0 : ℝ) < bseq b0 n := lt_of_lt_of_le (by positivity) h1
    positivity
  rw [div_le_iff₀ hbpos]
  calc (1 : ℝ) = ((200 / 201 : ℝ) ^ e) ^ n * ((201 / 200 : ℝ) ^ n) ^ e := ee.symm
    _ ≤ ((200 / 201 : ℝ) ^ e) ^ n * (bseq b0 n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `b_n k_n^{-6} ≤ 8^6 ((200/201)^5)^n`. -/
lemma bseq_mul_kseq_rpow_le {b0 : ℕ} (hb0 : 200 ≤ b0) (n : ℕ) :
    (bseq b0 n : ℝ) * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) ≤ 8 ^ 6 * ((200 / 201 : ℝ) ^ 5) ^ n := by
  have hbn : 200 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
  have h8 : bseq b0 n ≤ 8 * kseq b0 n := by unfold kseq; omega
  have hk1 : 1 ≤ kseq b0 n := by unfold kseq; omega
  have hk : (0 : ℝ) < kseq b0 n := by exact_mod_cast hk1
  have hb : (0 : ℝ) < bseq b0 n := by exact_mod_cast (show 0 < bseq b0 n by omega)
  have h8' : (bseq b0 n : ℝ) ≤ 8 * kseq b0 n := by exact_mod_cast h8
  rw [rpow_neg_six_eq hk.le]
  have h1 : (bseq b0 n : ℝ) * (1 / (kseq b0 n : ℝ) ^ 6) ≤ 8 ^ 6 * (1 / (bseq b0 n : ℝ) ^ 5) := by
    rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (bseq b0 n : ℝ) * (bseq b0 n : ℝ) ^ 5 = (bseq b0 n : ℝ) ^ 6 := by ring
      _ ≤ (8 * (kseq b0 n : ℝ)) ^ 6 := pow_le_pow_left₀ hb.le h8' 6
      _ = 8 ^ 6 * (kseq b0 n : ℝ) ^ 6 := by ring
  exact h1.trans (mul_le_mul_of_nonneg_left (inv_bseq_pow_le hb0 5 n) (by norm_num))

/-- `b exp(-e_b²/(6b)) ≤ 7! 240000^7 / b^6` for `b ≥ 200` (`e_b ≥ b/200`, `e^y ≥ y^7/7!`). -/
lemma bseq_mul_exp_le {b : ℕ} (hb : 200 ≤ b) :
    (b : ℝ) * Real.exp (-((eB b : ℝ) ^ 2) / (6 * b)) ≤ 5040 * 240000 ^ 7 / (b : ℝ) ^ 6 := by
  have hb' : (200 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  have he : (b : ℝ) ≤ 200 * eB b := by
    have : b ≤ 200 * eB b := by unfold eB; omega
    exact_mod_cast this
  set y : ℝ := (eB b : ℝ) ^ 2 / (6 * b) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyb : (b : ℝ) / 240000 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul he he hbpos.le (by positivity)]
  have hexp := Real.pow_div_factorial_le_exp y hy0 7
  have hF : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
  have hlow : (b : ℝ) ^ 7 / (240000 ^ 7 * 5040) ≤ Real.exp y := by
    calc (b : ℝ) ^ 7 / (240000 ^ 7 * 5040) = ((b : ℝ) / 240000) ^ 7 / 5040 := by
          rw [div_pow, div_div]
      _ ≤ y ^ 7 / 5040 := by gcongr
      _ = y ^ 7 / Nat.factorial 7 := by rw [hF]
      _ ≤ Real.exp y := hexp
  have hneg : -((eB b : ℝ) ^ 2) / (6 * b) = -y := by rw [hy, neg_div]
  rw [hneg, Real.exp_neg]
  have hinv : (Real.exp y)⁻¹ ≤ (240000 ^ 7 * 5040) / (b : ℝ) ^ 7 := by
    rw [← inv_div]; exact inv_anti₀ (by positivity) hlow
  calc (b : ℝ) * (Real.exp y)⁻¹ ≤ b * ((240000 ^ 7 * 5040) / (b : ℝ) ^ 7) :=
        mul_le_mul_of_nonneg_left hinv hbpos.le
    _ = 5040 * 240000 ^ 7 / (b : ℝ) ^ 6 := by field_simp

lemma rho3_lt_one : (101 / 100 : ℝ) * q2 < 1 := by
  apply lt_of_pow_lt_pow_left₀ 10 (by norm_num : (0 : ℝ) ≤ 1)
  unfold q2
  rw [mul_pow, mul_pow, two_rpow_neg_tenth_pow_ten]
  unfold Gc; norm_num

/-- `termErr ≤ C (n+1)^3 [ρ₁^n + q₁^n + ρ₃^n]` with `ρ₁ = G (200/201)^5`, `ρ₃ = (101/100) q₂`. -/
lemma termErr_le {b0 : ℕ} (hb0 : 200 ≤ b0) (CH C6 : ℝ) (n : ℕ) :
    termErr b0 CH C6 n ≤ max CH 0 * (2 / 3) * (((n : ℝ) + 1) ^ 3 *
      (6 * max C6 0 * (8 ^ 6 * (Gc * (200 / 201) ^ 5) ^ n) + 12 * (5040 * 240000 ^ 7 * q1 ^ n) +
        3 * (b0 * (101 / 100 * q2) ^ n))) := by
  have hbn : 200 ≤ bseq b0 n := hb0.trans (le_bseq b0 n)
  have h3b : ((2 * rB (bseq b0 n) + 1 : ℕ) : ℝ) ≤ 3 * bseq b0 n := by
    have : 2 * rB (bseq b0 n) + 1 ≤ 3 * bseq b0 n := by unfold rB wB; omega
    exact_mod_cast this
  have hGn : 0 ≤ Gc ^ n := by unfold Gc; positivity
  have hC6 : (0 : ℝ) ≤ max C6 0 := le_max_right _ _
  have hCH : (0 : ℝ) ≤ max CH 0 := le_max_right _ _
  have hk0 : 0 ≤ (kseq b0 n : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hE0 : 0 ≤ Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) := (Real.exp_pos _).le
  have hh0 : (0 : ℝ) ≤ (1 / 2) ^ (Kseq n + 1) := by positivity
  have hn3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  have t1 : (bseq b0 n : ℝ) * (Gc ^ n * (kseq b0 n : ℝ) ^ (-(6 : ℝ))) ≤
      8 ^ 6 * (Gc * (200 / 201) ^ 5) ^ n := by
    have := bseq_mul_kseq_rpow_le hb0 n
    calc (bseq b0 n : ℝ) * (Gc ^ n * (kseq b0 n : ℝ) ^ (-(6 : ℝ)))
        = Gc ^ n * ((bseq b0 n : ℝ) * (kseq b0 n : ℝ) ^ (-(6 : ℝ))) := by ring
      _ ≤ Gc ^ n * (8 ^ 6 * ((200 / 201 : ℝ) ^ 5) ^ n) := mul_le_mul_of_nonneg_left this hGn
      _ = 8 ^ 6 * (Gc * (200 / 201) ^ 5) ^ n := by rw [mul_pow]; ring
  have t2 : (bseq b0 n : ℝ) * (Gc ^ n * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n))) ≤
      5040 * 240000 ^ 7 * q1 ^ n := by
    have h1 := bseq_mul_exp_le hbn
    have h2 := inv_bseq_pow_le hb0 6 n
    calc (bseq b0 n : ℝ) * (Gc ^ n * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)))
        = Gc ^ n * ((bseq b0 n : ℝ) *
            Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n))) := by ring
      _ ≤ Gc ^ n * (5040 * 240000 ^ 7 / (bseq b0 n : ℝ) ^ 6) := mul_le_mul_of_nonneg_left h1 hGn
      _ = 5040 * 240000 ^ 7 * (Gc ^ n * (1 / (bseq b0 n : ℝ) ^ 6)) := by ring
      _ ≤ 5040 * 240000 ^ 7 * (Gc ^ n * ((200 / 201 : ℝ) ^ 6) ^ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hGn) (by norm_num)
      _ = 5040 * 240000 ^ 7 * q1 ^ n := by unfold q1; rw [mul_pow]
  have t3 : (bseq b0 n : ℝ) * (Gc ^ n * (1 / 2) ^ (Kseq n + 1)) ≤ b0 * (101 / 100 * q2) ^ n := by
    have h1 := bseq_upper b0 n
    have h2 := Gc_pow_mul_half_pow_le n
    calc (bseq b0 n : ℝ) * (Gc ^ n * (1 / 2) ^ (Kseq n + 1))
        ≤ (b0 * (101 / 100 : ℝ) ^ n) * (Gc ^ n * (1 / 2) ^ (Kseq n + 1)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (b0 * (101 / 100 : ℝ) ^ n) * q2 ^ n := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = b0 * (101 / 100 * q2) ^ n := by rw [mul_pow]; ring
  unfold termErr
  calc ((2 * rB (bseq b0 n) + 1 : ℕ) : ℝ) * (max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n * (2 / 3 *
        (2 * max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
          4 * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) +
            (1 / 2) ^ (Kseq n + 1))))))
      ≤ (3 * bseq b0 n) * (max CH 0 * (((n : ℝ) + 1) ^ 3 * (Gc ^ n * (2 / 3 *
        (2 * max C6 0 * (kseq b0 n : ℝ) ^ (-(6 : ℝ)) +
          4 * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)) +
            (1 / 2) ^ (Kseq n + 1)))))) := mul_le_mul_of_nonneg_right h3b (by positivity)
    _ = max CH 0 * (2 / 3) * (((n : ℝ) + 1) ^ 3 *
          (6 * max C6 0 * ((bseq b0 n : ℝ) * (Gc ^ n * (kseq b0 n : ℝ) ^ (-(6 : ℝ)))) +
            12 * ((bseq b0 n : ℝ) *
              (Gc ^ n * Real.exp (-((eB (bseq b0 n) : ℝ) ^ 2) / (6 * bseq b0 n)))) +
            3 * ((bseq b0 n : ℝ) * (Gc ^ n * (1 / 2) ^ (Kseq n + 1))))) := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hn3
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left t1 (by positivity))
          (mul_le_mul_of_nonneg_left t2 (by norm_num))) (mul_le_mul_of_nonneg_left t3 (by norm_num))

/-- The terminal error tends to `0`, uniformly in the seed. -/
lemma termErr_eventually_le {b0 : ℕ} (hb0 : 200 ≤ b0) (CH C6 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, termErr b0 CH C6 n ≤ ε := by
  have hr1 : 0 ≤ Gc * (200 / 201 : ℝ) ^ 5 := by unfold Gc; positivity
  have hr1' : Gc * (200 / 201 : ℝ) ^ 5 < 1 := by unfold Gc; norm_num
  have hr3 : 0 ≤ (101 / 100 : ℝ) * q2 := by have := q2_nonneg; positivity
  have s1 := summable_cube_geom hr1 hr1'
  have s2 := summable_cube_geom q1_nonneg q1_lt_one
  have s3 := summable_cube_geom hr3 rho3_lt_one
  have hF : Summable (fun n : ℕ => max CH 0 * (2 / 3) * (((n : ℝ) + 1) ^ 3 *
      (6 * max C6 0 * (8 ^ 6 * (Gc * (200 / 201) ^ 5) ^ n) + 12 * (5040 * 240000 ^ 7 * q1 ^ n) +
        3 * (b0 * (101 / 100 * q2) ^ n)))) := by
    have := ((s1.mul_left (6 * max C6 0 * 8 ^ 6)).add (s2.mul_left (12 * (5040 * 240000 ^ 7)))).add
      (s3.mul_left (3 * (b0 : ℝ)))
    refine (this.mul_left (max CH 0 * (2 / 3))).congr fun n => ?_
    ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((hF.tendsto_atTop_zero).eventually (Iic_mem_nhds hε))
  exact ⟨N, fun n hn => (termErr_le hb0 CH C6 n).trans (hN n hn)⟩

/-- **The terminal marked mass** (§8.4, the unlabelled paragraph before Lemma 8.8): there are
`a₀ > 0`, a generation `n₁` and a residue class `y mod 3^Q` such that for every odd seed
`M ≥ 16^{b_0}` with `M ≡ y`, every `n ≥ n₁` and every `X` admissible at generation `n`, the
terminal marked mass is at least `a₀`. (The paper's `a₀ = p_∞/4`; here `a₀` is half the bound of
`favourable_residue`.) -/
theorem terminal_mass (hA1 : OffsetMixing) : ∃ b₁ : ℕ, ∀ b0 ≥ b₁,
    ∃ (a₀ : ℝ) (n₁ Q : ℕ) (y : ZMod (3 ^ Q)), 0 < a₀ ∧ ∀ M : ℕ, Odd M → 16 ^ b0 ≤ M →
      (M : ZMod (3 ^ Q)) = y → ∀ n ≥ n₁, ∀ X : ℝ, Admissible b0 M n X → a₀ ≤ termMass b0 M n X := by
  obtain ⟨b₂, hFR⟩ := favourable_residue hA1
  obtain ⟨b₃, hHP⟩ := histogram_pairing
  obtain ⟨C6, hTC⟩ := transfer_comparison hA1 (A := 6) (by norm_num)
  refine ⟨max (max b₂ b₃) 200, fun b0 hb0 => ?_⟩
  have hb2 : b₂ ≤ b0 := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hb0)
  have hb3 : b₃ ≤ b0 := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hb0)
  have hb200 : 200 ≤ b0 := le_trans (le_max_right _ _) hb0
  obtain ⟨p, nst, Q, y, hp, hZ⟩ := hFR b0 hb2
  obtain ⟨CH, hCH⟩ := hHP b0 hb3
  obtain ⟨N, hN⟩ := termErr_eventually_le hb200 CH C6 (by positivity : (0 : ℝ) < p / 2)
  refine ⟨p / 2, max nst N, Q, y, by positivity, fun M hM hM16 hMy n hn X hX => ?_⟩
  have h1 := hZ M hM hM16 hMy n (le_of_max_le_left hn)
  have h2 := termMass_sub_le hb200 hCH hTC hM hM16 hX
  have h3 := hN n (le_of_max_le_right hn)
  have h4 := neg_abs_le (termMass b0 M n X - Zmark b0 M n)
  linarith

/-- **Lemma 8.8 [`lem:allscales`]**: for every sufficiently large `X` there is a generation
`n ≥ n₁` such that `L_{b_n}(R) < X ≤ U_{b_n}(R)` for every generation-`n` endpoint `R`. The
nonemptiness hypothesis of the appendix statement, used in the paper's argument, is not needed
(`allscales_of_bounds`). -/
theorem allscales : ∃ b₁ : ℕ, ∀ b0 ≥ b₁, ∀ M : ℕ, Odd M → 16 ^ b0 ≤ M →
    (∀ n, (hist b0 M n).Nonempty) → ∀ n₁ : ℕ, ∀ᶠ X : ℝ in atTop, ∃ n ≥ n₁, Admissible b0 M n X := by
  obtain ⟨b₁, h⟩ := allscales_of_bounds
  exact ⟨b₁, fun b0 hb0 M hM hM16 _ => h b0 hb0 M hM hM16⟩

end Positivity
end CollatzCLT
