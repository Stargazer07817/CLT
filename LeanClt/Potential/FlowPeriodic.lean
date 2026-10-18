import LeanClt.Potential.Rays
import LeanClt.Exceptional.Corollaries

/-!
# Proposition 7.3 [`prop:flow`], the periodic case

Stage 6 of the checkpoint-17 plan. Let `n` be periodic, `T^p(n) = n` with `p ≥ 1`, with cycle
`𝒵 = {T^j n : j < p}` (`fwdOrbit n`, for any period `p`) and merging class `C(n)`.

* `P_T(n) = C(n)` (`mergeClass_eq_pred_of_periodic`), so `h(n) = π_{C(n)}`.
* The preimages of `n` are `2n` and, when `n ≡ 4 (6)`, `(n-1)/3` (`sum_pre`). Exactly one of them lies
  on the cycle, the cycle predecessor `z' = T^{p-1}(n)`: any preimage `m ∈ 𝒵` satisfies
  `T^{p-1}(n) = T^{p-1}(T m) = T^p(m) = m` (`cycle_pre_unique`). Since `P_T(z') = P_T(n)`, the defect
  of (7.2, `eq:flow`) is the sum of `h` over the off-cycle preimages, which is `≥ 0`.
* The class is the disjoint union of the finite cycle and the basins `P_T(m)` of the off-cycle
  preimages `m` of the cycle vertices: a source not on the cycle enters it for the first time from
  such an `m`; two such basins are disjoint because after `m` the orbit stays on the cycle; the cycle
  has density `0`. Finite additivity gives `∑_{z ∈ 𝒵} ∑_{m ∈ T^{-1}(z) \ 𝒵} h(m) = π_{C(n)}`.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-- A finite set has density `0`. -/
lemma hasDensity_finset (s : Finset ℕ) : HasDensity (↑s : Set ℕ) 0 := by
  refine hasDensity_zero_of_le (g := fun _ => (s.card : ℝ)) ?_ (Eventually.of_forall fun X => ?_)
  · have := (tendsto_const_nhds (x := (s.card : ℝ))).div_atTop tendsto_natCast_atTop_atTop
    simpa using this
  · have : window (↑s) X ⊆ s := fun a ha => by rw [mem_window] at ha; exact ha.2
    exact_mod_cast Finset.card_le_card this

/-- A preimage of `z` is at most `2z`. -/
lemma le_two_mul_of_T_eq {m z : ℕ} (h : T m = z) : m ≤ 2 * z := by
  rcases T_eq_iff.mp h with h | ⟨-, h⟩ <;> omega

/-- The forward orbit is closed under `T`. -/
lemma fwdOrbit_iterate_mem {n x : ℕ} (hx : x ∈ fwdOrbit n) (k : ℕ) : T^[k] x ∈ fwdOrbit n := by
  obtain ⟨j, rfl⟩ := hx
  refine ⟨k + j, ?_⟩
  simp only [Function.iterate_add_apply]

/-- On a cycle of period `p`, `T^s(n) = T^{s mod p}(n)`. -/
lemma cycle_iter_mod {n p : ℕ} (hcyc : T^[p] n = n) (s : ℕ) : T^[s] n = T^[s % p] n := by
  conv_lhs => rw [← Nat.mod_add_div s p]
  rw [Function.iterate_add_apply, iterate_period_mul hcyc]

/-- The cycle is `{T^j n : j < p}`, for any period `p`. -/
lemma mem_cycle_iff {n p x : ℕ} (hp : 0 < p) (hcyc : T^[p] n = n) :
    x ∈ (range p).image (fun j => T^[j] n) ↔ x ∈ fwdOrbit n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j % p, Finset.mem_range.mpr (Nat.mod_lt _ hp), (cycle_iter_mod hcyc j).symm⟩

/-- Every point of the cycle of `n > 0` reaches `n`. -/
lemma cycle_mem_pred {n p x : ℕ} (hn : 0 < n) (hp : 0 < p) (hcyc : T^[p] n = n)
    (hx : x ∈ fwdOrbit n) : x ∈ Pred T n := by
  obtain ⟨j, rfl⟩ := hx
  refine ⟨iterate_T_pos hn j, (p - 1) * j, ?_⟩
  rw [← Function.iterate_add_apply, show (p - 1) * j + j = p * j by
    rcases p with _ | p
    · omega
    · simp only [Nat.add_sub_cancel]; ring, iterate_period_mul hcyc]

/-- The only preimage of `n` on its cycle is `T^{p-1}(n)`. -/
lemma cycle_pre_unique {n p m : ℕ} (hp : 0 < p) (hcyc : T^[p] n = n) (hm : m ∈ fwdOrbit n)
    (hTm : T m = n) : m = T^[p - 1] n := by
  obtain ⟨a, ha⟩ := hm
  have ha' : T^[a] n = m := ha
  have h1 : T^[p] m = m := by
    rw [← ha', ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hcyc]
  rw [← hTm, ← Function.iterate_succ_apply, show (p - 1).succ = p by omega, h1]

open Classical in
/-- The preimages of `n > 0`: `2n`, and `(n-1)/3` when `n ≡ 4 (6)`. -/
lemma sum_pre (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ m ∈ (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n), f m =
      f (2 * n) + (if n % 6 = 4 then f ((n - 1) / 3) else 0) := by
  have hset : (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n) =
      if n % 6 = 4 then {2 * n, (n - 1) / 3} else {2 * n} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    split_ifs with h6
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, hT⟩
        rcases T_eq_iff.mp hT with h | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr (by omega)
      · rintro (rfl | rfl)
        · exact ⟨by omega, by omega, T_two_mul n⟩
        · exact ⟨by omega, by omega, T_odd_preimage h6⟩
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, hT⟩
        rcases T_eq_iff.mp hT with h | ⟨hodd, h⟩
        · exact h
        · exfalso
          rw [Nat.not_even_iff_odd] at hodd
          obtain ⟨q, hq⟩ := hodd
          omega
      · rintro rfl
        exact ⟨by omega, by omega, T_two_mul n⟩
  rw [hset]
  split_ifs with h6
  · rw [Finset.sum_pair (by omega)]
  · rw [Finset.sum_singleton, add_zero]

open Classical in
/-- **Proposition 7.3 [`prop:flow`], the periodic case.** `T^{-1}(z) \ 𝒵` is written as the
positive `m ≤ 2z` with `T m = z` off the cycle `fwdOrbit n`; the cycle as `{T^j n : j < p}`. -/
theorem flow_periodic (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (hcyc : T^[p] n = n) :
    HasDensity (mergeClass n) (natDens (mergeClass n)) ∧ hpot n = natDens (mergeClass n) ∧
    hpot (2 * n) + (if n % 6 = 4 then hpot ((n - 1) / 3) else 0) - hpot n =
      ∑ m ∈ (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n ∧ m ∉ fwdOrbit n), hpot m ∧
    0 ≤ ∑ m ∈ (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n ∧ m ∉ fwdOrbit n), hpot m ∧
    ∑ z ∈ (range p).image (fun j => T^[j] n),
        ∑ m ∈ (range (2 * z + 1)).filter (fun m => 0 < m ∧ T m = z ∧ m ∉ fwdOrbit n), hpot m =
      natDens (mergeClass n) := by
  have hper : IsPeriodic n := ⟨p, hp, hcyc⟩
  have hclass : mergeClass n = Pred T n := mergeClass_eq_pred_of_periodic hper
  have hP := hasDensity_hpot hTM hTP hθ n hn
  have hnat : natDens (mergeClass n) = hpot n := by rw [hclass]; rfl
  -- the cycle predecessor `z' = T^{p-1}(n)`
  set z' := T^[p - 1] n with hz'
  have hTz' : T z' = n := by
    rw [hz', ← Function.iterate_succ_apply' T (p - 1) n, show (p - 1).succ = p by omega, hcyc]
  have hz'orb : z' ∈ fwdOrbit n := ⟨p - 1, rfl⟩
  have hz'pos : 0 < z' := iterate_T_pos hn _
  have hpz' : hpot z' = hpot n := by
    have : Pred T z' = Pred T n := by
      ext N
      constructor
      · intro h; exact pred_trans h ⟨hz'pos, 1, by simpa using hTz'⟩
      · intro h; exact pred_trans h ⟨hn, p - 1, rfl⟩
    rw [hpot, hpot, this]
  -- the off-cycle preimages of `n` are the preimages other than `z'`
  have hfilt : (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n ∧ m ∉ fwdOrbit n) =
      ((range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n)).erase z' := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro ⟨hm, hmpos, hTm, hnot⟩
      exact ⟨fun h => hnot (h ▸ hz'orb), hm, hmpos, hTm⟩
    · rintro ⟨hne, hm, hmpos, hTm⟩
      exact ⟨hm, hmpos, hTm, fun horb => hne (cycle_pre_unique hp hcyc horb hTm)⟩
  have hz'mem : z' ∈ (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := le_two_mul_of_T_eq hTz'; omega, hz'pos, hTz'⟩
  have hthird : hpot (2 * n) + (if n % 6 = 4 then hpot ((n - 1) / 3) else 0) - hpot n =
      ∑ m ∈ (range (2 * n + 1)).filter (fun m => 0 < m ∧ T m = n ∧ m ∉ fwdOrbit n), hpot m := by
    rw [hfilt, Finset.sum_erase_eq_sub hz'mem, sum_pre hpot hn, hpz']
  refine ⟨by rw [hnat, hclass]; exact hP, hnat.symm, hthird,
    Finset.sum_nonneg fun m _ => hpot_nonneg hTM hTP hθ m, ?_⟩
  -- the partition of the class into the cycle and the off-cycle basins
  set Zf := (range p).image (fun j => T^[j] n) with hZf
  have hPdisj : (Zf : Set ℕ).PairwiseDisjoint
      (fun z => (range (2 * z + 1)).filter (fun m => 0 < m ∧ T m = z ∧ m ∉ fwdOrbit n)) := by
    intro z _ z' _ hzz'
    refine Finset.disjoint_left.mpr fun m h1 h2 => hzz' ?_
    rw [Finset.mem_filter] at h1 h2
    exact h1.2.2.1.symm.trans h2.2.2.1
  set Q := Zf.biUnion
    (fun z => (range (2 * z + 1)).filter (fun m => 0 < m ∧ T m = z ∧ m ∉ fwdOrbit n)) with hQ
  have hdouble : ∑ z ∈ Zf,
      ∑ m ∈ (range (2 * z + 1)).filter (fun m => 0 < m ∧ T m = z ∧ m ∉ fwdOrbit n), hpot m =
      ∑ m ∈ Q, hpot m := (Finset.sum_biUnion hPdisj).symm
  rw [hdouble, hnat]
  -- membership in `Q`
  have hQmem : ∀ m ∈ Q, 0 < m ∧ T m ∈ fwdOrbit n ∧ m ∉ fwdOrbit n := by
    intro m hm
    rw [hQ, Finset.mem_biUnion] at hm
    obtain ⟨z, hz, hmz⟩ := hm
    rw [Finset.mem_filter] at hmz
    obtain ⟨-, hmpos, hTm, hoff⟩ := hmz
    exact ⟨hmpos, hTm ▸ (mem_cycle_iff hp hcyc).mp hz, hoff⟩
  -- the cover
  have hU : Pred T n = (↑Zf : Set ℕ) ∪ ⋃ m ∈ Q, Pred T m := by
    ext N
    constructor
    · intro hN
      by_cases hNorb : N ∈ fwdOrbit n
      · exact Or.inl (Finset.mem_coe.mpr ((mem_cycle_iff hp hcyc).mpr hNorb))
      · right
        obtain ⟨hNpos, t, ht⟩ := hN
        have hex : ∃ s, T^[s] N ∈ fwdOrbit n := ⟨t, ht ▸ ⟨0, rfl⟩⟩
        set s := Nat.find hex with hs
        have hsspec : T^[s] N ∈ fwdOrbit n := Nat.find_spec hex
        have hs0 : s ≠ 0 := fun h => hNorb (by rw [h] at hsspec; simpa using hsspec)
        set m := T^[s - 1] N with hm
        have hmnot : m ∉ fwdOrbit n := Nat.find_min hex (by omega : s - 1 < s)
        have hTm : T m = T^[s] N := by
          rw [hm, ← Function.iterate_succ_apply' T (s - 1) N, show (s - 1).succ = s by omega]
        have hmpos : 0 < m := iterate_T_pos hNpos _
        simp only [Set.mem_iUnion]
        refine ⟨m, ?_, ⟨hNpos, s - 1, rfl⟩⟩
        rw [hQ, Finset.mem_biUnion]
        refine ⟨T m, (mem_cycle_iff hp hcyc).mpr (hTm ▸ hsspec), ?_⟩
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := le_two_mul_of_T_eq (rfl : T m = T m); omega, hmpos, rfl, hmnot⟩
    · rintro (h | h)
      · exact cycle_mem_pred hn hp hcyc ((mem_cycle_iff hp hcyc).mp (Finset.mem_coe.mp h))
      · simp only [Set.mem_iUnion] at h
        obtain ⟨m, hmQ, hNm⟩ := h
        obtain ⟨hmpos, hTmorb, -⟩ := hQmem m hmQ
        exact pred_trans hNm (pred_trans ⟨hmpos, 1, by simp⟩ (cycle_mem_pred hn hp hcyc hTmorb))
  -- the basins are pairwise disjoint, and disjoint from the cycle
  have hdisjQ : (Q : Set ℕ).PairwiseDisjoint (fun m => Pred T m) := by
    intro m hm m' hm' hne
    obtain ⟨-, hTm, -⟩ := hQmem m hm
    obtain ⟨-, hTm', hoff'⟩ := hQmem m' hm'
    obtain ⟨-, -, hoff⟩ := hQmem m hm
    refine Set.disjoint_left.mpr fun N h1 h2 => ?_
    obtain ⟨-, a, ha⟩ := h1
    obtain ⟨-, b, hb⟩ := h2
    rcases lt_trichotomy a b with hab | rfl | hab
    · apply hoff'
      rw [← hb, show b = (b - a - 1) + 1 + a by omega, Function.iterate_add_apply,
        Function.iterate_add_apply, ha]
      exact fwdOrbit_iterate_mem (by simpa using hTm) _
    · exact hne (ha.symm.trans hb)
    · apply hoff
      rw [← ha, show a = (a - b - 1) + 1 + b by omega, Function.iterate_add_apply,
        Function.iterate_add_apply, hb]
      exact fwdOrbit_iterate_mem (by simpa using hTm') _
  have hdisj0 : Disjoint (↑Zf : Set ℕ) (⋃ m ∈ Q, Pred T m) := by
    refine Set.disjoint_left.mpr fun N hNZ hNU => ?_
    simp only [Set.mem_iUnion] at hNU
    obtain ⟨m, hmQ, -, a, ha⟩ := hNU
    obtain ⟨-, -, hoff⟩ := hQmem m hmQ
    exact hoff (ha ▸ fwdOrbit_iterate_mem ((mem_cycle_iff hp hcyc).mp (Finset.mem_coe.mp hNZ)) a)
  -- finite additivity
  have hQd : HasDensity (⋃ m ∈ Q, Pred T m) (∑ m ∈ Q, hpot m) :=
    hasDensity_biUnion Q hdisjQ fun m hm => hasDensity_hpot hTM hTP hθ m (hQmem m hm).1
  have hall := (hasDensity_finset Zf).union hdisj0 hQd
  rw [← hU] at hall
  have := hP.unique hall
  linarith

end CollatzCLT
