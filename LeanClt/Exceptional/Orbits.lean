import LeanClt.Exceptional.Defs
import LeanClt.Transfer.Transport
import LeanClt.Sampling.Lemma64

/-!
# Orbit combinatorics for Theorem 1.3, Theorems 6.7–6.8 and Corollaries 1.5–1.6

Everything here is unconditional: statements about single `T`-orbits, with no sampling.

* **Transport and doubling** (§6.6). `A_K` with the clock `-τ_K` and reward `(1, 1)` has the transport
  property at every threshold `x ≥ K` (`transport_AK`) and is doubling compatible (`doubling_AK`); a
  merging class with the zero clock and reward `(0, 0)` has both at every threshold
  (`transport_class`, `doubling_class`). The first two are instances of `transport_reach` and
  `doubling_reach`, for the basin of any set of integers `≤ x₀`.
* **Rays** (§6.7). For a nonrepeating ray `a_j = T^j(a)` with class `C`: `{n ∈ C : J_R(n) ≤ j} =
  P_T(a_j)` and `τ_{T,a_j} = e_R + j - J_R` on it (`ray_identities`); `C ∩ A_K ⊆ P_T(a_j)` for all
  large `j` (`classAK_subset_pred`); and late ray points are prime to 3
  (`eventually_not_three_dvd`, which holds for every positive orbit).
* **Cycles.** For a periodic `b` of period `p`: the basin of the cycle is `P_T(b)` (`reach_cycle`), and
  `0 ≤ τ_{T,b} - (entry time into the cycle) ≤ p - 1` (`hit_le_entry_cycle`). Two periodic points of
  one class lie on the same cycle (`fwdOrbit_eq_of_periodic_merge`).
* **The exceptional set** (Corollary 1.5 [`cor:dichotomy`]): `P_T(b) ⊆ E` for `b ∈ E`
  (`pred_subset_exc`), and every `n ∈ E` lies in `P_T(b)` for some `b ∈ E` prime to 3
  (`exists_three_free_basin`).
* **Reference orbits** (Corollary 1.6 [`cor:unconditional`]): an admissible choice exists
  (`refChoice_exists`); `ε` is finite (`eps_finite`); changing the reference orbit of a class changes
  `ε` on the class by a bounded amount, for every class (`ref_change`, stronger than the paper, which
  states it for divergent classes); and on `P_T(1)`, `0 ≤ τ_{T,1} - ε ≤ 2` (`eps_class_one`), because
  the reference orbit of the class of 1 is forced to be `{1, 4, 2}` (`fwdOrbit_one`).
-/

open Function

namespace CollatzCLT

/-! ## Elementary orbit facts -/

lemma T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by
  unfold T
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    omega
  · omega

lemma iterate_T_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < T^[k] n := by
  induction k with
  | zero => simpa using hn
  | succ k ih => rw [iterate_succ_apply']; exact T_pos ih

/-- Reaching `m` and then `b`. -/
lemma pred_trans {n m b : ℕ} (hn : n ∈ Pred T m) (hm : m ∈ Pred T b) : n ∈ Pred T b := by
  obtain ⟨h0, i, hi⟩ := hn
  obtain ⟨-, j, hj⟩ := hm
  exact ⟨h0, j + i, by rw [iterate_add_apply, hi, hj]⟩

/-- A periodic point returns to itself along multiples of its period. -/
lemma iterate_period_mul {b p : ℕ} (hp : T^[p] b = b) (k : ℕ) : T^[p * k] b = b := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, iterate_add_apply, hp, ih]

lemma isPeriodic_one : IsPeriodic 1 := ⟨3, by norm_num, by decide⟩

/-! ## Transport and doubling (§6.6) -/

/-- **Transport for a basin.** If every point of `S` is at most `x₀`, the basin of `S` with the
clock `-entry S` and reward `(1, 1)` has the transport property at every threshold `x ≥ x₀`: the
early segment of a source stays above `x ≥ x₀`, so it does not meet `S`, and entry times add. -/
theorem transport_reach {S : Set ℕ} {x₀ : ℝ} (hS : ∀ m ∈ S, (m : ℝ) ≤ x₀) :
    Transport (Reach S) (fun n => -(entry S n : ℝ)) 1 1 x₀ := by
  intro x hx hm1 N hN _ hmT _
  set r := passT x N - mT x
  obtain ⟨hTb, hTst⟩ := T_blocks hN r
  have hab := early_above hm1 hmT
  have hav : ∀ j < wsum (vword N) r + r, T^[j] N ∉ S := by
    intro j hj hjS
    obtain ⟨i, hi, hle⟩ := hTst j hj.le
    have h1 := hab i hi
    have h2 : (U^[i] N : ℝ) ≤ x₀ := le_trans (by exact_mod_cast hle) (hS _ hjS)
    linarith
  obtain ⟨hiff, hhit⟩ := reach_shift hTb hav hN.pos (odd_U_iterate hN r).pos
  refine ⟨hiff, fun hNA => ?_⟩
  simp only [hhit hNA]
  push_cast
  ring

/-- **Doubling compatibility for a basin**, when `2n ∉ S` for `n ≥ n₀`: then `T(2n) = n` gives
`entry S (2n) = entry S n + 1`. -/
theorem doubling_reach {S : Set ℕ} {n0 : ℕ} (hn0 : 0 < n0) (hS : ∀ n, n0 ≤ n → 2 * n ∉ S) :
    DoublingCompatible (Reach S) (fun n => -(entry S n : ℝ)) 1 := by
  refine ⟨n0, fun n hn => ?_⟩
  have hstep : T^[1] (2 * n) = n := by simp
  have hav : ∀ j < 1, T^[j] (2 * n) ∉ S := by
    intro j hj
    obtain rfl : j = 0 := by omega
    exact hS n hn
  obtain ⟨hiff, hent⟩ := reach_shift hstep hav (by omega) (by omega)
  refine ⟨hiff, fun hA => ?_⟩
  change -(entry S (2 * n) : ℝ) = -(entry S n : ℝ) - 1
  rw [hent (hiff.mpr hA)]
  push_cast
  ring

/-- **Transport for `A_K`** (Theorem 1.3(i)): clock `-τ_K`, reward `(1, 1)`, every threshold
`x ≥ K`. -/
theorem transport_AK (K : ℕ) : Transport (AK K) (fun n => -(tauK K n : ℝ)) 1 1 K :=
  transport_reach (S := {m | m ≤ K}) (fun m hm => by exact_mod_cast hm)

/-- **Doubling compatibility for `A_K`**: `τ_K(2n) = τ_K(n) + 1` for `2n > K`. -/
theorem doubling_AK (K : ℕ) : DoublingCompatible (AK K) (fun n => -(tauK K n : ℝ)) 1 :=
  doubling_reach (S := {m | m ≤ K}) (n0 := K + 1) (by omega) (fun n hn h => by
    change 2 * n ≤ K at h
    omega)

/-- **Transport for a merging class** (Theorem 1.3(iii)): zero clock, reward `(0, 0)`, every
threshold. The backtracked point `U^r(N)` is a raw iterate of `N`, so the two merge. -/
theorem transport_class (n0 : ℕ) (x₀ : ℝ) : Transport (mergeClass n0) (fun _ => 0) 0 0 x₀ := by
  intro x _ _ N hN _ _ _
  obtain ⟨k, hk⟩ := exists_T_iterate_eq_U_iterate hN (passT x N - mT x)
  have hM : 0 < U^[passT x N - mT x] N := (odd_U_iterate hN _).pos
  have hmerge : Merge (U^[passT x N - mT x] N) N := ⟨0, k, hk.symm⟩
  refine ⟨⟨fun ⟨_, h⟩ => ⟨hM, merge_equivalence.trans hmerge h⟩,
    fun ⟨_, h⟩ => ⟨hN.pos, merge_equivalence.trans (merge_equivalence.symm hmerge) h⟩⟩,
    fun _ => by simp⟩

/-- **Doubling compatibility for a merging class**: `2n` and `n` merge, since `T(2n) = n`. -/
theorem doubling_class (n0 : ℕ) : DoublingCompatible (mergeClass n0) (fun _ => 0) 0 := by
  refine ⟨1, fun n hn => ⟨?_, fun _ => by simp⟩⟩
  have hm : Merge (2 * n) n := ⟨1, 0, by simp⟩
  exact ⟨fun ⟨_, h⟩ => ⟨by omega, merge_equivalence.trans (merge_equivalence.symm hm) h⟩,
    fun ⟨_, h⟩ => ⟨by omega, merge_equivalence.trans hm h⟩⟩

/-! ## Rays (§6.7) -/

/-- On the basin of the forward orbit of `a`, the first point reached is `a_{J_R(n)}`. -/
lemma iterate_entry_ray {a n : ℕ} (h : ∃ k, T^[k] n ∈ fwdOrbit a) :
    T^[entry (fwdOrbit a) n] n = T^[rayIndex a n] a := by
  obtain ⟨j, hj⟩ := iterate_entry h
  have hj' : T^[j] a = T^[entry (fwdOrbit a) n] n := hj
  exact Nat.sInf_mem (s := {j | T^[entry (fwdOrbit a) n] n = T^[j] a}) ⟨j, hj'.symm⟩

/-- After entering the forward orbit of `a`, the orbit of `n` follows it. -/
lemma iterate_after_entry {a n : ℕ} (h : ∃ k, T^[k] n ∈ fwdOrbit a) (t : ℕ) :
    T^[entry (fwdOrbit a) n + t] n = T^[rayIndex a n + t] a := by
  rw [add_comm _ t, iterate_add_apply, iterate_entry_ray h, ← iterate_add_apply, add_comm t]

-- `0 < a` is kept to match the paper's setting; the identities hold for every injective orbit.
set_option linter.unusedVariables false in
/-- **The ray identities** (proof of Theorem 6.7 [`thm:rayentry`]). For a nonrepeating ray
`a_j = T^j(a)` with class `C`: `P_T(a_j) = {n ∈ C : J_R(n) ≤ j}`, and on `P_T(a_j)`,
`τ_{T,a_j} = e_R + j - J_R`. -/
theorem ray_identities {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) (j : ℕ) :
    Pred T (T^[j] a) = {n | n ∈ mergeClass a ∧ rayIndex a n ≤ j} ∧
    ∀ n ∈ Pred T (T^[j] a), rayIndex a n ≤ j ∧
      hit T (T^[j] a) n + rayIndex a n = entry (fwdOrbit a) n + j := by
  -- if `T^k(n) = a_j`, then `e_R(n) ≤ k` and `J_R(n) + (k - e_R(n)) = j`
  have key : ∀ n k, T^[k] n = T^[j] a →
      entry (fwdOrbit a) n ≤ k ∧ rayIndex a n + (k - entry (fwdOrbit a) n) = j := by
    intro n k hk
    have hreach : ∃ k, T^[k] n ∈ fwdOrbit a := ⟨k, j, hk.symm⟩
    have he : entry (fwdOrbit a) n ≤ k := entry_le ⟨j, hk.symm⟩
    refine ⟨he, hR ?_⟩
    change T^[rayIndex a n + (k - entry (fwdOrbit a) n)] a = T^[j] a
    rw [← iterate_after_entry hreach, Nat.add_sub_cancel' he, hk]
  have hpred : ∀ n ∈ Pred T (T^[j] a), rayIndex a n ≤ j ∧
      hit T (T^[j] a) n + rayIndex a n = entry (fwdOrbit a) n + j := by
    rintro n ⟨_, k, hk⟩
    obtain ⟨he, hJ⟩ := key n _ (iterate_hit (G := T) ⟨k, hk⟩)
    omega
  refine ⟨?_, hpred⟩
  ext n
  constructor
  · rintro ⟨hn0, k, hk⟩
    exact ⟨⟨hn0, k, j, hk⟩, (hpred n ⟨hn0, k, hk⟩).1⟩
  · rintro ⟨⟨hn0, i, i', hii⟩, hJ⟩
    have hreach : ∃ k, T^[k] n ∈ fwdOrbit a := ⟨i, i', hii.symm⟩
    refine ⟨hn0, entry (fwdOrbit a) n + (j - rayIndex a n), ?_⟩
    rw [iterate_after_entry hreach, Nat.add_sub_cancel' hJ]

/-- `C ∩ A_K ⊆ P_T(a_j)` for every large `j` (proof of Theorem 6.7 [`thm:rayentry`]): the
finitely many members of `C ∩ [1, K]` all reach `a_j` once `j` exceeds their entrance indices. -/
theorem classAK_subset_pred {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) (K : ℕ) :
    ∃ jK : ℕ, ∀ j, jK ≤ j → mergeClass a ∩ AK K ⊆ Pred T (T^[j] a) := by
  classical
  set F := (Finset.Icc 1 K).filter (· ∈ mergeClass a) with hF
  refine ⟨F.sup (rayIndex a), fun j hj n hn => ?_⟩
  obtain ⟨hnC, hn0, k, hk⟩ := hn
  have hm0 : 0 < T^[k] n := iterate_T_pos hn0 k
  have hmC : T^[k] n ∈ mergeClass a :=
    ⟨hm0, merge_equivalence.trans (merge_equivalence.symm (merge_iterate n k)) hnC.2⟩
  have hmF : T^[k] n ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm0, hk⟩, hmC⟩
  have hJ : rayIndex a (T^[k] n) ≤ j := (Finset.le_sup (f := rayIndex a) hmF).trans hj
  have hmP : T^[k] n ∈ Pred T (T^[j] a) := by
    rw [(ray_identities ha hR j).1]
    exact ⟨hmC, hJ⟩
  exact pred_trans ⟨hn0, k, rfl⟩ hmP

lemma not_three_dvd_T {n : ℕ} (h : ¬ 3 ∣ n) : ¬ 3 ∣ T n := by
  unfold T
  split_ifs with he
  · obtain ⟨k, rfl⟩ := he
    omega
  · omega

lemma not_three_dvd_iterate {n : ℕ} (h : ¬ 3 ∣ n) (t : ℕ) : ¬ 3 ∣ T^[t] n := by
  induction t with
  | zero => simpa using h
  | succ t ih => rw [iterate_succ_apply']; exact not_three_dvd_T ih

/-- **Late orbit points are prime to 3**: once an orbit leaves `3ℤ` it never returns. For a ray this
is the paper's "finitely many early `a_j` may be divisible by 3". -/
theorem eventually_not_three_dvd {a : ℕ} (ha : 0 < a) :
    ∃ j0 : ℕ, ∀ j, j0 ≤ j → ¬ 3 ∣ T^[j] a := by
  obtain ⟨k, hk⟩ := exists_iterate_not_three_dvd ha
  refine ⟨k, fun j hj => ?_⟩
  rw [show j = (j - k) + k by omega, iterate_add_apply]
  exact not_three_dvd_iterate hk _

/-! ## Cycles -/

/-- **The basin of a cycle is `P_T(b)`** for any point `b` of the cycle. -/
theorem reach_cycle {b p : ℕ} (hp : 0 < p) (hper : T^[p] b = b) :
    Reach (fwdOrbit b) = Pred T b := by
  ext n
  constructor
  · rintro ⟨hn, k, j, hj⟩
    have hj' : T^[j] b = T^[k] n := hj
    refine ⟨hn, k + (p * j - j), ?_⟩
    rw [add_comm k, iterate_add_apply, ← hj', ← iterate_add_apply,
      Nat.sub_add_cancel (Nat.le_mul_of_pos_left j hp), iterate_period_mul hper]
  · rintro ⟨hn, k, hk⟩
    exact ⟨hn, k, 0, hk.symm⟩

/-- **Entry into a cycle versus hitting a point of it**: on `P_T(b)`, with `T^p(b) = b`,
`entry ≤ τ_{T,b} ≤ entry + (p - 1)`. -/
theorem hit_le_entry_cycle {b p : ℕ} (hp : 0 < p) (hper : T^[p] b = b) {n : ℕ}
    (hn : n ∈ Pred T b) :
    entry (fwdOrbit b) n ≤ hit T b n ∧ hit T b n ≤ entry (fwdOrbit b) n + (p - 1) := by
  obtain ⟨hn0, k, hk⟩ := hn
  have hreach : ∃ k, T^[k] n ∈ fwdOrbit b := ⟨k, 0, hk.symm⟩
  refine ⟨entry_le ⟨0, (iterate_hit ⟨k, hk⟩).symm⟩, ?_⟩
  obtain ⟨J, hJ⟩ := iterate_entry hreach
  have hJ' : T^[J] b = T^[entry (fwdOrbit b) n] n := hJ
  -- reduce the index of the entry point modulo the period
  have hmod : T^[J] b = T^[J % p] b := by
    conv_lhs => rw [← Nat.mod_add_div J p]
    rw [iterate_add_apply, iterate_period_mul hper]
  have hlt : J % p < p := Nat.mod_lt J hp
  rcases Nat.eq_zero_or_pos (J % p) with h0 | hpos
  · have hat : T^[entry (fwdOrbit b) n] n = b := by
      rw [← hJ', hmod, h0]
      rfl
    exact (hit_le hat).trans (by omega)
  · have hat : T^[entry (fwdOrbit b) n + (p - J % p)] n = b := by
      rw [add_comm, iterate_add_apply, ← hJ', hmod, ← iterate_add_apply,
        Nat.sub_add_cancel hlt.le, hper]
    exact (hit_le hat).trans (by omega)

/-- A periodic point lies on the forward orbit of every point it merges with. -/
lemma mem_fwdOrbit_of_periodic_merge {p p' : ℕ} (hper : IsPeriodic p) (h : Merge p p') :
    p ∈ fwdOrbit p' := by
  obtain ⟨q, hq, hpq⟩ := hper
  obtain ⟨i, i', hii⟩ := h
  refine ⟨q * i - i + i', ?_⟩
  change T^[q * i - i + i'] p' = p
  rw [iterate_add_apply, ← hii, ← iterate_add_apply,
    Nat.sub_add_cancel (Nat.le_mul_of_pos_left i hq), iterate_period_mul hpq]

lemma fwdOrbit_subset {p p' : ℕ} (h : p ∈ fwdOrbit p') : fwdOrbit p ⊆ fwdOrbit p' := by
  obtain ⟨j, hj⟩ := h
  have hj' : T^[j] p' = p := hj
  rintro _ ⟨t, rfl⟩
  exact ⟨t + j, by
    change T^[t + j] p' = T^[t] p
    rw [iterate_add_apply, hj']⟩

/-- **A class contains at most one cycle**: two periodic points that merge have the same forward
orbit. -/
theorem fwdOrbit_eq_of_periodic_merge {p p' : ℕ} (hp : IsPeriodic p) (hp' : IsPeriodic p')
    (h : Merge p p') : fwdOrbit p = fwdOrbit p' :=
  (fwdOrbit_subset (mem_fwdOrbit_of_periodic_merge hp h)).antisymm
    (fwdOrbit_subset (mem_fwdOrbit_of_periodic_merge hp' (merge_equivalence.symm h)))

/-- The trivial cycle. -/
theorem fwdOrbit_one : fwdOrbit 1 = {1, 4, 2} := by
  ext m
  constructor
  · rintro ⟨j, rfl⟩
    change T^[j] 1 ∈ ({1, 4, 2} : Set ℕ)
    induction j with
    | zero => exact Or.inl rfl
    | succ j ih =>
      rw [iterate_succ_apply']
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
      rcases ih with h | h | h <;> rw [h] <;> decide
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-! ## The exceptional set (Corollary 1.5) -/

/-- If `n` reaches both `b` and a periodic point `c`, then `b` reaches `c`. -/
lemma pred_of_pred_of_periodic {n b c k : ℕ} (hc : IsPeriodic c) (hk : T^[k] n = b) (hb : 0 < b)
    (hn : n ∈ Pred T c) : b ∈ Pred T c := by
  obtain ⟨q, hq, hqc⟩ := hc
  obtain ⟨-, k', hk'⟩ := hn
  refine ⟨hb, ?_⟩
  by_cases h : k ≤ k'
  · exact ⟨k' - k, by rw [← hk, ← iterate_add_apply, Nat.sub_add_cancel h, hk']⟩
  · -- `b = T^{k-k'}(c)` lies on the cycle of `c`
    have hk2 : T^[k - k'] c = b := by
      rw [← hk', ← iterate_add_apply, Nat.sub_add_cancel (by omega)]
      exact hk
    refine ⟨q * (k - k') - (k - k'), ?_⟩
    rw [← hk2, ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hq),
      iterate_period_mul hqc]

lemma mem_exc_iff {n : ℕ} (hn : 0 < n) : n ∈ Exc ↔ n ∉ Pred T 1 :=
  ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

lemma exc_eq_empty_iff : Exc = ∅ ↔ ∀ n : ℕ, 0 < n → n ∈ Pred T 1 := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h n hn => by_contra fun h1 => h n ⟨hn, h1⟩, fun h n hn => hn.2 (h n hn.1)⟩

/-- **`P_T(b) ⊆ E` for `b ∈ E`** (Corollary 1.5): an orbit that reaches 1 stays on `{1, 4, 2}`. -/
theorem pred_subset_exc {b : ℕ} (hb : b ∈ Exc) : Pred T b ⊆ Exc := by
  rintro n ⟨hn, k, hk⟩
  exact ⟨hn, fun h1 => hb.2 (pred_of_pred_of_periodic isPeriodic_one hk hb.1 h1)⟩

lemma iterate_mem_exc {n : ℕ} (hn : n ∈ Exc) (k : ℕ) : T^[k] n ∈ Exc :=
  ⟨iterate_T_pos hn.1 k, fun ⟨_, j, hj⟩ => hn.2 ⟨hn.1, j + k, by rw [iterate_add_apply, hj]⟩⟩

/-- **Every counterexample lies in the basin of a counterexample prime to 3** (Corollary 1.5): a
point of its orbit not divisible by 3. -/
theorem exists_three_free_basin {n : ℕ} (hn : n ∈ Exc) :
    ∃ b ∈ Exc, ¬ 3 ∣ b ∧ n ∈ Pred T b := by
  obtain ⟨k, hk⟩ := exists_iterate_not_three_dvd hn.1
  exact ⟨T^[k] n, iterate_mem_exc hn k, hk, hn.1, k, rfl⟩

/-! ## Reference orbits (Corollary 1.6) -/

open Classical in
/-- A representative point of each merging class: a positive periodic one when the class has one,
otherwise any positive member (and `0` for the class of `0`). -/
noncomputable def classRep (C : Quotient mergeSetoid) : ℕ :=
  if h : ∃ p, 0 < p ∧ Quotient.mk mergeSetoid p = C ∧ IsPeriodic p then Classical.choose h
  else if h' : ∃ p, 0 < p ∧ Quotient.mk mergeSetoid p = C then Classical.choose h' else 0

/-- **An admissible choice of reference orbits exists**, so `RefChoice` in Corollary 1.6 is not
vacuous. -/
theorem refChoice_exists : ∃ ref : ℕ → ℕ, RefChoice ref := by
  refine ⟨fun n => classRep (Quotient.mk mergeSetoid n), ?_, ?_, ?_⟩
  · intro n hn
    change 0 < classRep _ ∧ Merge (classRep _) n
    unfold classRep
    split_ifs with h h'
    · obtain ⟨h1, h2, -⟩ := Classical.choose_spec h
      exact ⟨h1, Quotient.exact h2⟩
    · obtain ⟨h1, h2⟩ := Classical.choose_spec h'
      exact ⟨h1, Quotient.exact h2⟩
    · exact absurd ⟨n, hn, rfl⟩ h'
  · intro m n _ _ hmn
    change classRep _ = classRep _
    rw [Quotient.sound (s := mergeSetoid) hmn]
  · rintro n _ ⟨p, hp, hpn, hper⟩
    change IsPeriodic (classRep _)
    have h : ∃ p, 0 < p ∧ Quotient.mk mergeSetoid p = Quotient.mk mergeSetoid n ∧ IsPeriodic p :=
      ⟨p, hp, Quotient.sound hpn, hper⟩
    unfold classRep
    split_ifs
    exact (Classical.choose_spec h).2.2

/-- **`ε` is finite** (Corollary 1.6): the reference orbit lies in the class of `n`. -/
theorem eps_finite {ref : ℕ → ℕ} (href : RefChoice ref) :
    ∀ n : ℕ, 0 < n → ∃ k, T^[k] n ∈ fwdOrbit (ref n) := by
  intro n hn
  obtain ⟨i, j, hij⟩ := (href.1 n hn).2
  exact ⟨j, i, hij⟩

/-- If the forward orbits of `a` and `a'` share the point `T^i(a) = T^{i'}(a')`, entering the
orbit of `a` takes at most `i'` steps longer than entering that of `a'`. -/
lemma entry_le_entry_add {a a' i i' n : ℕ} (hii : T^[i] a = T^[i'] a')
    (hn : ∃ k, T^[k] n ∈ fwdOrbit a') :
    entry (fwdOrbit a) n ≤ entry (fwdOrbit a') n + i' := by
  obtain ⟨J, hJ⟩ := iterate_entry hn
  have hJ' : T^[J] a' = T^[entry (fwdOrbit a') n] n := hJ
  apply entry_le
  refine ⟨J + i, ?_⟩
  change T^[J + i] a = T^[entry (fwdOrbit a') n + i'] n
  rw [iterate_add_apply, hii, ← iterate_add_apply, add_comm J i', iterate_add_apply, hJ',
    ← iterate_add_apply, add_comm]

-- `0 < a`, `0 < a'` are kept as audited; the bound holds for any two merging points.
set_option linter.unusedVariables false in
/-- **Change of reference orbit** (Corollary 1.6): replacing a forward orbit of a class by another
changes the entry time by a bounded amount on the whole class. Stated for every class; the paper
states it for divergent classes. -/
theorem ref_change {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (h : Merge a a') :
    ∃ B : ℕ, ∀ n : ℕ, 0 < n → Merge n a →
      entry (fwdOrbit a) n ≤ entry (fwdOrbit a') n + B ∧
      entry (fwdOrbit a') n ≤ entry (fwdOrbit a) n + B := by
  obtain ⟨i, i', hii⟩ := h
  refine ⟨max i i', fun n _ hna => ?_⟩
  have hreach : ∀ {b : ℕ}, Merge n b → ∃ k, T^[k] n ∈ fwdOrbit b :=
    fun ⟨k, j, hkj⟩ => ⟨k, j, hkj.symm⟩
  have hna' : Merge n a' := merge_equivalence.trans hna ⟨i, i', hii⟩
  exact ⟨(entry_le_entry_add hii (hreach hna')).trans (Nat.add_le_add_left (le_max_right i i') _),
    (entry_le_entry_add hii.symm (hreach hna)).trans (Nat.add_le_add_left (le_max_left i i') _)⟩

/-- **The reference orbit of the class of 1 is `{1, 4, 2}`**: `RefChoice` forces it to be periodic,
and the class of 1 contains only one cycle. -/
theorem fwdOrbit_ref_of_merge_one {ref : ℕ → ℕ} (href : RefChoice ref) {n : ℕ} (hn : 0 < n)
    (h1 : Merge n 1) : fwdOrbit (ref n) = fwdOrbit 1 := by
  obtain ⟨-, hmerge⟩ := href.1 n hn
  have hper : IsPeriodic (ref n) :=
    href.2.2 n hn ⟨1, one_pos, merge_equivalence.symm h1, isPeriodic_one⟩
  exact fwdOrbit_eq_of_periodic_merge hper isPeriodic_one (merge_equivalence.trans hmerge h1)

/-- **On `P_T(1)`, `0 ≤ τ_{T,1} - ε ≤ 2`** (the last sentence of Corollary 1.6). -/
theorem eps_class_one {ref : ℕ → ℕ} (href : RefChoice ref) :
    ∀ n ∈ Pred T 1, eps ref n ≤ hit T 1 n ∧ hit T 1 n ≤ eps ref n + 2 := by
  intro n hn
  have h1 : Merge n 1 := (pred_subset_mergeClass 1 hn).2
  unfold eps
  rw [fwdOrbit_ref_of_merge_one href hn.1 h1]
  exact hit_le_entry_cycle (p := 3) (by norm_num) (by decide) hn

end CollatzCLT
