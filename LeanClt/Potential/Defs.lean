import LeanClt.Exceptional.Orbits

/-!
# Theorem 1.4 [`thm:potential`] and §7: definitions and orbit lemmas

The six definitions of the checkpoint-17 plan, copied from the audited buffer, and the unconditional
facts about the entrance label `H_K` that the later stages use.

* **Definitions.** `natDens A` and `nuK K E` are `limUnder`s (junk values where no limit exists);
  `natDens_eq` and `nuK_eq` pin them down wherever the limit exists. `hpot n = natDens (P_T(n))` is
  the potential `h(n)`. `entK K N` is `H_K(N)`, the first odd value `≤ K` on the raw `T`-orbit of
  `N`, or `none` (the cemetery `†`). `lawHK K Y E = P(H_K(N_Y) ∈ E)` for `N_Y` uniform on the odd
  integers of `[Y, 2Y]`, `nuK K E` its limit as `Y → ∞`, and `fK` is the finite-orbit potential
  `f_K` of Proposition 7.5 [`prop:approx`].
* **The label `H_K`.** Characterisations of `entK K N = some m` and `= none` (`entK_eq_some_iff`,
  `entK_eq_none_iff`); labels are odd and `≤ K` (`entK_label`); `H_K` is unchanged along a segment
  with no odd value `≤ K` (`entK_shift`), in particular `H_K(2n) = H_K(n)` (`entK_two_mul`); for odd
  `N` it is the first value `≤ K` of the `U`-orbit (`entK_of_odd`); and `{H_K ≠ †} = A_K` on the
  positive integers (`entK_ne_none_iff`).
* **Transport and doubling** (§7.2): for every set of labels `E`, the set `{N : H_K(N) ∈ E}` with the
  zero clock has the transport property at every threshold `x ≥ K` (`transport_entK`): the early
  segment stays above `x ≥ K`, so it has no odd value `≤ K`. It is doubling compatible
  (`doubling_entK`).

Everything here is unconditional.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## New definitions -/

/-- The natural density of `A` when it exists (`limUnder` of `#(A ∩ [1, X]) / X`; a junk value
otherwise). Every use below is paired with a `HasDensity` statement that pins it down. -/
def natDens (A : Set ℕ) : ℝ :=
  limUnder atTop (fun X : ℕ => ((window A X).card : ℝ) / X)

/-- **The predecessor-density potential** `h(n) = dens P_T(n)` (Theorem 1.4 [`thm:potential`]). -/
def hpot (n : ℕ) : ℝ := natDens (Pred T n)

open Classical in
/-- `H_K(N)` (§7.2): the first odd value `≤ K` on the raw `T`-orbit of `N`, or `none` (the
cemetery `†`) if the orbit has no odd value `≤ K`. -/
def entK (K N : ℕ) : Option ℕ :=
  if h : ∃ i, Odd (T^[i] N) ∧ T^[i] N ≤ K then some (T^[Nat.find h] N) else none

open Classical in
/-- `P(H_K(N_Y) ∈ E)` for `N_Y` uniform on the odd integers of `[Y, 2Y]` (`oddClosed Y`). -/
def lawHK (K : ℕ) (Y : ℝ) (E : Set (Option ℕ)) : ℝ :=
  (((oddClosed Y).filter (fun N => entK K N ∈ E)).card : ℝ) / (oddClosed Y).card

/-- `ν_K(E) = lim_{Y → ∞} P(H_K(N_Y) ∈ E)` (§7.2), over real `Y`. -/
def nuK (K : ℕ) (E : Set (Option ℕ)) : ℝ := limUnder atTop (fun Y : ℝ => lawHK K Y E)

open Classical in
/-- `f_K(n) = ∑_{k odd, k ≤ K} ν_K({k}) 1{k reaches n}` (Proposition 7.5 [`prop:approx`]). -/
def fK (K n : ℕ) : ℝ :=
  ∑ k ∈ (range (K + 1)).filter Odd, nuK K {some k} * (fwdOrbit k).indicator (fun _ => (1 : ℝ)) n

/-! ## API for the junk-valued definitions (unconditional) -/

lemma natDens_eq {A : Set ℕ} {a : ℝ} (h : HasDensity A a) : natDens A = a := h.limUnder_eq

lemma nuK_eq {K : ℕ} {E : Set (Option ℕ)} {x : ℝ}
    (h : Tendsto (fun Y : ℝ => lawHK K Y E) atTop (𝓝 x)) : nuK K E = x := h.limUnder_eq

/-! ## The label `H_K` -/

/-- `H_K(N) = m` iff `m` is odd, `m ≤ K`, and `m` is the first odd value `≤ K` of the raw orbit. -/
lemma entK_eq_some_iff {K N m : ℕ} :
    entK K N = some m ↔
      ∃ i, T^[i] N = m ∧ Odd m ∧ m ≤ K ∧ ∀ j < i, ¬ (Odd (T^[j] N) ∧ T^[j] N ≤ K) := by
  classical
  unfold entK
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨Nat.find h, rfl, (Nat.find_spec h).1, (Nat.find_spec h).2,
        fun j hj => Nat.find_min h hj⟩
    · rintro ⟨i, rfl, hodd, hle, hmin⟩
      have h1 : Nat.find h ≤ i := Nat.find_min' h ⟨hodd, hle⟩
      have h2 : ¬ Nat.find h < i := fun hlt => hmin _ hlt (Nat.find_spec h)
      rw [show Nat.find h = i by omega]
  · simp only [false_iff, not_exists, not_and]
    intro i hi hodd hle _
    exact h ⟨i, hi ▸ ⟨hodd, hle⟩⟩

/-- `H_K(N) = †` iff the raw orbit of `N` has no odd value `≤ K`. -/
lemma entK_eq_none_iff {K N : ℕ} :
    entK K N = none ↔ ∀ i, ¬ (Odd (T^[i] N) ∧ T^[i] N ≤ K) := by
  classical
  unfold entK
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    exact h
  · simp only [true_iff]
    exact fun i hi => h ⟨i, hi⟩

/-- Labels are odd and `≤ K`. -/
lemma entK_label {K N m : ℕ} (h : entK K N = some m) : Odd m ∧ m ≤ K := by
  obtain ⟨_, _, hodd, hle, _⟩ := entK_eq_some_iff.mp h
  exact ⟨hodd, hle⟩

/-- **Shifting along a segment with no odd value `≤ K`**: if the first `k` states of the orbit of
`N` contain no odd value `≤ K` and `T^k(N) = M`, then `H_K(N) = H_K(M)`. -/
lemma entK_shift {K N M k : ℕ} (hk : T^[k] N = M)
    (hav : ∀ j < k, ¬ (Odd (T^[j] N) ∧ T^[j] N ≤ K)) : entK K N = entK K M := by
  have hshift : ∀ i, T^[i + k] N = T^[i] M := fun i => by
    rw [Function.iterate_add_apply, hk]
  rcases hM : entK K M with _ | m
  · rw [entK_eq_none_iff] at hM ⊢
    intro i hi
    by_cases hik : i < k
    · exact hav i hik hi
    · have := hM (i - k)
      rw [← hshift, show i - k + k = i by omega] at this
      exact this hi
  · obtain ⟨i, hi, hodd, hle, hmin⟩ := entK_eq_some_iff.mp hM
    refine entK_eq_some_iff.mpr ⟨i + k, by rw [hshift, hi], hodd, hle, fun j hj => ?_⟩
    by_cases hjk : j < k
    · exact hav j hjk
    · have := hmin (j - k) (by omega)
      rwa [← hshift, show j - k + k = j by omega] at this

/-- `H_K(2n) = H_K(n)`: the first step halves, and `2n` is even. -/
lemma entK_two_mul (K n : ℕ) : entK K (2 * n) = entK K n := by
  refine entK_shift (k := 1) (by simp) (fun j hj => ?_)
  obtain rfl : j = 0 := by omega
  rintro ⟨hodd, -⟩
  exact (Nat.not_odd_iff_even.mpr (even_two_mul n)) (by simpa using hodd)

open Classical in
/-- §7.2: for odd `N`, `H_K(N)` is the first value `≤ K` of the `U`-orbit. -/
lemma entK_of_odd (K : ℕ) {N : ℕ} (hN : Odd N) :
    entK K N = if h : ∃ r, U^[r] N ≤ K then some (U^[Nat.find h] N) else none := by
  split_ifs with h
  · set r0 := Nat.find h with hr0
    refine entK_eq_some_iff.mpr ⟨wsum (vword N) r0 + r0, (T_blocks hN r0).1,
      odd_U_iterate hN r0, Nat.find_spec h, fun j hj => ?_⟩
    rintro ⟨hodd, hle⟩
    -- `r0 ≥ 1`, and the time `j` lies before or inside the last block
    obtain ⟨r, hr⟩ : ∃ r, r0 = r + 1 := by
      rcases Nat.eq_zero_or_pos r0 with h0 | h0
      · rw [h0] at hj; simp [wsum] at hj
      · exact ⟨r0 - 1, by omega⟩
    have hws : wsum (vword N) r0 = wsum (vword N) r + vword N r := by
      rw [hr]; unfold wsum; rw [Finset.sum_range_succ]
    set base := wsum (vword N) r + r with hbase
    obtain ⟨hTb, hTst⟩ := T_blocks hN r
    by_cases hjb : j ≤ base
    · -- an earlier `U`-state is at most `T^j(N) ≤ K`, against the minimality of `r0`
      obtain ⟨i, hi, hle'⟩ := hTst j hjb
      have := Nat.find_min' h (hle'.trans hle)
      omega
    · -- inside the halving run of `U^r(N)`, every state is even
      have hu : Odd (U^[r] N) := odd_U_iterate hN r
      have ht1 : 1 ≤ j - base := by omega
      have ht2 : j - base ≤ padicValNat 2 (3 * U^[r] N + 1) := by
        have : j < base + vword N r + 1 := by rw [hws] at hj; omega
        unfold vword at this; omega
      have heven := T_iterate_even_of_lt hu ht1 ht2
      rw [← hTb, ← Function.iterate_add_apply, show j - base + base = j by omega] at heven
      exact (Nat.not_odd_iff_even.mpr heven) hodd
  · refine entK_eq_none_iff.mpr fun i ⟨hodd, hle⟩ => h ?_
    obtain ⟨k, hk⟩ := exists_U_iterate_eq_T_iterate i N hN hodd
    exact ⟨k, hk ▸ hle⟩

/-- Every positive integer reaches an odd value at most itself, by halving. -/
lemma exists_iterate_odd_le {m : ℕ} (hm : 0 < m) : ∃ e, Odd (T^[e] m) ∧ T^[e] m ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hodd : Odd m
    · exact ⟨0, hodd, le_rfl⟩
    · have hev : Even m := Nat.not_odd_iff_even.mp hodd
      have hT : T m = m / 2 := T_of_even hev
      obtain ⟨e, he1, he2⟩ := ih (m / 2) (by omega) (by obtain ⟨k, hk⟩ := hev; omega)
      refine ⟨e + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hT]; exact he1
      · rw [Function.iterate_succ_apply, hT]; omega

/-- §7.2: `{H_K ≠ †} = A_K` on the positive integers. -/
lemma entK_ne_none_iff (K : ℕ) {N : ℕ} (hN : 0 < N) : entK K N ≠ none ↔ N ∈ AK K := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨i, hi, -, hle, -⟩ := entK_eq_some_iff.mp hm
    exact ⟨hN, i, hi ▸ hle⟩
  · rintro ⟨-, k, hk⟩ hnone
    obtain ⟨e, he1, he2⟩ := exists_iterate_odd_le (iterate_T_pos hN k)
    refine entK_eq_none_iff.mp hnone (e + k) ⟨?_, ?_⟩
    · rw [Function.iterate_add_apply]; exact he1
    · rw [Function.iterate_add_apply]; omega

/-! ## Transport and doubling for the events `{H_K ∈ E}` (§7.2) -/

/-- **Transport for `{H_K ∈ E}`**, zero clock, reward `(0, 0)`, every threshold `x ≥ K`: every odd
state of the early segment exceeds `x ≥ K`, so `H_K(N) = H_K(M)`. -/
theorem transport_entK (K : ℕ) (E : Set (Option ℕ)) :
    Transport {N | entK K N ∈ E} (fun _ => 0) 0 0 K := by
  intro x hx hm1 N hN _ hmT _
  set r := passT x N - mT x
  obtain ⟨hTb, hTst⟩ := T_blocks hN r
  have hab := early_above hm1 hmT
  have hav : ∀ j < wsum (vword N) r + r, ¬ (Odd (T^[j] N) ∧ T^[j] N ≤ K) := by
    rintro j hj ⟨-, hle⟩
    obtain ⟨i, hi, hle'⟩ := hTst j hj.le
    have h1 := hab i hi
    have h2 : (U^[i] N : ℝ) ≤ K := by exact_mod_cast hle'.trans hle
    linarith
  have hsh := entK_shift hTb hav
  refine ⟨?_, fun _ => by simp⟩
  simp only [Set.mem_ofPred_eq, hsh]

/-- **Doubling compatibility for `{H_K ∈ E}`**: `H_K(2n) = H_K(n)`. -/
theorem doubling_entK (K : ℕ) (E : Set (Option ℕ)) :
    DoublingCompatible {N | entK K N ∈ E} (fun _ => 0) 0 :=
  ⟨0, fun n _ => ⟨by simp only [Set.mem_ofPred_eq, entK_two_mul], fun _ => by simp⟩⟩

end CollatzCLT
