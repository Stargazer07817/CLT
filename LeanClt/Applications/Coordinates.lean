import LeanClt.Exceptional.Orbits
import LeanClt.Positivity.Seed

/-!
# §6.7: the spatial coordinates of a divergent class (stage 3 of the checkpoint-20 plan)

Unconditional. A divergent class is the merging class `mergeClass a` of a nonrepeating `T`-ray
`a_j = T^j(a)`. Its raw coordinate `ℓ_T(n) = j - i` when `T^i(n) = a_j` is `coordT a`, built on the
entrance index and entry time of `Exceptional/Defs.lean`; its shortcut coordinate `ℓ_C(n) = j - i`
when `F^i(n) = F^j(a)` is `coordF a`, built on the `F`-ray objects `fwdOrbitF`, `entryF` and
`rayIndexF`, copies of the `T`-definitions with `F`.

* **The two rays.** The shortcut ray through `a` is injective exactly when the raw ray is
  (`nonRepeatingF_iff`): the `F`-orbit is a subsequence of the `T`-orbit, and an eventually periodic
  `T`-orbit is finite. Every point of the class also `F`-merges with `a` (`mergeF_of_merge`), since
  odd states of a `T`-orbit are `F`-states and every positive orbit has odd states.
* **The coordinates along a meeting.** If `T^k(n) = a_j` then `ℓ_T(n) = j - k` (`coordT_eq`), and the
  same for `F` (`coordF_eq`). Hence each coordinate increases by exactly one per step of its map
  everywhere on the class (`coordT_T`, `coordF_F`, and the iterates `coordT_iterate`,
  `coordF_iterate`), and decreases by one under doubling (`coordT_two_pow_mul`, `coordF_two_pow_mul`).
* **Transport (6.2, `eq:transport`).** Since the early segment `N → U^r(N)` consists of `S + r`
  raw steps and `S` shortcut steps, the two coordinates have the transport property on the class with
  rewards `(1, 1)` and `(1, 0)`, at every threshold (`transport_coordT`, `transport_coordF`). No
  early-segment argument is needed: the coordinates move by one per step on the whole class.
* **A finite union of classes** (for Theorem 6.10(iii) [`thm:anticonc`]). For pairwise non-merging
  base points and one level per class, the class-dependent clock `ℓ_{C(n)}(n) - j_{C(n)}`
  (`classClock`) has the transport property on the union (`transport_classClock`) and the doubling
  property (`classClock_two_pow_mul`).
-/

open Function

noncomputable section

namespace CollatzCLT

/-! ## Definitions -/

/-- The raw spatial coordinate `ℓ_T(n) = j - i` when `T^i(n) = a_j` (§6.7), for `n` in the class of
the nonrepeating `T`-ray `a_j = T^j(a)`: the entrance index minus the entry time (a junk value off
the class). -/
def coordT (a n : ℕ) : ℤ := (rayIndex a n : ℤ) - (entry (fwdOrbit a) n : ℤ)

/-- The forward `F`-orbit `{F^j(a) : j ≥ 0}` (the shortcut ray through `a`). -/
def fwdOrbitF (a : ℕ) : Set ℕ := Set.range (fun j => F^[j] a)

/-- First entry time of the `F`-orbit of `n` into `S` (`sInf ∅ = 0` off the basin). -/
def entryF (S : Set ℕ) (n : ℕ) : ℕ := sInf {k | F^[k] n ∈ S}

/-- The shortcut entrance index: the index `j` of the first point `F^j(a)` reached. -/
def rayIndexF (a n : ℕ) : ℕ := sInf {j | F^[entryF (fwdOrbitF a) n] n = F^[j] a}

/-- The shortcut spatial coordinate `ℓ_C(n) = j - i` when `F^i(n) = a_j`, `a_j = F^j(a)` (§6.7). -/
def coordF (a n : ℕ) : ℤ := (rayIndexF a n : ℤ) - (entryF (fwdOrbitF a) n : ℤ)

/-! ## Raw and shortcut orbits -/

/-- Every raw state of the orbit of `n` is a shortcut state, or the image under `T` of an odd
shortcut state (the skipped even state `3x + 1`). -/
lemma exists_F_iterate_or_odd (n : ℕ) :
    ∀ k, ∃ j, F^[j] n = T^[k] n ∨ (¬ Even (F^[j] n) ∧ T^[k] n = T (F^[j] n)) := by
  intro k
  induction k with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ k ih =>
    obtain ⟨j, hj | ⟨hodd, hj⟩⟩ := ih
    · by_cases he : Even (T^[k] n)
      · refine ⟨j + 1, Or.inl ?_⟩
        rw [iterate_succ_apply', iterate_succ_apply', hj, F_eq_T_of_even he]
      · refine ⟨j, Or.inr ⟨by rw [hj]; exact he, ?_⟩⟩
        rw [iterate_succ_apply', hj]
    · refine ⟨j + 1, Or.inl ?_⟩
      rw [iterate_succ_apply', iterate_succ_apply', hj, F_eq_T_T_of_odd hodd]

/-- An odd raw state is a shortcut state. -/
lemma exists_F_iterate_of_odd {n k : ℕ} (h : ¬ Even (T^[k] n)) : ∃ j, F^[j] n = T^[k] n := by
  obtain ⟨j, hj | ⟨hodd, hj⟩⟩ := exists_F_iterate_or_odd n k
  · exact ⟨j, hj⟩
  · exfalso
    apply h
    rw [hj, T_of_odd hodd]
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hodd
    exact ⟨3 * m + 2, by rw [hm]; ring⟩

/-- Every positive orbit has an odd state. -/
lemma exists_iterate_odd {y : ℕ} (hy : 0 < y) : ∃ m, ¬ Even (T^[m] y) := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    by_cases he : Even y
    · obtain ⟨r, hr⟩ := he
      obtain ⟨m, hm⟩ := ih (y / 2) (by omega) (by omega)
      refine ⟨m + 1, ?_⟩
      rw [iterate_succ_apply, T_of_even ⟨r, hr⟩]
      exact hm
    · exact ⟨0, he⟩

/-- A shortcut state after `p` steps is a raw state after at least `p` steps. -/
lemma exists_T_iterate_eq_F_iterate_ge (n : ℕ) : ∀ p, ∃ m, p ≤ m ∧ T^[m] n = F^[p] n := by
  intro p
  induction p with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ p ih =>
    obtain ⟨m, hm, hk⟩ := ih
    by_cases he : Even (F^[p] n)
    · refine ⟨m + 1, by omega, ?_⟩
      rw [iterate_succ_apply', iterate_succ_apply', hk, F_eq_T_of_even he]
    · refine ⟨m + 2, by omega, ?_⟩
      rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', hk,
        F_eq_T_T_of_odd he]

/-- A raw orbit with a repetition `T^i(a) = T^j(a)`, `i < j`, takes only the values
`T^{m'}(a)`, `m' < j`. -/
lemma iterate_eq_of_lt_period {a i j : ℕ} (hlt : i < j) (h : T^[i] a = T^[j] a) :
    ∀ m, ∃ m' < j, T^[m] a = T^[m'] a := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < j
    · exact ⟨m, hm, rfl⟩
    · obtain ⟨m', hm', he⟩ := ih (m - j + i) (by omega)
      refine ⟨m', hm', ?_⟩
      rw [← he]
      calc T^[m] a = T^[m - j] (T^[j] a) := by
            rw [← iterate_add_apply, Nat.sub_add_cancel (by omega)]
        _ = T^[m - j] (T^[i] a) := by rw [h]
        _ = T^[m - j + i] a := by rw [iterate_add_apply]

lemma F_iterate_two_pow_mul (k a : ℕ) : F^[k] (2 ^ k * a) = a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply, show 2 ^ (k + 1) * a = 2 * (2 ^ k * a) by ring, F_two_mul, ih]

/-! ## The two rays -/

/-- A `T`-ray is nonrepeating iff the shortcut ray through the same point is. -/
lemma nonRepeatingF_iff (a : ℕ) :
    Function.Injective (fun j => F^[j] a) ↔ NonRepeating a := by
  constructor
  · intro hF
    -- a repeating raw orbit is finite, and the shortcut orbit lies inside it
    by_contra hT
    have hrep : ∃ i j, i < j ∧ T^[i] a = T^[j] a := by
      unfold NonRepeating Function.Injective at hT
      push Not at hT
      obtain ⟨i, j, hij, hne⟩ := hT
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact ⟨i, j, h, hij⟩
      · exact ⟨j, i, h, hij.symm⟩
    obtain ⟨i, j, hlt, hij⟩ := hrep
    have hsub : Set.range (fun k => F^[k] a) ⊆
        ((Finset.range j).image (fun m => T^[m] a) : Set ℕ) := by
      rintro _ ⟨k, rfl⟩
      obtain ⟨m, hm⟩ := exists_T_iterate_eq_F_iterate a k
      obtain ⟨m', hm', he⟩ := iterate_eq_of_lt_period hlt hij m
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨m', hm', by rw [← he, hm]⟩
    exact Set.infinite_range_of_injective hF ((Finset.finite_toSet _).subset hsub)
  · intro hR
    -- a repeating shortcut orbit gives a raw return `T^m(b) = b` with `m ≥ 1`
    have key : ∀ i j, i < j → F^[i] a ≠ F^[j] a := by
      intro i j hlt hij
      have hret : F^[j - i] (F^[i] a) = F^[i] a := by
        rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le, hij]
      obtain ⟨m, hm, hTm⟩ := exists_T_iterate_eq_F_iterate_ge (F^[i] a) (j - i)
      obtain ⟨k, hk⟩ := exists_T_iterate_eq_F_iterate a i
      have h1 : T^[m + k] a = T^[k] a := by
        rw [iterate_add_apply, hk, hTm, hret]
      have h2 : m + k = k := hR h1
      omega
    intro i j hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h hij
    · exact key j i h hij.symm

/-- Every point of a class merges with the base point under `F` as well. -/
lemma mergeF_of_merge {a n : ℕ} (hn : n ∈ mergeClass a) :
    ∃ i j, F^[i] n = F^[j] a := by
  obtain ⟨hn0, i, j, hij⟩ := hn
  obtain ⟨m, hm⟩ := exists_iterate_odd (iterate_T_pos hn0 i)
  have h1 : T^[m + i] n = T^[m + j] a := by rw [iterate_add_apply, iterate_add_apply, hij]
  obtain ⟨p, hp⟩ := exists_F_iterate_of_odd (n := n) (k := m + i) (by rwa [iterate_add_apply])
  obtain ⟨q, hq⟩ := exists_F_iterate_of_odd (n := a) (k := m + j)
    (by rwa [← h1, iterate_add_apply])
  exact ⟨p, q, by rw [hp, hq, h1]⟩

/-! ## Entry times along the shortcut orbit -/

lemma iterate_entryF {S : Set ℕ} {n : ℕ} (h : ∃ k, F^[k] n ∈ S) : F^[entryF S n] n ∈ S :=
  Nat.sInf_mem h

lemma entryF_le {S : Set ℕ} {n k : ℕ} (h : F^[k] n ∈ S) : entryF S n ≤ k :=
  Nat.sInf_le h

/-- On the basin of the shortcut ray, the first point reached is `F^{J}(a)`, `J = rayIndexF a n`. -/
lemma iterate_entry_rayF {a n : ℕ} (h : ∃ k, F^[k] n ∈ fwdOrbitF a) :
    F^[entryF (fwdOrbitF a) n] n = F^[rayIndexF a n] a := by
  obtain ⟨j, hj⟩ := iterate_entryF h
  have hj' : F^[j] a = F^[entryF (fwdOrbitF a) n] n := hj
  exact Nat.sInf_mem (s := {j | F^[entryF (fwdOrbitF a) n] n = F^[j] a}) ⟨j, hj'.symm⟩

lemma iterate_after_entryF {a n : ℕ} (h : ∃ k, F^[k] n ∈ fwdOrbitF a) (t : ℕ) :
    F^[entryF (fwdOrbitF a) n + t] n = F^[rayIndexF a n + t] a := by
  rw [add_comm _ t, iterate_add_apply, iterate_entry_rayF h, ← iterate_add_apply, add_comm t]

/-! ## The coordinates along a meeting -/

/-- **The raw coordinate at a meeting**: if `T^k(n) = a_j` on a nonrepeating ray, then
`ℓ_T(n) = j - k`. -/
lemma coordT_eq {a n k j : ℕ} (hR : NonRepeating a) (h : T^[k] n = T^[j] a) :
    coordT a n = (j : ℤ) - k := by
  have hreach : ∃ k, T^[k] n ∈ fwdOrbit a := ⟨k, j, h.symm⟩
  have he : entry (fwdOrbit a) n ≤ k := entry_le ⟨j, h.symm⟩
  have hJ : rayIndex a n + (k - entry (fwdOrbit a) n) = j := hR (by
    change T^[rayIndex a n + (k - entry (fwdOrbit a) n)] a = T^[j] a
    rw [← iterate_after_entry hreach, Nat.add_sub_cancel' he, h])
  unfold coordT
  omega

/-- **The shortcut coordinate at a meeting**: if `F^k(n) = F^j(a)` on an injective shortcut ray,
then `ℓ_C(n) = j - k`. -/
lemma coordF_eq {a n k j : ℕ} (hF : Function.Injective (fun j => F^[j] a))
    (h : F^[k] n = F^[j] a) : coordF a n = (j : ℤ) - k := by
  have hreach : ∃ k, F^[k] n ∈ fwdOrbitF a := ⟨k, j, h.symm⟩
  have he : entryF (fwdOrbitF a) n ≤ k := entryF_le ⟨j, h.symm⟩
  have hJ : rayIndexF a n + (k - entryF (fwdOrbitF a) n) = j := hF (by
    change F^[rayIndexF a n + (k - entryF (fwdOrbitF a) n)] a = F^[j] a
    rw [← iterate_after_entryF hreach, Nat.add_sub_cancel' he, h])
  unfold coordF
  omega

/-- `ℓ_T(T^t n) = ℓ_T(n) + t` on the class. -/
lemma coordT_iterate {a n : ℕ} (hR : NonRepeating a) (hn : n ∈ mergeClass a) (t : ℕ) :
    coordT a (T^[t] n) = coordT a n + t := by
  obtain ⟨-, i, j, hij⟩ := hn
  have h1 : T^[i] (T^[t] n) = T^[t + j] a := by
    rw [← iterate_add_apply, add_comm i t, iterate_add_apply, hij, ← iterate_add_apply]
  rw [coordT_eq hR h1, coordT_eq hR hij]
  push_cast
  ring

set_option linter.unusedVariables false in
/-- The coordinates increase by one along a step of their map, on the class. -/
lemma coordT_T {a n : ℕ} (ha : 0 < a) (hR : NonRepeating a) (hn : n ∈ mergeClass a) :
    coordT a (T n) = coordT a n + 1 := by
  simpa using coordT_iterate hR hn 1

set_option linter.unusedVariables false in
/-- Iterated: `ℓ_C(F^t n) = ℓ_C(n) + t` on the class (the level-set inclusion of the proof of
Corollary 6.11). -/
lemma coordF_iterate {a n : ℕ} (ha : 0 < a) (hR : NonRepeating a) (hn : n ∈ mergeClass a)
    (t : ℕ) : coordF a (F^[t] n) = coordF a n + t := by
  have hF := (nonRepeatingF_iff a).mpr hR
  obtain ⟨i, j, hij⟩ := mergeF_of_merge hn
  have h1 : F^[i] (F^[t] n) = F^[t + j] a := by
    rw [← iterate_add_apply, add_comm i t, iterate_add_apply, hij, ← iterate_add_apply]
  rw [coordF_eq hF h1, coordF_eq hF hij]
  push_cast
  ring

lemma coordF_F {a n : ℕ} (ha : 0 < a) (hR : NonRepeating a) (hn : n ∈ mergeClass a) :
    coordF a (F n) = coordF a n + 1 := by
  simpa using coordF_iterate ha hR hn 1

/-! ## Doubling -/

/-- `2^e u` and `u` lie in the same class (`u > 0`). -/
lemma two_pow_mul_mem_mergeClass {a u : ℕ} (hu : 0 < u) (e : ℕ) :
    2 ^ e * u ∈ mergeClass a ↔ u ∈ mergeClass a := by
  have hm : Merge (2 ^ e * u) u := ⟨e, 0, by rw [Positivity.T_iterate_two_pow_mul]; rfl⟩
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hu, merge_equivalence.trans (merge_equivalence.symm hm) h⟩
  · rintro ⟨_, h⟩
    exact ⟨by positivity, merge_equivalence.trans hm h⟩

/-- `ℓ_T(2^e u) = ℓ_T(u) - e` on the class. -/
lemma coordT_two_pow_mul {a u : ℕ} (hR : NonRepeating a) (hu : u ∈ mergeClass a) (e : ℕ) :
    coordT a (2 ^ e * u) = coordT a u - e := by
  have h := coordT_iterate hR ((two_pow_mul_mem_mergeClass hu.1 e).mpr hu) e
  rw [Positivity.T_iterate_two_pow_mul] at h
  omega

/-- `ℓ_C(2^e u) = ℓ_C(u) - e` on the class. -/
lemma coordF_two_pow_mul {a u : ℕ} (ha : 0 < a) (hR : NonRepeating a) (hu : u ∈ mergeClass a)
    (e : ℕ) : coordF a (2 ^ e * u) = coordF a u - e := by
  have h := coordF_iterate ha hR ((two_pow_mul_mem_mergeClass hu.1 e).mpr hu) e
  rw [F_iterate_two_pow_mul] at h
  omega

/-! ## Transport -/

set_option linter.unusedVariables false in
/-- The two coordinates have the transport property (6.2, `eq:transport`) on the class, with
rewards `(1, 1)` and `(1, 0)`, for every threshold. -/
theorem transport_coordT {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) (x₀ : ℝ) :
    Transport (mergeClass a) (fun n => (coordT a n : ℝ)) 1 1 x₀ := by
  intro x hx hm1 N hN hc hmT hM
  refine ⟨(transport_class a x₀ x hx hm1 N hN hc hmT hM).1, fun hNC => ?_⟩
  obtain ⟨hTb, -⟩ := T_blocks hN (passT x N - mT x)
  have h := coordT_iterate hR hNC (wsum (vword N) (passT x N - mT x) + (passT x N - mT x))
  rw [hTb] at h
  simp only [h]
  push_cast
  ring

theorem transport_coordF {a : ℕ} (ha : 0 < a) (hR : NonRepeating a) (x₀ : ℝ) :
    Transport (mergeClass a) (fun n => (coordF a n : ℝ)) 1 0 x₀ := by
  intro x hx hm1 N hN hc hmT hM
  refine ⟨(transport_class a x₀ x hx hm1 N hN hc hmT hM).1, fun hNC => ?_⟩
  obtain ⟨hFb, -⟩ := F_blocks hN (passT x N - mT x)
  have h := coordF_iterate ha hR hNC (wsum (vword N) (passT x N - mT x))
  rw [hFb] at h
  simp only [h]
  push_cast
  ring

/-! ## A finite union of classes (Theorem 6.10(iii)) -/

/-- Pairwise non-merging base points have disjoint classes. -/
lemma mem_mergeClass_unique {A : Finset ℕ} (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a')
    {a b n : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hna : n ∈ mergeClass a) (hnb : n ∈ mergeClass b) :
    a = b :=
  hdis a ha b hb (merge_equivalence.trans (merge_equivalence.symm hna.2) hnb.2)

/-- The class-dependent clock `ℓ_{C(n)}(n) - j_{C(n)}` on a union of classes, for a coordinate
`coord` (`coordT` or `coordF`) and one level `jC a` per base point (zero off the union). -/
def classClock (A : Finset ℕ) (coord : ℕ → ℕ → ℤ) (jC : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ a ∈ A, (mergeClass a).indicator (fun n => coord a n - jC a) n

lemma classClock_eq {A : Finset ℕ} (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a')
    (coord : ℕ → ℕ → ℤ) (jC : ℕ → ℤ) {a n : ℕ} (ha : a ∈ A) (hn : n ∈ mergeClass a) :
    classClock A coord jC n = coord a n - jC a := by
  unfold classClock
  rw [Finset.sum_eq_single_of_mem a ha, Set.indicator_of_mem hn]
  intro b hb hba
  exact Set.indicator_of_notMem (fun hnb => hba (mem_mergeClass_unique hdis hb ha hnb hn)) _

/-- **Transport for the class-dependent clock** on a finite union of pairwise non-merging classes,
when each coordinate has the transport property on its class. -/
theorem transport_classClock {A : Finset ℕ} (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a')
    (coord : ℕ → ℕ → ℤ) (jC : ℕ → ℤ) {ρ η x₀ : ℝ}
    (ht : ∀ a ∈ A, Transport (mergeClass a) (fun n => (coord a n : ℝ)) ρ η x₀) :
    Transport (⋃ a ∈ A, mergeClass a) (fun n => (classClock A coord jC n : ℝ)) ρ η x₀ := by
  intro x hx hm1 N hN hc hmT hM
  have h := fun a ha => ht a ha x hx hm1 N hN hc hmT hM
  refine ⟨?_, fun hNU => ?_⟩
  · simp only [Set.mem_iUnion]
    exact ⟨fun ⟨a, ha, hNa⟩ => ⟨a, ha, (h a ha).1.mp hNa⟩,
      fun ⟨a, ha, hMa⟩ => ⟨a, ha, (h a ha).1.mpr hMa⟩⟩
  · simp only [Set.mem_iUnion] at hNU
    obtain ⟨a, ha, hNa⟩ := hNU
    have hMa := (h a ha).1.mp hNa
    have hq := (h a ha).2 hNa
    simp only at hq ⊢
    rw [classClock_eq hdis coord jC ha hNa, classClock_eq hdis coord jC ha hMa]
    push_cast
    linarith

/-- The class-dependent clock of the raw coordinate has the transport property with reward
`(1, 1)`, and that of the shortcut coordinate with reward `(1, 0)`, at every threshold. -/
theorem transport_classClockT {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a ∧ NonRepeating a)
    (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') (jC : ℕ → ℤ) (x₀ : ℝ) :
    Transport (⋃ a ∈ A, mergeClass a) (fun n => (classClock A coordT jC n : ℝ)) 1 1 x₀ :=
  transport_classClock hdis coordT jC fun a ha => transport_coordT (hA a ha).1 (hA a ha).2 x₀

theorem transport_classClockF {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a ∧ NonRepeating a)
    (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') (jC : ℕ → ℤ) (x₀ : ℝ) :
    Transport (⋃ a ∈ A, mergeClass a) (fun n => (classClock A coordF jC n : ℝ)) 1 0 x₀ :=
  transport_classClock hdis coordF jC fun a ha => transport_coordF (hA a ha).1 (hA a ha).2 x₀

/-- **Doubling for the class-dependent clock**: for `u > 0`, `2^e u` lies in the union iff `u` does,
and the clock drops by `e`, when each coordinate drops by `e` under `u ↦ 2^e u` on its class. -/
lemma classClock_two_pow_mul {A : Finset ℕ} (hdis : ∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a')
    (coord : ℕ → ℕ → ℤ) (jC : ℕ → ℤ)
    (hc : ∀ a ∈ A, ∀ u ∈ mergeClass a, ∀ e : ℕ, coord a (2 ^ e * u) = coord a u - e)
    {u : ℕ} (hu : 0 < u) (e : ℕ) :
    (2 ^ e * u ∈ ⋃ a ∈ A, mergeClass a ↔ u ∈ ⋃ a ∈ A, mergeClass a) ∧
      (u ∈ ⋃ a ∈ A, mergeClass a →
        classClock A coord jC (2 ^ e * u) = classClock A coord jC u - e) := by
  simp only [Set.mem_iUnion]
  refine ⟨⟨fun ⟨a, ha, h⟩ => ⟨a, ha, (two_pow_mul_mem_mergeClass hu e).mp h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, (two_pow_mul_mem_mergeClass hu e).mpr h⟩⟩, ?_⟩
  rintro ⟨a, ha, hua⟩
  rw [classClock_eq hdis coord jC ha ((two_pow_mul_mem_mergeClass hu e).mpr hua),
    classClock_eq hdis coord jC ha hua, hc a ha u hua e]
  ring

end CollatzCLT
