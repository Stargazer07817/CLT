import LeanClt.Renewal.Defs
import LeanClt.Elementary.Affine
import LeanClt.Sampling.Basic

/-!
# §3 and §5: definitions

## The geometric model (§2.3)

A *word* of length `n` with total `s` is a composition `a : Fin n → ℕ` of `s` into `n` positive
parts; under `Geom(2)^n` it has probability `2^{-s}`.

* `Xmod a`: the target-outward Syracuse offset `X̃_n = ∑_{j=1}^n 3^{j-1} 2^{-S_j}` reduced
  modulo `3^n` (using the inverse of `2` in `ℤ/3^nℤ`), equation (2.3).
* `muJ n s x = P(S_n = s, X_n = x)`, the joint law `μ_n`.
* `Qop n m ν`: the operator `Q^{(n)}_m` of (2.4), which keeps the counter and the residue modulo
  `3^m` and spreads the remaining ternary digits uniformly.
* `JointMixing`: **Theorem 3.1**, `‖μ_n - Q^{(n)}_m μ_n‖₁ ≤ C_A m^{-A}`. It is proved from Tao's
  imports in `Mixing/Telescope.lean` (`jointMixing_of_tao`); §5–§6 take it as a hypothesis, and
  `Main/OfTao.lean` discharges it.

## First passage and the backtracked target set (§5.1)

* `Lx x = log x`, `alpha = 1.001`, `n0 x = ⌊L/(10ℓ)⌋`, `mT x = ⌊10⁻⁵ L⌋` (5.1).
* `crosses x N`, `passT x N = T_x(N)`: the first `r` with `U^r(N) ≤ x`.
* `Mset x`: the backtracked target set `𝓜_x` of (5.3).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## The geometric model -/

/-- Words of length `n` with total `s`: compositions of `s` into `n` positive parts. -/
def words (n s : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.Nat.antidiagonalTuple n s).filter (fun a => ∀ i, 1 ≤ a i)

/-- The inverse of `2` in `ℤ/3^nℤ`. -/
def half (n : ℕ) : ZMod (3 ^ n) := (2 : ZMod (3 ^ n))⁻¹

/-- The partial sum `S_{j+1} = a_0 + ⋯ + a_j` of a word. -/
def psum {n : ℕ} (a : Fin n → ℕ) (j : Fin n) : ℕ := ∑ i : Fin n, if i ≤ j then a i else 0

/-- The target-outward offset `X_n = ∑_{j=1}^n 3^{j-1} 2^{-S_j} mod 3^n` (2.3). -/
def Xmod {n : ℕ} (a : Fin n → ℕ) : ZMod (3 ^ n) :=
  ∑ j : Fin n, (3 : ZMod (3 ^ n)) ^ (j : ℕ) * half n ^ psum a j

/-- The joint law `μ_n(s, x) = P(S_n = s, X_n = x)` under `Geom(2)^n`. -/
def muJ (n s : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  ∑ a ∈ words n s, if Xmod a = x then (1 / 2 : ℝ) ^ s else 0

/-- The smoothing operator `Q^{(n)}_m` (2.4):
`(Q ν)(s, x) = 3^{m-n} ∑_{y ≡ x (3^m)} ν(s, y)`. -/
def Qop (n m : ℕ) (ν : ℕ → ZMod (3 ^ n) → ℝ) (s : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  (3 : ℝ) ^ ((m : ℤ) - n) *
    ∑ y : ZMod (3 ^ n), if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast x then ν s y else 0

/-- **Theorem 3.1 (joint offset/counter mixing)**, as a hypothesis:
for every `A > 0` there is `C_A` with `‖μ_n - Q^{(n)}_m μ_n‖₁ ≤ C_A m^{-A}` for `1 ≤ m ≤ n`
(the `L¹` norm on `ℕ × ℤ/3^nℤ`, without a factor `1/2`). -/
def JointMixing : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ m n : ℕ, 1 ≤ m → m ≤ n →
    ∑' s : ℕ, ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| ≤ C * (m : ℝ) ^ (-A)

/-! ## Parameters (5.1) -/

/-- `L = log x`. -/
def Lx (x : ℝ) : ℝ := Real.log x

/-- `α = 1.001`. -/
def alpha : ℝ := 1.001

/-- `n₀ = ⌊L/(10ℓ)⌋`. -/
def n0 (x : ℝ) : ℕ := ⌊Lx x / (10 * ell)⌋₊

/-- `m = ⌊10⁻⁵ L⌋`, the coarse depth (the paper's `m = ⌊(α-1)L/100⌋`). -/
def mT (x : ℝ) : ℕ := ⌊(alpha - 1) * Lx x / 100⌋₊

/-! ## First passage below `x` -/

/-- The `U`-orbit of `N` reaches `[0, x]`. -/
def crosses (x : ℝ) (N : ℕ) : Prop := ∃ r : ℕ, (U^[r] N : ℝ) ≤ x

/-- The first passage time `T_x(N) = inf {r ≥ 0 : U^r(N) ≤ x}` (meaningful when
`crosses x N`). -/
def passT (x : ℝ) (N : ℕ) : ℕ := sInf {r : ℕ | (U^[r] N : ℝ) ≤ x}

/-- The backtracked target set `𝓜_x` (5.3): odd `M` with `T_x(M) = m` and
`L + cm - L^{0.7} ≤ log M ≤ L + cm + L^{0.7}`. -/
def Mset (x : ℝ) : Set ℕ :=
  {M | Odd M ∧ crosses x M ∧ passT x M = mT x ∧
    |Real.log M - (Lx x + c * mT x)| ≤ Lx x ^ (0.7 : ℝ)}

/-- The event `𝓔'` of Theorem 5.10 for a source `N`: `m ≤ T_x(N) < ∞` and the backtracked
point `U^{T_x(N) - m}(N)` lies in `E`. -/
def Event (x : ℝ) (E : Finset ℕ) (N : ℕ) : Prop :=
  crosses x N ∧ mT x ≤ passT x N ∧ U^[passT x N - mT x] N ∈ E

open Classical in
/-- The left side of (5.14): `E[1_{𝓔'} e^{i s (q(M) - ρ S - η r)}]` for `N_Y` uniform on the odd
integers of `[Y, 2Y]`, with `r = T_x(N_Y) - m`, `M = U^r(N_Y)` and `S = S_r(N_Y)`. -/
def transferLHS (x Y : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (ρ η s : ℝ) : ℂ :=
  ((oddClosed Y).card : ℂ)⁻¹ * ∑ N ∈ oddClosed Y,
    if Event x E N then
      cexp ((((s * (q (U^[passT x N - mT x] N) - ρ * wsum (vword N) (passT x N - mT x) -
        η * (passT x N - mT x : ℕ))) : ℝ) : ℂ) * I)
    else 0

open Classical in
/-- The right side of (5.14):
`(Y/L_Y) ∑_{M ∈ E} (3^m/M) E[1{X_m ≡ M} 1{S_m ≤ 3m} e^{is(q(M) - ρ S_m - η m)}
R^{ρ,η}_s(log(Y/M) - Z_m)]`, with the geometric expectation written as a sum over words. -/
def transferRHS (x Y : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (ρ η s : ℝ) : ℂ :=
  ((Y / (oddClosed Y).card : ℝ) : ℂ) * ∑ M ∈ E, (((3 : ℝ) ^ mT x / M : ℝ) : ℂ) *
    ∑ S ∈ Icc (mT x) (3 * mT x), ∑ a ∈ words (mT x) S,
      if Xmod a = (M : ZMod (3 ^ mT x)) then
        (((1 / 2 : ℝ) ^ S : ℝ) : ℂ) *
          cexp (((s * (q M - ρ * S - η * mT x) : ℝ) : ℂ) * I) *
          renewalR ρ η s (Real.log (Y / M) - (ell * S - bet * mT x))
      else 0

/-- `P(X_m ≡ M (3^m))` under the geometric law. -/
def probXm (m M : ℕ) : ℝ := ∑' S : ℕ, muJ m S (M : ZMod (3 ^ m))

open Classical in
/-- `P(𝓔')`: the left side of (5.15). -/
def eventProb (x Y : ℝ) (E : Finset ℕ) : ℝ :=
  ((oddClosed Y).card : ℝ)⁻¹ * ((oddClosed Y).filter (Event x E)).card

/-! ## The transport property (§6.1) -/

/-- **Transport property (6.2)** of a set `A` and clock `q` with reward `(ρ, η)`, for thresholds
`x ≥ x₀` with `m ≥ 1`: whenever an odd `N` has `m ≤ T_x(N) < ∞` with backtracked point
`M = U^{T_x(N) - m}(N) ∈ 𝓜_x`, early total `S` and early depth `r = T_x(N) - m`, then
`N ∈ A ↔ M ∈ A`, and `q(N) = q(M) - ρS - ηr` on `A`.

The condition `m ≥ 1` (true once `x ≥ e^{10⁵}`) is needed for the verification in §6.5: with
`m = 0` the backtracked point is the crossing point `M ≤ x` itself, and the halving run just
before it can pass through an even target `b` (e.g. `b = 10`, `x = 11`, `N = 13`, `M = 5`). -/
def Transport (A : Set ℕ) (q : ℕ → ℝ) (ρ η x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → 1 ≤ mT x → ∀ N : ℕ, Odd N → crosses x N → mT x ≤ passT x N →
    U^[passT x N - mT x] N ∈ Mset x →
      (N ∈ A ↔ U^[passT x N - mT x] N ∈ A) ∧
      (N ∈ A → q N = q (U^[passT x N - mT x] N) -
        ρ * wsum (vword N) (passT x N - mT x) - η * (passT x N - mT x : ℕ))

end CollatzCLT
