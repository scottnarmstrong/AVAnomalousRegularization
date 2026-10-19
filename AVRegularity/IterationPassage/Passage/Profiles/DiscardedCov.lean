-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.External.FourierCarrierParseval
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
public import AVRegularity.Definitions.Iteration.CascadeStatement
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.EntryWeak.ScheduledAnchorDistance
import AVRegularity.EntryWeak.SourceParameterPeriodicity
import AVenhance.Infra.Section5.AnalyticBridge.Sobolev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public section
namespace AVRegularity.IterationPassage.Passage

/-! **Real algebra of the retained lift profile**.

Abstract real lemmas, no analysis. Notation: `ρ` the lift radius, `E` the parent wavelength,
`r = c_r ρ θ` the width of the fresh kernel (`θ = E^{σ₀}`), `ω = E^c` with `ρ ≤ C_ρ E ω`.

* `liftInput_radius_alg`: `ρ^j r^{l-j} ≤ C_ρ^{K-1} c_r^{-N} ρ E^{l-1}` for `1 ≤ j ≤ K + N` and
  `l = min{K, j + 2n}`. For `j ≤ l` it is `r ≤ ρ ≤ E`. For `l = K < j` the `j - K ≤ N` negative
  powers of `r` cost `(c_r θ)^{-N}`, paid by `(ρ/E)^{K-1} ≤ C_ρ^{K-1} ω^{K-1}` and the exponent
  condition `ω^{K-1} ≤ θ^N` (that is `σ₀N ≤ c(K-1)`).
* `liftInput_term_alg`: one term of the word bound of `P_p𝖱S_r` at the radius `ρ`.
* `liftScale_alg`: `e^{-s} d_* E^{s-1} ≤ 2C E^{μ_s}`, `μ_s = (q-1)(1-s) - qγ`, from `e ≤ 2E^q`
  and `d_*/e ≤ C E^{-qγ}`.

Special cases: `N = 0` (only `j ≤ K`, no negative power); `n = 0` (no covariance factor);
`j = 1` (`l ≥ 1 = j`). -/

/-- The radius powers of one term: `ρ^j r^{l-j} ≤ C_ρ^{K-1} c_r^{-N} ρ E^{l-1}`. -/
theorem liftInput_radius_alg {ρ E r cr θ ω Cρ : ℝ} {K N j l : ℕ}
    (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : r = cr * ρ * θ)
    (hCρ : 1 ≤ Cρ) (hρω : ρ ≤ Cρ * (E * ω)) (hωθ : ω ^ (K - 1) ≤ θ ^ N)
    (hj1 : 1 ≤ j) (hjKN : j ≤ K + N) (hl1 : 1 ≤ l) (hcase : j ≤ l ∨ l = K) :
    ρ ^ j * (r ^ l / r ^ j) ≤ Cρ ^ (K - 1) * cr⁻¹ ^ N * (ρ * E ^ (l - 1)) := by
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrρ : r ≤ ρ := by
    rw [hr]
    calc cr * ρ * θ ≤ 1 * ρ * 1 := by gcongr
      _ = ρ := by ring
  have hCρ0 : 0 ≤ Cρ := zero_le_one.trans hCρ
  have hconst : 1 ≤ Cρ ^ (K - 1) * cr⁻¹ ^ N :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCρ)
      (one_le_pow₀ ((one_le_inv₀ hcr).mpr hcr1))
  by_cases hjl : j ≤ l
  · obtain ⟨a, rfl⟩ : ∃ a, l = j + a := ⟨l - j, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
    have h1 : r ^ (b + 1 + a) / r ^ (b + 1) = r ^ a := by
      rw [pow_add (a := r) (m := b + 1) (n := a)]
      field_simp
    have hexp : b + 1 + a - 1 = b + a := by omega
    rw [h1, hexp]
    have h2 : ρ ^ (b + 1) * r ^ a ≤ ρ * E ^ (b + a) := by
      calc ρ ^ (b + 1) * r ^ a = ρ * (ρ ^ b * r ^ a) := by ring
        _ ≤ ρ * (E ^ b * E ^ a) := by
          gcongr
          exact hrρ.trans hρE
        _ = ρ * E ^ (b + a) := by rw [pow_add]
    exact h2.trans (le_mul_of_one_le_left (by positivity) hconst)
  · have hlK : l = K := hcase.resolve_left hjl
    subst hlK
    obtain ⟨b, rfl⟩ : ∃ b, j = l + b := ⟨j - l, by omega⟩
    have hbN : b ≤ N := by omega
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    have hωθ' : ω ^ k ≤ θ ^ N := by simpa only [Nat.add_sub_cancel] using hωθ
    have hθN : 0 < θ ^ N := pow_pos hθ N
    have hcθ : 0 < cr * θ := mul_pos hcr hθ
    have hcθ1 : cr * θ ≤ 1 := (mul_le_mul hcr1 hθ1 hθ.le zero_le_one).trans_eq (one_mul 1)
    have hinv : ((cr * θ) ^ b)⁻¹ ≤ cr⁻¹ ^ N * (θ ^ N)⁻¹ := by
      have hp : (cr * θ) ^ N ≤ (cr * θ) ^ b := pow_le_pow_of_le_one hcθ.le hcθ1 hbN
      calc ((cr * θ) ^ b)⁻¹ ≤ ((cr * θ) ^ N)⁻¹ := inv_anti₀ (pow_pos hcθ N) hp
        _ = cr⁻¹ ^ N * (θ ^ N)⁻¹ := by rw [mul_pow, mul_inv, inv_pow]
    have hρk : ρ ^ k ≤ Cρ ^ k * E ^ k * θ ^ N := by
      calc ρ ^ k ≤ (Cρ * (E * ω)) ^ k := pow_le_pow_left₀ hρ.le hρω k
        _ = Cρ ^ k * E ^ k * ω ^ k := by ring
        _ ≤ Cρ ^ k * E ^ k * θ ^ N := mul_le_mul_of_nonneg_left hωθ' (by positivity)
    have hquot : r ^ (k + 1) / r ^ (k + 1 + b) = (r ^ b)⁻¹ := by
      rw [pow_add (a := r) (m := k + 1) (n := b)]
      field_simp
    have hrb : (r ^ b)⁻¹ = (ρ ^ b)⁻¹ * ((cr * θ) ^ b)⁻¹ := by
      rw [hr, ← mul_inv, ← mul_pow]
      congr 2
      ring
    have hρb : ρ ^ (k + 1 + b) * (ρ ^ b)⁻¹ = ρ * ρ ^ k := by
      rw [pow_add (a := ρ) (m := k + 1) (n := b), mul_assoc,
        mul_inv_cancel₀ (pow_pos hρ b).ne', mul_one, pow_succ]
      ring
    rw [hquot, hrb, ← mul_assoc, hρb, Nat.add_sub_cancel]
    calc ρ * ρ ^ k * ((cr * θ) ^ b)⁻¹
        ≤ ρ * (Cρ ^ k * E ^ k * θ ^ N) * (cr⁻¹ ^ N * (θ ^ N)⁻¹) := by gcongr
      _ = Cρ ^ k * cr⁻¹ ^ N * (ρ * E ^ k) * (θ ^ N * (θ ^ N)⁻¹) := by ring
      _ = Cρ ^ k * cr⁻¹ ^ N * (ρ * E ^ k) := by rw [mul_inv_cancel₀ hθN.ne', mul_one]

/-- One term of the word bound of `P_p𝖱S_r` at the radius `ρ`: order `j`, covariance degree `n`,
kernel order `i = j + 2n`, field order `l = min{K, i}`. -/
theorem liftInput_term_alg {ρ E r cr θ ω Cρ εc Cc Cn Ck s : ℝ} {K N p j n : ℕ}
    (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : r = cr * ρ * θ)
    (hCρ : 1 ≤ Cρ) (hρω : ρ ≤ Cρ * (E * ω)) (hωθ : ω ^ (K - 1) ≤ θ ^ N)
    (hε : 0 ≤ εc) (hεC : εc ≤ Cc) (hCc : 1 ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck) (hK : 1 ≤ K)
    (hj1 : 1 ≤ j) (hj : j ≤ K + N) (hn : n ≤ p) :
    ρ ^ j * ((4 * (εc * r ^ 2)) ^ n * Cn * 2 ^ (j + 2 * n) *
        (Ck * r ^ (((min K (j + 2 * n) : ℕ) : ℝ) - ((j + 2 * n : ℕ) : ℝ)))) ≤
      (4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck * Cρ ^ (K - 1) * cr⁻¹ ^ N) *
        (ρ * E ^ (s - 1)) * E ^ (((min K (j + 2 * n) : ℕ) : ℝ) - s) := by
  have hr0 : 0 < r := by rw [hr]; positivity
  have hCρ0 : 0 ≤ Cρ := zero_le_one.trans hCρ
  have hCc0 : 0 ≤ Cc := zero_le_one.trans hCc
  obtain ⟨l, hl⟩ : ∃ l, l = min K (j + 2 * n) := ⟨_, rfl⟩
  have hl1 : 1 ≤ l := by omega
  have hcase : j ≤ l ∨ l = K := by omega
  rw [← hl]
  have hrpow : r ^ ((l : ℝ) - ((j + 2 * n : ℕ) : ℝ)) = r ^ l / r ^ (j + 2 * n) := by
    rw [Real.rpow_sub hr0, Real.rpow_natCast, Real.rpow_natCast]
  have hEpow : E ^ (s - 1) * E ^ ((l : ℝ) - s) = E ^ (l - 1) := by
    rw [← Real.rpow_add hE, ← Real.rpow_natCast, Nat.cast_sub hl1]
    congr 1
    push_cast
    ring
  have hcomb : (4 * (εc * r ^ 2)) ^ n * (r ^ l / r ^ (j + 2 * n)) =
      4 ^ n * εc ^ n * (r ^ l / r ^ j) := by
    rw [mul_pow, mul_pow, ← pow_mul, pow_add (a := r) (m := j) (n := 2 * n)]
    field_simp
  have hcore := liftInput_radius_alg (K := K) (N := N) (j := j) (l := l) hρ hE hρE hcr hcr1 hθ hθ1
    hr hCρ hρω hωθ hj1 hj hl1 hcase
  have h4 : (4 : ℝ) ^ n ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num) hn
  have hεn : εc ^ n ≤ Cc ^ p :=
    (pow_le_pow_left₀ hε hεC n).trans (pow_le_pow_right₀ hCc hn)
  have h2 : (2 : ℝ) ^ (j + 2 * n) ≤ 2 ^ (K + N + 2 * p) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hq0 : 0 ≤ ρ ^ j * (r ^ l / r ^ j) := by positivity
  calc ρ ^ j * ((4 * (εc * r ^ 2)) ^ n * Cn * 2 ^ (j + 2 * n) *
        (Ck * r ^ ((l : ℝ) - ((j + 2 * n : ℕ) : ℝ))))
      = (4 ^ n * εc ^ n * Cn * 2 ^ (j + 2 * n) * Ck) * (ρ ^ j * (r ^ l / r ^ j)) := by
        rw [hrpow]
        calc ρ ^ j * ((4 * (εc * r ^ 2)) ^ n * Cn * 2 ^ (j + 2 * n) *
              (Ck * (r ^ l / r ^ (j + 2 * n))))
            = ρ ^ j * (Cn * 2 ^ (j + 2 * n) * Ck) *
              ((4 * (εc * r ^ 2)) ^ n * (r ^ l / r ^ (j + 2 * n))) := by ring
          _ = _ := by rw [hcomb]; ring
    _ ≤ (4 ^ p * Cc ^ p * Cn * 2 ^ (K + N + 2 * p) * Ck) *
        (Cρ ^ (K - 1) * cr⁻¹ ^ N * (ρ * E ^ (l - 1))) := by
        gcongr
    _ = _ := by rw [← hEpow]; ring

/-- The scale of the retained lift profile: `e^{-s} d_* E^{s-1} ≤ 2C E^{μ_s}`. -/
theorem liftScale_alg {e E s q γ Cl dB : ℝ} (he : 0 < e) (hE : 0 < E) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (heq : e ≤ 2 * E ^ q) (hdB0 : 0 ≤ dB) (hdB : dB ≤ Cl * E ^ (-(q * γ))) :
    e ^ (-s) * (e * dB) * E ^ (s - 1) ≤ 2 * Cl * E ^ ((q - 1) * (1 - s) - q * γ) := by
  have h1s : 0 ≤ 1 - s := by linarith
  have hee : e ^ (-s) * e = e ^ (1 - s) := by
    have h := Real.rpow_add he (-s) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hEq : 0 < E ^ q := Real.rpow_pos_of_pos hE q
  have h2 : (2 : ℝ) ^ (1 - s) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - s) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 2 := Real.rpow_one 2
  have hepow : e ^ (1 - s) ≤ 2 * E ^ (q * (1 - s)) := by
    calc e ^ (1 - s) ≤ (2 * E ^ q) ^ (1 - s) := Real.rpow_le_rpow he.le heq h1s
      _ = 2 ^ (1 - s) * (E ^ q) ^ (1 - s) := Real.mul_rpow (by norm_num) hEq.le
      _ = 2 ^ (1 - s) * E ^ (q * (1 - s)) := by rw [← Real.rpow_mul hE.le]
      _ ≤ 2 * E ^ (q * (1 - s)) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hE.le _)
  have hE0 : 0 ≤ E ^ (s - 1) := Real.rpow_nonneg hE.le _
  have hexp : E ^ (q * (1 - s)) * E ^ (-(q * γ)) * E ^ (s - 1) =
      E ^ ((q - 1) * (1 - s) - q * γ) := by
    rw [← Real.rpow_add hE, ← Real.rpow_add hE]
    congr 1
    ring
  calc e ^ (-s) * (e * dB) * E ^ (s - 1) = e ^ (1 - s) * dB * E ^ (s - 1) := by
        rw [← hee]; ring
    _ ≤ (2 * E ^ (q * (1 - s))) * (Cl * E ^ (-(q * γ))) * E ^ (s - 1) := by
        gcongr
    _ = 2 * Cl * (E ^ (q * (1 - s)) * E ^ (-(q * γ)) * E ^ (s - 1)) := by ring
    _ = _ := by rw [hexp]

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.IterationPassage.Passage

/-! **Scaled Sobolev to profile, part 1: the lattice sum**.

The Fourier weight `w_k = (1 + (2πρ)² |k|²)²` on `ℤ²` has `∑_k w_k⁻¹ ≤ 9 ρ⁻²` for `0 < ρ ≤ 1`.
This is the sharp power of `ρ`: it is what makes `‖f‖_∞ ≤ C ρ⁻¹ (∑ w_k |f̂_k|²)^{1/2}`.
The proof is elementary: `w_k⁻¹ ≤ g(k₀) g(k₁)` with `g(n) = (1 + a²n²)⁻¹`, `a = 2πρ`, and
`∑_{n ∈ s} g(n) ≤ 2 + 4/a` for every finite `s ⊂ ℤ` by a telescoping bound.
Special cases: `ρ = 1` (`a = 2π`) gives a bounded sum; `ρ → 0` grows like `ρ⁻²`, as the number of
lattice points in the ball of radius `1/ρ`. -/

section
open AVRegularity.External

/-- The Fourier weight `(1 + (2πρ)² |k|²)²` of the scaled Sobolev readout. -/
def sobolevProfileWeight (ρ : ℝ) (k : Fin 2 → ℤ) : ℝ :=
  (1 + (2 * Real.pi * ρ) ^ 2 * torusFrequencySq k) ^ 2

theorem sobolevProfileWeight_pos (ρ : ℝ) (k : Fin 2 → ℤ) : 0 < sobolevProfileWeight ρ k := by
  unfold sobolevProfileWeight torusFrequencySq
  positivity

theorem sobolevProfileLattice_telescope (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((1 + a * ((n : ℝ) + 1)) ^ 2)⁻¹ ≤ a⁻¹ := by
  have key : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((1 + a * ((n : ℝ) + 1)) ^ 2)⁻¹ ≤
      a⁻¹ * (1 - (1 + a * (N : ℝ))⁻¹) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hx : 0 < 1 + a * (N : ℝ) := by positivity
      have hy : 0 < 1 + a * ((N : ℝ) + 1) := by positivity
      have hstep : ((1 + a * ((N : ℝ) + 1)) ^ 2)⁻¹ ≤
          a⁻¹ * ((1 + a * (N : ℝ))⁻¹ - (1 + a * (((N + 1 : ℕ) : ℝ)))⁻¹) := by
        have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have h1 : a⁻¹ * ((1 + a * (N : ℝ))⁻¹ - (1 + a * ((N : ℝ) + 1))⁻¹) =
            ((1 + a * (N : ℝ)) * (1 + a * ((N : ℝ) + 1)))⁻¹ := by
          field_simp
          ring
        rw [h1]
        apply inv_anti₀ (by positivity)
        nlinarith
      have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
      calc _ ≤ a⁻¹ * (1 - (1 + a * (N : ℝ))⁻¹) +
            a⁻¹ * ((1 + a * (N : ℝ))⁻¹ - (1 + a * (((N + 1 : ℕ) : ℝ)))⁻¹) := add_le_add ih hstep
        _ = a⁻¹ * (1 - (1 + a * (((N + 1 : ℕ) : ℝ)))⁻¹) := by ring
  refine (key N).trans ?_
  have : 0 ≤ (1 + a * (N : ℝ))⁻¹ := by positivity
  nlinarith [inv_pos.mpr ha]

/-- The one-dimensional kernel `g(n) = (1 + a²n²)⁻¹`. -/
def sobolevProfileKernel (a : ℝ) (n : ℤ) : ℝ := (1 + a ^ 2 * (n : ℝ) ^ 2)⁻¹

theorem sobolevProfileKernel_neg (a : ℝ) (n : ℤ) :
    sobolevProfileKernel a (-n) = sobolevProfileKernel a n := by
  simp [sobolevProfileKernel]

theorem sobolevProfileKernel_nonneg (a : ℝ) (n : ℤ) : 0 ≤ sobolevProfileKernel a n := by
  unfold sobolevProfileKernel
  positivity

theorem sobolevProfileKernel_le (a : ℝ) (ha : 0 < a) (m : ℕ) :
    sobolevProfileKernel a (m : ℤ) ≤ 2 * ((1 + a * (m : ℝ)) ^ 2)⁻¹ := by
  unfold sobolevProfileKernel
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : (0 : ℝ) < 1 + a ^ 2 * ((m : ℤ) : ℝ) ^ 2 := by positivity
  have h2 : (0 : ℝ) < (1 + a * (m : ℝ)) ^ 2 := by positivity
  rw [show 2 * ((1 + a * (m : ℝ)) ^ 2)⁻¹ = (((1 + a * (m : ℝ)) ^ 2) / 2)⁻¹ by
    rw [inv_div, div_eq_mul_inv], inv_le_inv₀ h1 (by positivity)]
  push_cast
  nlinarith [sq_nonneg (a * (m : ℝ) - 1)]

theorem sobolevProfileKernel_Icc_sum_le (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, sobolevProfileKernel a n ≤
      1 + 4 * ∑ i ∈ Finset.range N, ((1 + a * ((i : ℝ) + 1)) ^ 2)⁻¹ := by
  induction N with
  | zero => simp [sobolevProfileKernel]
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hn1 : (-((N + 1 : ℕ) : ℤ)) ∉ insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    have hn2 : ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      push_cast
      omega
    rw [hset, Finset.sum_insert hn1, Finset.sum_insert hn2, sobolevProfileKernel_neg,
      Finset.sum_range_succ]
    have hb := sobolevProfileKernel_le a ha (N + 1)
    have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hb
    linarith

theorem sobolevProfileKernel_finset_sum_le (a : ℝ) (ha : 0 < a) (s : Finset ℤ) :
    ∑ n ∈ s, sobolevProfileKernel a n ≤ 1 + 4 * a⁻¹ := by
  set N : ℕ := ∑ n ∈ s, n.natAbs with hN
  have hsub : s ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro n hn
    have : n.natAbs ≤ N := Finset.single_le_sum (f := fun n : ℤ => n.natAbs)
      (fun _ _ => Nat.zero_le _) hn
    simp only [Finset.mem_Icc]
    omega
  calc ∑ n ∈ s, sobolevProfileKernel a n
      ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) N, sobolevProfileKernel a n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sobolevProfileKernel_nonneg a n)
    _ ≤ 1 + 4 * ∑ i ∈ Finset.range N, ((1 + a * ((i : ℝ) + 1)) ^ 2)⁻¹ :=
        sobolevProfileKernel_Icc_sum_le a ha N
    _ ≤ 1 + 4 * a⁻¹ := by
        have := sobolevProfileLattice_telescope a ha N
        linarith

theorem sobolevProfileWeight_inv_le_kernel (ρ : ℝ) (k : Fin 2 → ℤ) :
    (sobolevProfileWeight ρ k)⁻¹ ≤
      sobolevProfileKernel (2 * Real.pi * ρ) (k 0) * sobolevProfileKernel (2 * Real.pi * ρ) (k 1) := by
  unfold sobolevProfileWeight sobolevProfileKernel torusFrequencySq
  rw [Fin.sum_univ_two, ← mul_inv]
  apply inv_anti₀ (by positivity)
  set x := (2 * Real.pi * ρ) ^ 2 * (k 0 : ℝ) ^ 2
  set y := (2 * Real.pi * ρ) ^ 2 * (k 1 : ℝ) ^ 2
  have hx : 0 ≤ x := by positivity
  have hy : 0 ≤ y := by positivity
  have : (2 * Real.pi * ρ) ^ 2 * ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) = x + y := by ring
  rw [this]
  nlinarith [mul_nonneg hx hy]

theorem sobolevProfileWeight_inv_finset_sum_le (ρ : ℝ) (hρ : 0 < ρ) (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, (sobolevProfileWeight ρ k)⁻¹ ≤ (1 + 4 * (2 * Real.pi * ρ)⁻¹) ^ 2 := by
  have ha : 0 < 2 * Real.pi * ρ := by positivity
  set a := 2 * Real.pi * ρ
  set N : ℕ := ∑ k ∈ s, ((k 0).natAbs + (k 1).natAbs) with hN
  have hsub : s ⊆ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(N : ℤ)) N) := by
    intro k hk
    have : (k 0).natAbs + (k 1).natAbs ≤ N := Finset.single_le_sum
      (f := fun k : Fin 2 → ℤ => (k 0).natAbs + (k 1).natAbs) (fun _ _ => Nat.zero_le _) hk
    rw [Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_Icc]
    fin_cases i <;> simp <;> omega
  calc ∑ k ∈ s, (sobolevProfileWeight ρ k)⁻¹
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(N : ℤ)) N),
          (sobolevProfileWeight ρ k)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => (inv_pos.mpr (sobolevProfileWeight_pos ρ k)).le)
    _ ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(N : ℤ)) N),
          ∏ i : Fin 2, sobolevProfileKernel a (k i) := by
        apply Finset.sum_le_sum
        intro k _
        rw [Fin.prod_univ_two]
        exact sobolevProfileWeight_inv_le_kernel ρ k
    _ = ∏ i : Fin 2, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, sobolevProfileKernel a n :=
        (Finset.prod_univ_sum (fun _ : Fin 2 => Finset.Icc (-(N : ℤ)) N)
          (fun _ n => sobolevProfileKernel a n)).symm
    _ ≤ (1 + 4 * a⁻¹) ^ 2 := by
        rw [Fin.prod_univ_two, ← sq]
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => sobolevProfileKernel_nonneg a n)
          (sobolevProfileKernel_finset_sum_le a ha _) 2

theorem sobolevProfileWeight_inv_summable (ρ : ℝ) (hρ : 0 < ρ) :
    Summable (fun k : Fin 2 → ℤ => (sobolevProfileWeight ρ k)⁻¹) :=
  summable_of_sum_le (fun k => (inv_pos.mpr (sobolevProfileWeight_pos ρ k)).le)
    (fun s => sobolevProfileWeight_inv_finset_sum_le ρ hρ s)

/-- **The lattice sum**: `∑_k w_k⁻¹ ≤ 9 ρ⁻²` for `0 < ρ ≤ 1`. -/
theorem sobolevProfileWeight_inv_tsum_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∑' k : Fin 2 → ℤ, (sobolevProfileWeight ρ k)⁻¹ ≤ 9 * (ρ ^ 2)⁻¹ := by
  refine ((sobolevProfileWeight_inv_summable ρ hρ).tsum_le_of_sum_le
    (fun s => sobolevProfileWeight_inv_finset_sum_le ρ hρ s)).trans ?_
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have ha : 0 < 2 * Real.pi * ρ := by positivity
  have h1 : 1 + 4 * (2 * Real.pi * ρ)⁻¹ ≤ 12 * (2 * Real.pi * ρ)⁻¹ := by
    have hle : 2 * Real.pi * ρ ≤ 2 * Real.pi := by nlinarith
    have : 1 ≤ 8 * (2 * Real.pi * ρ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ ha]
      linarith
    linarith
  have h2 : (1 + 4 * (2 * Real.pi * ρ)⁻¹) ^ 2 ≤ (12 * (2 * Real.pi * ρ)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  refine h2.trans ?_
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hsq : 36 * ρ ^ 2 ≤ (2 * Real.pi * ρ) ^ 2 := by
    have : (2 * Real.pi * ρ) ^ 2 = 4 * Real.pi ^ 2 * ρ ^ 2 := by ring
    rw [this]
    have hp2 : 9 < Real.pi ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hp2.le hρ2.le]
  have hinv : ((2 * Real.pi * ρ) ^ 2)⁻¹ ≤ (36 * ρ ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
  have h36 : (36 * ρ ^ 2)⁻¹ = (1 / 36) * (ρ ^ 2)⁻¹ := by
    rw [mul_inv]; ring
  have : (12 * (2 * Real.pi * ρ)⁻¹) ^ 2 = 144 * ((2 * Real.pi * ρ) ^ 2)⁻¹ := by
    rw [mul_pow, inv_pow]; norm_num
  rw [this]
  have hpos : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
  nlinarith
end

/-! **Scaled Sobolev to profile: the scalar sharp sup bound**.

For `W ∈ H^M(𝕋²)` (real, `TorusHk M ℝ`), `0 < ρ ≤ 1`, a derivative word `w` of length `j ≤ M - 2`
and a continuous periodic `h` equal almost everywhere on the unit cell to the weak jet
`⟨j, w⟩` of `W`:

`h(x)² ≤ C_M ρ^{-2j-2} ‖W‖²_{ρ,M}`  (`‖W‖²_{ρ,M} = factorialNormSq ρ W`).

Proof: weighted Fourier Cauchy-Schwarz (`torusFourierWeightedSupReadout`) with weights
`(1 + (2πρ)²|k|²)²` (lattice sum `≤ 9ρ⁻²`); the weighted energy of `ĥ_k = (2πik)^w ĥ₀(k)` is
bounded pointwise in `k` by `(1+t)² t^j ≤ 4 (1 + t^{j+2})`, `t = (2πρ)²|k|²`, against the
value coefficient and the top-order coefficient of one constant word (Parseval for the factorial
norm). Corollary for a classical representative
(`IsClassicalRep`) of order `n`, `M = n + 2`.
Special cases: `j = 0`, `ρ = 1`: the Sobolev embedding `H² ⊂ L∞`; a single mode `|k| ≈ 1/ρ`
gives equality of orders. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.External
  AVRegularity.EntryWeakProofs

local instance sobolevProfileScalarMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sobolevProfileScalarIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sobolevProfileScalarProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The constant of the scaled sup bound at Sobolev order `M`. -/
def sobolevScaledConst (M : ℕ) : ℝ := 36 * 2 ^ M * ((M.factorial : ℝ)) ^ 2

theorem sobolevScaled_alg_a (P Q c : ℝ) (j : ℕ) :
    (P ^ j * Q * c) ^ 2 = (P ^ 2) ^ j * Q ^ 2 * c ^ 2 := by ring

theorem sobolevScaled_alg_b (P x c : ℝ) (n : ℕ) :
    (P ^ n * x ^ n * c) ^ 2 = (P ^ 2) ^ n * (x ^ 2) ^ n * c ^ 2 := by ring

theorem sobolevScaled_poly (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    (1 + t) ^ 2 * t ^ j ≤ 4 * (1 + t ^ (j + 2)) := by
  have h1 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  have h2 : t ^ j ≤ 1 + t ^ (j + 2) := by
    by_cases h : t ≤ 1
    · have := pow_le_one₀ ht h (n := j)
      have : 0 ≤ t ^ (j + 2) := by positivity
      linarith
    · have h := not_le.mp h
      have := pow_le_pow_right₀ h.le (Nat.le_add_right j 2)
      linarith
  have h3 : 0 ≤ t ^ j := by positivity
  calc (1 + t) ^ 2 * t ^ j ≤ 2 * (1 + t ^ 2) * t ^ j := by gcongr
    _ = 2 * (t ^ j + t ^ (j + 2)) := by ring
    _ ≤ 4 * (1 + t ^ (j + 2)) := by
        have : 0 ≤ t ^ (j + 2) := by positivity
        linarith

theorem sobolevScaled_pointwise (ρ F c A E : ℝ) (j : ℕ) (hρ : 0 < ρ) (hF : 0 ≤ F)
    (hA : A ^ 2 ≤ ((2 * Real.pi) ^ 2 * F) ^ j * c ^ 2)
    (hE : c ^ 2 + ρ ^ (2 * (j + 2)) / ((j + 2).factorial : ℝ) ^ 2 *
      (((2 * Real.pi) ^ 2 * F) / 2) ^ (j + 2) * c ^ 2 ≤ E) :
    (1 + (2 * Real.pi * ρ) ^ 2 * F) ^ 2 * A ^ 2 ≤
      4 * 2 ^ (j + 2) * ((j + 2).factorial : ℝ) ^ 2 * (ρ ^ (2 * j))⁻¹ * E := by
  set u : ℝ := (2 * Real.pi) ^ 2 * F with hu
  have hu0 : 0 ≤ u := by positivity
  set t : ℝ := (2 * Real.pi * ρ) ^ 2 * F with ht
  have htu : t = ρ ^ 2 * u := by rw [ht, hu]; ring
  have ht0 : 0 ≤ t := by positivity
  set J : ℕ := j + 2 with hJ
  set D : ℝ := 2 ^ J * ((J.factorial : ℝ)) ^ 2 with hD
  have hD1 : 1 ≤ D := by
    have h1 : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (J.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos J
    rw [hD]; nlinarith [one_le_pow₀ (n := 2) h2]
  have hDpos : 0 < D := by linarith
  have e1 : t ^ J = ρ ^ (2 * J) * u ^ J := by rw [htu, mul_pow, ← pow_mul]
  have e2 : t ^ j = ρ ^ (2 * j) * u ^ j := by rw [htu, mul_pow, ← pow_mul]
  have hρj : 0 < ρ ^ (2 * j) := by positivity
  have hfac : 0 < ((J.factorial : ℝ)) := by exact_mod_cast Nat.factorial_pos J
  have e3 : ρ ^ (2 * J) / ((J.factorial : ℝ)) ^ 2 * (u / 2) ^ J = t ^ J / D := by
    rw [e1, hD, div_pow]
    field_simp
  have hE' : c ^ 2 * (1 + t ^ J / D) ≤ E := by
    have : c ^ 2 * (1 + t ^ J / D) = c ^ 2 + ρ ^ (2 * J) / ((J.factorial : ℝ)) ^ 2 *
        (u / 2) ^ J * c ^ 2 := by rw [e3]; ring
    rw [this]; exact hE
  have e4 : u ^ j = (ρ ^ (2 * j))⁻¹ * t ^ j := by
    rw [e2]; field_simp
  have hDE : (1 + t ^ J) * c ^ 2 ≤ D * E := by
    have h1 : D * (c ^ 2 * (1 + t ^ J / D)) ≤ D * E := mul_le_mul_of_nonneg_left hE' hDpos.le
    have h2 : D * (c ^ 2 * (1 + t ^ J / D)) = c ^ 2 * (D + t ^ J) := by field_simp
    have h3 : 0 ≤ c ^ 2 := by positivity
    nlinarith
  calc (1 + t) ^ 2 * A ^ 2 ≤ (1 + t) ^ 2 * (u ^ j * c ^ 2) := by gcongr
    _ = (ρ ^ (2 * j))⁻¹ * ((1 + t) ^ 2 * t ^ j) * c ^ 2 := by rw [e4]; ring
    _ ≤ (ρ ^ (2 * j))⁻¹ * (4 * (1 + t ^ J)) * c ^ 2 := by
        have := sobolevScaled_poly t ht0 j
        gcongr
    _ = 4 * (ρ ^ (2 * j))⁻¹ * ((1 + t ^ J) * c ^ 2) := by ring
    _ ≤ 4 * (ρ ^ (2 * j))⁻¹ * (D * E) := by gcongr
    _ = 4 * 2 ^ J * ((J.factorial : ℝ)) ^ 2 * (ρ ^ (2 * j))⁻¹ * E := by rw [hD]; ring

theorem sobolevScaled_realJetFourier_eq (M : ℕ) (W : TorusHk M ℝ) (a : JetIndex2 M) (k : Fin 2 → ℤ) :
    realJetFourier M W a k = UnitAddTorus.mFourierCoeff (torusJetComponentL2 W a) k := by
  rw [realJetFourier, UnitAddTorus.mFourierBasis_repr]
  rfl

theorem sobolevScaled_coeff_eq {M : ℕ} (W : TorusHk M ℝ) (a : JetIndex2 M) (h : Vec 2 → ℝ)
    (hae : h =ᵐ[volume.restrict AVenhance.unitCube] W.toFunction.jet a) (k : Fin 2 → ℤ) :
    AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (h x : ℂ)) k = realJetFourier M W a k := by
  rw [realJetFourier_apply,
    AVenhance.Infra.Section5.AnalyticBridge.Sobolev.mFourierCoeff_periodicToTorus]
  unfold AVenhance.Infra.Torus.smoothFourierCoeff
  rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  simp [hx]

theorem sobolevScaled_sq_le_freq (k : Fin 2 → ℤ) (i : Fin 2) :
    ((k i : ℤ) : ℝ) ^ 2 ≤ torusFrequencySq k := by
  unfold torusFrequencySq
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp <;> positivity

theorem sobolevScaled_exists_half (k : Fin 2 → ℤ) :
    ∃ i : Fin 2, torusFrequencySq k / 2 ≤ ((k i : ℤ) : ℝ) ^ 2 := by
  unfold torusFrequencySq
  rw [Fin.sum_univ_two]
  by_cases h : ((k 1 : ℤ) : ℝ) ^ 2 ≤ ((k 0 : ℤ) : ℝ) ^ 2
  · exact ⟨0, by linarith⟩
  · exact ⟨1, by linarith⟩

/-- Pointwise in the frequency: the weighted energy of the jet `⟨j,w⟩` is bounded by the
factorial energy of `W`. -/
theorem sobolevScaled_freq_bound {M : ℕ} (W : TorusHk M ℝ) {j : ℕ} (hj : j + 2 ≤ M)
    (w : DerivativeWord2 j) {ρ : ℝ} (hρ : 0 < ρ) (k : Fin 2 → ℤ) :
    sobolevProfileWeight ρ k *
        ‖realJetFourier M W (⟨⟨j, by omega⟩, w⟩ : JetIndex2 M) k‖ ^ 2 ≤
      4 * 2 ^ (j + 2) * ((j + 2).factorial : ℝ) ^ 2 * (ρ ^ (2 * j))⁻¹ *
        ∑ a : JetIndex2 M, factorialWeight ρ a.1.val * ‖realJetFourier M W a k‖ ^ 2 := by
  set c : ℝ := ‖realJetFourier M W (valueIndex2 M) k‖ with hc
  set F : ℝ := torusFrequencySq k with hF
  have hF0 : 0 ≤ F := by rw [hF]; unfold torusFrequencySq; positivity
  have hc0 : 0 ≤ c := norm_nonneg _
  have hA : ‖realJetFourier M W (⟨⟨j, by omega⟩, w⟩ : JetIndex2 M) k‖ ^ 2 ≤
      ((2 * Real.pi) ^ 2 * F) ^ j * c ^ 2 := by
    have hn : ‖realJetFourier M W (⟨⟨j, by omega⟩, w⟩ : JetIndex2 M) k‖ =
        (2 * Real.pi) ^ j * (∏ l : Fin j, |((k (w l) : ℤ) : ℝ)|) * c :=
      realJetFourier_word_norm M W j (by omega) w k
    have hprod : (∏ l : Fin j, |((k (w l) : ℤ) : ℝ)|) ^ 2 ≤ F ^ j := by
      rw [← Finset.prod_pow]
      calc ∏ l : Fin j, |((k (w l) : ℤ) : ℝ)| ^ 2 ≤ ∏ _l : Fin j, F :=
            by
              gcongr with l _
              rw [sq_abs]; exact sobolevScaled_sq_le_freq k (w l)
        _ = F ^ j := by simp
    calc _ = ((2 * Real.pi) ^ 2) ^ j * (∏ l : Fin j, |((k (w l) : ℤ) : ℝ)|) ^ 2 * c ^ 2 := by
          rw [hn, sobolevScaled_alg_a]
      _ ≤ ((2 * Real.pi) ^ 2) ^ j * F ^ j * c ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
      _ = _ := by rw [← mul_pow]
  obtain ⟨i, hi⟩ := sobolevScaled_exists_half k
  have hnJ : ‖realJetFourier M W (⟨⟨j + 2, by omega⟩, fun _ => i⟩ : JetIndex2 M) k‖ =
      (2 * Real.pi) ^ (j + 2) * (∏ _l : Fin (j + 2), |((k i : ℤ) : ℝ)|) * c :=
    realJetFourier_word_norm M W (j + 2) hj (fun _ => i) k
  have hJ : ((2 * Real.pi) ^ 2 * F / 2) ^ (j + 2) * c ^ 2 ≤
      ‖realJetFourier M W (⟨⟨j + 2, by omega⟩, fun _ => i⟩ : JetIndex2 M) k‖ ^ 2 := by
    rw [hnJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [sobolevScaled_alg_b, sq_abs, ← mul_pow]
    gcongr
    linarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (2 * Real.pi))]
  have hE : c ^ 2 + ρ ^ (2 * (j + 2)) / ((j + 2).factorial : ℝ) ^ 2 *
      (((2 * Real.pi) ^ 2 * F) / 2) ^ (j + 2) * c ^ 2 ≤
      ∑ a : JetIndex2 M, factorialWeight ρ a.1.val * ‖realJetFourier M W a k‖ ^ 2 := by
    have hne : (valueIndex2 M : JetIndex2 M) ≠ ⟨⟨j + 2, by omega⟩, fun _ => i⟩ := by
      intro h
      have := congrArg (fun a : JetIndex2 M => a.1.val) h
      simp [valueIndex2, valueIndex] at this
    have hsub : ({valueIndex2 M, ⟨⟨j + 2, by omega⟩, fun _ => i⟩} : Finset (JetIndex2 M)) ⊆
        Finset.univ := Finset.subset_univ _
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => mul_nonneg (factorialWeight_nonneg ρ _) (sq_nonneg _)))
    rw [Finset.sum_pair hne]
    have hv : factorialWeight ρ (valueIndex2 M).1.val = 1 := by
      simp [valueIndex2, valueIndex, factorialWeight]
    rw [hv, one_mul]
    have hw2 : factorialWeight ρ (j + 2) = ρ ^ (2 * (j + 2)) / ((j + 2).factorial : ℝ) ^ 2 := rfl
    have hfw : 0 ≤ ρ ^ (2 * (j + 2)) / ((j + 2).factorial : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hJ hfw
    show c ^ 2 + _ ≤ c ^ 2 + factorialWeight ρ (j + 2) * _
    rw [hw2]
    nlinarith
  exact sobolevScaled_pointwise ρ F c _ _ j hρ hF0 hA hE

/-- **Scaled sharp sup bound for a weak jet** (`h` a continuous periodic function equal a.e. on the
cell to the jet `⟨j, w⟩` of `W`, `j + 2 ≤ M`):
`h(x)² ≤ C_M ρ^{-(2j+2)} ‖W‖²_{ρ,M}`. -/
theorem sobolevScaledSup_jet_sq {M : ℕ} (W : TorusHk M ℝ) {j : ℕ} (hj : j + 2 ≤ M)
    (w : DerivativeWord2 j) (h : Vec 2 → ℝ) (hc : Continuous h) (hp : AVenhance.IsZ2Periodic h)
    (hae : h =ᵐ[volume.restrict AVenhance.unitCube]
      W.toFunction.jet (⟨⟨j, by omega⟩, w⟩ : JetIndex2 M))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (x : Vec 2) :
    (h x) ^ 2 ≤ sobolevScaledConst M * (ρ ^ (2 * j + 2))⁻¹ * factorialNormSq ρ W.val := by
  classical
  have hcont : Continuous (fun x => (h x : ℂ)) := Complex.continuous_ofReal.comp hc
  have hper : AVenhance.Infra.Torus.IsZdPeriodic (fun x => (h x : ℂ)) :=
    (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).mpr (fun n y => by simp only [hp n y])
  let Fk : (Fin 2 → ℤ) → ℝ := fun k =>
    ∑ a : JetIndex2 M, factorialWeight ρ a.1.val * ‖realJetFourier M W a k‖ ^ 2
  have hpar : HasSum Fk (factorialNormSq ρ W.val) := by
    have := torusJetFactorialParseval W ρ
    simpa only [Fk, sobolevScaled_realJetFourier_eq] using this
  set Bj : ℝ := 4 * 2 ^ (j + 2) * ((j + 2).factorial : ℝ) ^ 2 * (ρ ^ (2 * j))⁻¹ with hBj
  have hbound : ∀ k, sobolevProfileWeight ρ k *
      ‖AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (h x : ℂ)) k‖ ^ 2 ≤ Bj * Fk k := by
    intro k
    rw [sobolevScaled_coeff_eq W _ h hae k]
    exact sobolevScaled_freq_bound W hj w hρ k
  have hsumm : Summable (fun k => sobolevProfileWeight ρ k *
      ‖AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (h x : ℂ)) k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (sobolevProfileWeight_pos ρ k).le (sq_nonneg _)) hbound
      (hpar.summable.mul_left Bj)
  have hS : ∑' k, sobolevProfileWeight ρ k *
      ‖AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (h x : ℂ)) k‖ ^ 2 ≤
      Bj * factorialNormSq ρ W.val := by
    calc _ ≤ ∑' k, Bj * Fk k := hsumm.tsum_le_tsum hbound (hpar.summable.mul_left Bj)
      _ = _ := by rw [tsum_mul_left, hpar.tsum_eq]
  have hread := AVRegularity.External.torusFourierWeightedSupReadout hcont hper
    (sobolevProfileWeight ρ) (sobolevProfileWeight_pos ρ)
    (sobolevProfileWeight_inv_summable ρ hρ) hsumm.hasSum x
  have hA := sobolevProfileWeight_inv_tsum_le ρ hρ hρ1
  have hA0 : 0 ≤ ∑' k : Fin 2 → ℤ, (sobolevProfileWeight ρ k)⁻¹ :=
    tsum_nonneg fun k => (inv_pos.mpr (sobolevProfileWeight_pos ρ k)).le
  have hS0 : 0 ≤ ∑' k, sobolevProfileWeight ρ k *
      ‖AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (h x : ℂ)) k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sobolevProfileWeight_pos ρ k).le (sq_nonneg _)
  have hnorm : ‖(h x : ℂ)‖ = |h x| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hread
  have hsq : (h x) ^ 2 ≤ (∑' k : Fin 2 → ℤ, (sobolevProfileWeight ρ k)⁻¹) *
      (∑' k, sobolevProfileWeight ρ k *
        ‖AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (h x : ℂ)) k‖ ^ 2) := by
    rw [← sq_abs, ← Real.sq_sqrt hA0, ← Real.sq_sqrt hS0, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hread 2
  have hN := factorialNormSq_nonneg ρ W.val
  have hBj0 : 0 ≤ Bj := by rw [hBj]; positivity
  have hinv : (ρ ^ (2 * j + 2))⁻¹ = (ρ ^ (2 * j))⁻¹ * (ρ ^ 2)⁻¹ := by
    rw [pow_add, mul_inv]
  have h2 : (2 : ℝ) ^ (j + 2) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hj
  have h3 : ((j + 2).factorial : ℝ) ≤ (M.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hj
  have hC : 9 * Bj ≤ sobolevScaledConst M * (ρ ^ (2 * j))⁻¹ := by
    rw [hBj, sobolevScaledConst]
    have hpos : 0 ≤ (ρ ^ (2 * j))⁻¹ := by positivity
    have : 0 ≤ ((j + 2).factorial : ℝ) := Nat.cast_nonneg _
    have h4 : ((j + 2).factorial : ℝ) ^ 2 ≤ (M.factorial : ℝ) ^ 2 := pow_le_pow_left₀ this h3 2
    have h5 : (2 : ℝ) ^ (j + 2) * ((j + 2).factorial : ℝ) ^ 2 ≤ 2 ^ M * (M.factorial : ℝ) ^ 2 :=
      mul_le_mul h2 h4 (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right h5 hpos]
  calc (h x) ^ 2 ≤ _ := hsq
    _ ≤ (9 * (ρ ^ 2)⁻¹) * (Bj * factorialNormSq ρ W.val) :=
        mul_le_mul hA hS hS0 (by positivity)
    _ = ((ρ ^ 2)⁻¹ * (9 * Bj)) * factorialNormSq ρ W.val := by ring
    _ ≤ ((ρ ^ 2)⁻¹ * (sobolevScaledConst M * (ρ ^ (2 * j))⁻¹)) * factorialNormSq ρ W.val := by
        gcongr
    _ = _ := by rw [hinv]; ring

/-- **Scaled sharp sup bound for a classical representative** (the form used by the weak-entry
argument): `W ∈ H^{n+2}`, `a` a classical representative of order `n`, a word of length `j ≤ n`:
`(∂^w a (x))² ≤ C_{n+2} ρ^{-(2j+2)} ‖W‖²_{ρ,n+2}`. -/
theorem sobolevScaledSup_classical_sq {n : ℕ} (W : TorusHk (n + 2) ℝ) (a : Vec 2 → ℝ)
    (ha : IsClassicalRep W a n) {j : ℕ} (hj : j ≤ n) (w : DerivativeWord2 j)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (x : Vec 2) :
    (orderedDerivative w a x) ^ 2 ≤
      sobolevScaledConst (n + 2) * (ρ ^ (2 * j + 2))⁻¹ * factorialNormSq ρ W.val := by
  have hda : ContDiff ℝ ((j : ℕ) : ℕ∞) a := ha.2.1.of_le (by exact_mod_cast hj)
  have hc : Continuous (orderedDerivative w a) :=
    (Sampling.contDiff_orderedDerivative 0 w a (by simpa using hda)).continuous
  have hp : AVenhance.IsZ2Periodic (orderedDerivative w a) :=
    AVRegularity.CycleComparison.Lift.orderedDerivative_periodic w a hda ha.2.2.1
  have hae := ha.2.2.2 j hj w
  have hjet : torusJetOrder W j w = W.toFunction.jet (⟨⟨j, by omega⟩, w⟩ : JetIndex2 (n + 2)) := by
    funext y
    simp [torusJetOrder, show j ≤ n + 2 by omega]
  rw [hjet] at hae
  exact sobolevScaledSup_jet_sq W (by omega) w _ hc hp hae.symm hρ hρ1 x
end

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
open Finset AVRegularity.CycleComparison.Coarse
namespace AVRegularity.IterationPassage.Passage

/-! **The scale algebra of the discarded profiles** (exponents).

Abstract real lemmas: the scale sum `∑_{j ≤ K} E^{j-s} ρ^{-j-1} ≤ (K+1) C^{K+1} E^{-(1+s+c₁(K+1))}` when
`ρ ≥ C⁻¹ E^{1+c₁}`, and the two final inequalities (`D_E` and `D_e`) with exponents.
Special cases: `K = 0`; `E = 1`; `B = 0`. -/

/-- Monotonicity of `E^a` in the exponent for `0 < E ≤ 1`. -/
theorem discScale_exp_le {E a b : ℝ} (hE0 : 0 < E) (hE1 : E ≤ 1) (hab : b ≤ a) :
    E ^ a ≤ E ^ b :=
  Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hab

/-- One term of the scale sum. -/
theorem discScale_term {E ρ C c₁ s : ℝ} {j K : ℕ} (hE0 : 0 < E) (hE1 : E ≤ 1) (hC : 1 ≤ C)
    (hc₁ : 0 ≤ c₁) (hρ : C⁻¹ * E ^ (1 + c₁) ≤ ρ) (hj : j ≤ K) :
    E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) ≤ C ^ ((K : ℝ) + 1) * E ^ (-(1 + s + c₁ * ((K : ℝ) + 1))) := by
  have hC0 : 0 < C := by linarith
  have hb : 0 < C⁻¹ * E ^ (1 + c₁) := by positivity
  have hρ0 : 0 < ρ := lt_of_lt_of_le hb hρ
  have h1 : ρ ^ (-(j : ℝ) - 1) ≤ (C⁻¹ * E ^ (1 + c₁)) ^ (-(j : ℝ) - 1) :=
    Real.rpow_le_rpow_of_nonpos hb hρ (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have h2 : (C⁻¹ * E ^ (1 + c₁)) ^ (-(j : ℝ) - 1) =
      C ^ ((j : ℝ) + 1) * E ^ (-(1 + c₁) * ((j : ℝ) + 1)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hC0.le,
      ← Real.rpow_mul hE0.le]
    have : -(j : ℝ) - 1 = -((j : ℝ) + 1) := by ring
    rw [this, Real.rpow_neg hC0.le, inv_inv]
    ring_nf
  have h3 : C ^ ((j : ℝ) + 1) ≤ C ^ ((K : ℝ) + 1) := by
    exact Real.rpow_le_rpow_of_exponent_le hC (by
      have : (j : ℝ) ≤ K := by exact_mod_cast hj
      linarith)
  calc E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1)
      ≤ E ^ ((j : ℝ) - s) * (C ^ ((j : ℝ) + 1) * E ^ (-(1 + c₁) * ((j : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (h1.trans_eq h2) (by positivity)
    _ = C ^ ((j : ℝ) + 1) * E ^ (-(1 + s + c₁ * ((j : ℝ) + 1))) := by
        rw [mul_left_comm, ← Real.rpow_add hE0]
        congr 2
        ring
    _ ≤ C ^ ((K : ℝ) + 1) * E ^ (-(1 + s + c₁ * ((K : ℝ) + 1))) := by
        refine mul_le_mul h3 (discScale_exp_le hE0 hE1 ?_) (by positivity) (by positivity)
        have : (j : ℝ) ≤ K := by exact_mod_cast hj
        nlinarith

/-- The scale sum. -/
theorem discScale_sum {E ρ C c₁ s : ℝ} (K : ℕ) (hE0 : 0 < E) (hE1 : E ≤ 1) (hC : 1 ≤ C)
    (hc₁ : 0 ≤ c₁) (hρ : C⁻¹ * E ^ (1 + c₁) ≤ ρ) :
    ∑ j ∈ range (K + 1), E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) ≤
      ((K : ℝ) + 1) * C ^ ((K : ℝ) + 1) * E ^ (-(1 + s + c₁ * ((K : ℝ) + 1))) := by
  calc _ ≤ ∑ _j ∈ range (K + 1), C ^ ((K : ℝ) + 1) * E ^ (-(1 + s + c₁ * ((K : ℝ) + 1))) :=
        sum_le_sum fun j hj => discScale_term hE0 hE1 hC hc₁ hρ (Nat.lt_succ_iff.mp (mem_range.mp hj))
    _ = _ := by rw [sum_const, card_range]; simp; ring

/-- The final inequality for `D_E`. -/
theorem discScale_final_E {E CE μ Cμ CS Cm B Pe Z δ σL : ℝ} (hE0 : 0 < E) (hE1 : E ≤ 1)
    (hCE : 0 ≤ CE) (hμ : 0 ≤ μ) (hμb : μ ≤ Cμ * E ^ δ) (hCS : 0 ≤ CS)
    (hCm : 0 ≤ Cm) (hB : 0 ≤ B) (S : ℝ) (hS0 : 0 ≤ S) (hSb : S ≤ CS * E ^ (-Z))
    (hP : Pe ≤ δ - Z + σL) :
    CE * μ * S * (Cm * E ^ σL * B) ≤ (CE * Cμ * CS * Cm) * E ^ Pe * B := by
  have hCμ : 0 ≤ Cμ :=
    (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hE0 δ)).mp (hμ.trans hμb)
  have hexp : E ^ δ * E ^ (-Z) * E ^ σL = E ^ (δ - Z + σL) := by
    rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]; congr 1
  have hle : E ^ (δ - Z + σL) ≤ E ^ Pe := discScale_exp_le hE0 hE1 hP
  calc CE * μ * S * (Cm * E ^ σL * B) ≤ CE * (Cμ * E ^ δ) * (CS * E ^ (-Z)) * (Cm * E ^ σL * B) := by
        have h1 : CE * μ ≤ CE * (Cμ * E ^ δ) := mul_le_mul_of_nonneg_left hμb hCE
        have h2 : CE * μ * S ≤ CE * (Cμ * E ^ δ) * (CS * E ^ (-Z)) :=
          mul_le_mul h1 hSb hS0 (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (CE * Cμ * CS * Cm) * (E ^ δ * E ^ (-Z) * E ^ σL) * B := by ring
    _ ≤ (CE * Cμ * CS * Cm) * E ^ Pe * B := by
        rw [hexp]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hB

/-- The final inequality for `D_e`. -/
theorem discScale_final_e {E e ρ C s q Cd Cm B Pe σL : ℝ} (hE0 : 0 < E) (hE1 : E ≤ 1)
    (hC : 1 ≤ C) (hs : 0 < s) (hCd : 0 ≤ Cd) (hCm : 0 ≤ Cm) (hB : 0 ≤ B)
    (he : C⁻¹ * E ^ q ≤ e) (hρ : C⁻¹ * E ^ q ≤ ρ)
    (hP : Pe ≤ σL - q * (1 + s)) :
    Cd * e ^ (-s) * ρ⁻¹ * (Cm * E ^ σL * B) ≤ (Cd * C ^ (s + 1) * Cm) * E ^ Pe * B := by
  have hC0 : 0 < C := by linarith
  have hb : 0 < C⁻¹ * E ^ q := by positivity
  have he0 : 0 < e := lt_of_lt_of_le hb he
  have hρ0 : 0 < ρ := lt_of_lt_of_le hb hρ
  have h1 : e ^ (-s) ≤ (C⁻¹ * E ^ q) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hb he (by linarith)
  have h1' : (C⁻¹ * E ^ q) ^ (-s) = C ^ s * E ^ (-q * s) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hC0.le,
      ← Real.rpow_mul hE0.le, Real.rpow_neg hC0.le, inv_inv]
    ring_nf
  have h2 : ρ⁻¹ ≤ (C⁻¹ * E ^ q)⁻¹ := inv_anti₀ hb hρ
  have h2' : (C⁻¹ * E ^ q)⁻¹ = C * E ^ (-q) := by
    rw [mul_inv, inv_inv, Real.rpow_neg hE0.le]
  have hCs : C ^ s * C = C ^ (s + 1) := by
    rw [Real.rpow_add hC0, Real.rpow_one]
  have hexp : E ^ (-q * s) * E ^ (-q) * E ^ σL = E ^ (σL - q * (1 + s)) := by
    rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]; congr 1; ring
  have hle : E ^ (σL - q * (1 + s)) ≤ E ^ Pe := discScale_exp_le hE0 hE1 hP
  have h3 : e ^ (-s) * ρ⁻¹ ≤ (C ^ s * E ^ (-q * s)) * (C * E ^ (-q)) :=
    mul_le_mul (h1.trans_eq h1') (h2.trans_eq h2') (by positivity) (by positivity)
  calc Cd * e ^ (-s) * ρ⁻¹ * (Cm * E ^ σL * B) = Cd * (e ^ (-s) * ρ⁻¹) * (Cm * E ^ σL * B) := by ring
    _ ≤ Cd * ((C ^ s * E ^ (-q * s)) * (C * E ^ (-q))) * (Cm * E ^ σL * B) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCd) (by positivity)
    _ = (Cd * (C ^ s * C) * Cm) * (E ^ (-q * s) * E ^ (-q) * E ^ σL) * B := by ring
    _ ≤ (Cd * C ^ (s + 1) * Cm) * E ^ Pe * B := by
        rw [hCs, hexp]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hB

/-- The covariance constant `fbCovConst` is `O(E^δ)`: `cb ≤ 4 ε r²`, `r = ρ E^{σ₀}`,
`ε = C' E^{δ-2σ₀}`. -/
theorem discScale_mu {cb ρ R E δ σ₀ C' r ε : ℝ} (hρ : 0 < ρ) (hE : 0 < E)
    (hr : r = ρ * E ^ σ₀) (hε : ε = C' * E ^ (δ - 2 * σ₀)) (hcb : cb ≤ 4 * (ε * r ^ 2)) :
    cb * (R / ρ) ^ 2 ≤ (4 * C' * R ^ 2) * E ^ δ := by
  have h1 : E ^ (δ - 2 * σ₀) * (E ^ σ₀) ^ 2 = E ^ δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le, ← Real.rpow_add hE]
    congr 1; push_cast; ring
  have h2 : 4 * (ε * r ^ 2) * (R / ρ) ^ 2 = (4 * C' * R ^ 2) * (E ^ (δ - 2 * σ₀) * (E ^ σ₀) ^ 2) := by
    rw [hε, hr]; field_simp
  calc cb * (R / ρ) ^ 2 ≤ 4 * (ε * r ^ 2) * (R / ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcb (by positivity)
    _ = _ := by rw [h2, h1]

/-- `covBound` from the entries. -/
theorem discScale_covBound_le (H : Matrix (Fin 2) (Fin 2) ℝ) {x : ℝ} (h : ∀ i j, |H i j| ≤ x) :
    covBound H ≤ 4 * x := by
  simp only [covBound, Fin.sum_univ_two]
  linarith [h 0 0, h 0 1, h 1 0, h 1 1]

/-- `μ ≤ 1` from `μ ≤ Cμ E^δ` and the threshold. -/
theorem discScale_mu_one {μ Cμ x : ℝ} (hC : 0 < Cμ) (hμ : μ ≤ Cμ * x) (hx : x ≤ 1 / Cμ) :
    μ ≤ 1 := by
  calc μ ≤ Cμ * x := hμ
    _ ≤ Cμ * (1 / Cμ) := mul_le_mul_of_nonneg_left hx hC.le
    _ = 1 := by field_simp

/-- The ratio `(r/ρ)^L = E^{σ₀ L}`. -/
theorem discScale_ratio {r ρ E σ₀ : ℝ} (L : ℕ) (hρ : 0 < ρ) (hE : 0 < E) (hr : r = ρ * E ^ σ₀) :
    (r / ρ) ^ L = E ^ (σ₀ * L) := by
  rw [hr, mul_div_cancel_left₀ _ hρ.ne', ← Real.rpow_natCast, ← Real.rpow_mul hE.le]

/-- Positivity of `ρ` from a lower bound. -/
theorem discScale_pos {C E c ρ : ℝ} (hC : 0 < C) (hE : 0 < E) (hρ : C⁻¹ * E ^ c ≤ ρ) : 0 < ρ :=
  lt_of_lt_of_le (by positivity) hρ

/-- Combination of the two profile bounds. -/
theorem discScale_combine {E e ρ s q σL δ Pacc Z CE μ Cμ CS Cm1 Cm2 Cd Cs Cf B S wn1 wn2 : ℝ}
    {P2 P3 : ENNReal} (hE0 : 0 < E) (hE1 : E ≤ 1) (hs : 0 < s) (hCs : 1 ≤ Cs) (hCE : 0 ≤ CE)
    (hμ0 : 0 ≤ μ) (hμb : μ ≤ Cμ * E ^ δ) (hCS : 0 ≤ CS) (hCm1 : 0 ≤ Cm1) (hCm2 : 0 ≤ Cm2)
    (hCd : 0 ≤ Cd) (hB : 0 ≤ B) (hS0 : 0 ≤ S) (hSb : S ≤ CS * E ^ (-Z)) (hwn1 : 0 ≤ wn1)
    (hwn2 : 0 ≤ wn2) (hw1 : wn1 ≤ Cm1 * E ^ σL * B) (hw2 : wn2 ≤ Cm2 * E ^ σL * B)
    (he : Cs⁻¹ * E ^ q ≤ e) (hρ : Cs⁻¹ * E ^ q ≤ ρ) (hP1 : Pacc ≤ δ - Z + σL)
    (hP2 : Pacc ≤ σL - q * (1 + s)) (hCf : CE * Cμ * CS * Cm1 + Cd * Cs ^ (s + 1) * Cm2 ≤ Cf)
    (h2 : P2 ≤ ENNReal.ofReal (CE * μ * S * wn1))
    (h3 : P3 ≤ ENNReal.ofReal (Cd * e ^ (-s) * ρ⁻¹ * wn2)) :
    P2 + P3 ≤ ENNReal.ofReal (Cf * E ^ Pacc * B) := by
  have hCs0 : 0 < Cs := by linarith
  have hρ0 : 0 < ρ := discScale_pos hCs0 hE0 hρ
  have he0 : 0 < e := discScale_pos hCs0 hE0 he
  have hCμ : 0  ≤ Cμ :=
    (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hE0 δ)).mp (hμ0.trans hμb)
  have hX1 : CE * μ * S * wn1 ≤ (CE * Cμ * CS * Cm1) * E ^ Pacc * B :=
    (mul_le_mul_of_nonneg_left hw1 (by positivity)).trans
      (discScale_final_E hE0 hE1 hCE hμ0 hμb hCS hCm1 hB S hS0 hSb hP1)
  have hX2 : Cd * e ^ (-s) * ρ⁻¹ * wn2 ≤ (Cd * Cs ^ (s + 1) * Cm2) * E ^ Pacc * B :=
    (mul_le_mul_of_nonneg_left hw2 (by positivity)).trans
      (discScale_final_e hE0 hE1 hCs hs hCd hCm2 hB he hρ hP2)
  have hEB : 0 ≤ E ^ Pacc * B := by positivity
  have hn1 : 0 ≤ CE * μ * S * wn1 := by positivity
  have hn2 : 0 ≤ Cd * e ^ (-s) * ρ⁻¹ * wn2 := by positivity
  calc P2 + P3 ≤ ENNReal.ofReal (CE * μ * S * wn1) + ENNReal.ofReal (Cd * e ^ (-s) * ρ⁻¹ * wn2) :=
        add_le_add h2 h3
    _ = ENNReal.ofReal (CE * μ * S * wn1 + Cd * e ^ (-s) * ρ⁻¹ * wn2) :=
        (ENNReal.ofReal_add hn1 hn2).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (CE * Cμ * CS * Cm1) * E ^ Pacc * B + (Cd * Cs ^ (s + 1) * Cm2) * E ^ Pacc * B ≤
            Cf * E ^ Pacc * B := by
          have h := mul_le_mul_of_nonneg_right hCf hEB
          nlinarith [h]
        linarith

/-- A threshold for `E^δ` from a threshold for `E`. -/
theorem discScale_pow_thresh {E δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hE : 0 < E)
    (h : E ≤ c ^ (1 / δ)) : E ^ δ ≤ c := by
  calc E ^ δ ≤ (c ^ (1 / δ)) ^ δ := Real.rpow_le_rpow hE.le h hδ.le
    _ = c := by rw [← Real.rpow_mul hc.le]; field_simp; simp

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.IterationPassage.Passage

/-! **Classical factorial energy in normalized coordinates** (the `D_E` step of the discarded profiles).

* `discCoarse_orderedDerivative_compField_normSq`: `‖∂^w (compField π a) x‖² = ∑_v π_v⁻¹ (∂^w a_v x)²`.
* `discCoarse_energy_compField`: `∑_v π_v⁻¹ 𝓕(a_v) = 𝓕(compField π a)` for the classical factorial
  density `𝓕 = classicalFactorialSq ρ K`.
* `discCoarse_energy_clm_le`: `𝓕(L ∘ g) ≤ ‖L‖² 𝓕(g)`.

Special cases: `K = 0` (the `L²` norm); `L = 0`; one component. -/

open AVRegularity.ChartTransport

theorem discCoarse_contDiff_compField {S : Finset Comp} (π : CompIn S → ℝ) {n : ℕ∞}
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (ha : ∀ v, ContDiff ℝ n (fun x => a x v)) : ContDiff ℝ n (compField π a) := by
  refine (contDiff_piLp 2).2 fun v => ?_
  exact contDiff_const.mul (ha v)

theorem discCoarse_orderedDerivative_compField_coord {S : Finset Comp} (π : CompIn S → ℝ)
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) {j : ℕ} (w : DerivativeWord2 j)
    (ha : ∀ v, ContDiff ℝ (j : ℕ∞) (fun x => a x v)) (x : Vec 2) (v : CompIn S) :
    (orderedDerivative w (compField π a) x).ofLp v =
      (Real.sqrt (π v))⁻¹ * orderedDerivative w (fun y => a y v) x := by
  have hc := discCoarse_contDiff_compField π a ha
  let R : CompSpace S →L[ℝ] ℝ := PiLp.proj 2 (fun _ : CompIn S => ℝ) v
  have h1 := orderedDerivative_clm_comp (F := CompSpace S) (G := ℝ)
    R w (g := compField π a) hc
  have h2 := orderedDerivative_clm_comp (F := ℝ) (G := ℝ)
    ((Real.sqrt (π v))⁻¹ • (ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ)) w (g := fun y => a y v) (ha v)
  have h3 : (fun y : Vec 2 => R (compField π a y)) =
      fun y : Vec 2 => ((Real.sqrt (π v))⁻¹ • (ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ))
        (a y v) := by
    funext y; rfl
  rw [h3, h2] at h1
  exact (congrFun h1 x).symm

theorem discCoarse_orderedDerivative_compField_normSq {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) {j : ℕ} (w : DerivativeWord2 j)
    (ha : ∀ v, ContDiff ℝ (j : ℕ∞) (fun x => a x v)) (x : Vec 2) :
    ‖orderedDerivative w (compField π a) x‖ ^ 2 =
      ∑ v, (π v)⁻¹ * (orderedDerivative w (fun y => a y v) x) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.norm_eq_abs, sq_abs, discCoarse_orderedDerivative_compField_coord π a w ha x v,
    mul_pow, inv_pow]
  rw [Real.sq_sqrt (hπ v).le]

theorem discCoarse_enorm_sq {F : Type*} [NormedAddCommGroup F] (y : F) :
    ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem discCoarse_energy_compField {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (ρ : ℝ) (K : ℕ) (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (ha : ∀ v, ContDiff ℝ (K : ℕ∞) (fun x => a x v)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * classicalFactorialSq ρ K (fun x => a x v) =
      classicalFactorialSq ρ K (compField π a) := by
  classical
  unfold classicalFactorialSq
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have haj : ∀ v, ContDiff ℝ (j : ℕ∞) (fun x => a x v) := fun v =>
    (ha v).of_le (by exact_mod_cast hjK)
  have hmeas : ∀ (v : CompIn S) (w : DerivativeWord2 j),
      Measurable (fun x => ENNReal.ofReal (π v)⁻¹ * ‖orderedDerivative w (fun y => a y v) x‖ₑ ^ 2) :=
    fun v w => Measurable.const_mul
      (((continuous_orderedDerivative w (haj v)).enorm.measurable).pow_const 2) _
  have hw : ∀ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube,
      ‖orderedDerivative w (compField π a) x‖ₑ ^ 2 = ∑ v, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w (fun y => a y v) x‖ₑ ^ 2 := by
    intro w
    have hpt : ∀ x, ‖orderedDerivative w (compField π a) x‖ₑ ^ 2 =
        ∑ v, ENNReal.ofReal (π v)⁻¹ * ‖orderedDerivative w (fun y => a y v) x‖ₑ ^ 2 := by
      intro x
      rw [discCoarse_enorm_sq, discCoarse_orderedDerivative_compField_normSq π hπ a w haj x,
        ENNReal.ofReal_sum_of_nonneg (fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (sq_nonneg _))]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le), discCoarse_enorm_sq, Real.norm_eq_abs,
        sq_abs]
    simp_rw [hpt]
    rw [lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun v _ => ?_
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · exact fun v _ => hmeas v w
  simp_rw [hw, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => mul_left_comm _ _ _

/-- A continuous linear map multiplies the classical factorial density by at most `‖L‖²`. -/
theorem discCoarse_energy_clm_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (ρ : ℝ) (K : ℕ)
    {g : Vec 2 → F} (hg : ContDiff ℝ (K : ℕ∞) g) :
    classicalFactorialSq ρ K (fun x => L (g x)) ≤
      ENNReal.ofReal (‖L‖ ^ 2) * classicalFactorialSq ρ K g := by
  unfold classicalFactorialSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hgj : ContDiff ℝ (j : ℕ∞) g := hg.of_le (by exact_mod_cast hjK)
  rw [mul_left_comm (ENNReal.ofReal (‖L‖ ^ 2))]
  refine mul_le_mul_right ?_ _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [orderedDerivative_clm_comp L w hgj, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [discCoarse_enorm_sq, discCoarse_enorm_sq, ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm _) 2

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Passage

/-! **Scaled Sobolev to profile: statement** (Lemma 13.3 of the paper).

`SobolevProfileStatement`: for every order `K` there is `C_K ≥ 0` such that, for a finite set of
components with positive masses `π`, a radius `0 < ρ ≤ 1`, a wavelength `λ > 0`, a family
`X v ∈ H^{K+2}` and a classical field `g` whose normalized field `F g = compField π g` is `C^K` and
periodic, with the value jet of `X v` almost everywhere equal to `g · v` on the unit cell:

`𝓘_{λ,K;s}(F g) ≤ C_K (∑_{j ≤ K} λ^{j-s} ρ^{-j-1}) ‖X‖_{ρ,K+2;π}`.

The weighted norm is `weightedNorm ρ π 1`: the `ℓ²`
sum over the components, with weights `π_v⁻¹`, of the factorial norms
`∑_{i ≤ K+2} ρ^{2i}/(i!)² ‖∇^i X_v‖²_{L²(cell)}` (`factorialNormSq`). The power `ρ^{-j-1}` is
the sharp one in dimension two; it is what the error profile, the discarded profiles
and the bottom bound of the cascade need.

Special cases. An empty family: `F g` is the zero function of the trivial space, `0 ≤ ·`. `X = 0`:
`g = 0` almost everywhere, hence `F g = 0` (continuous), `0 ≤ 0`. `g` constant `= c`:
`𝓘 = λ^{-s}‖F c‖`, the right side is at least `C_K λ^{-s} ρ^{-1} ‖F c‖` (the `L²` norm of a
constant on the unit cell is its norm), fine for `C_K ≥ 1` and `ρ ≤ 1`. `K = 0`: only the
amplitude, `‖F g‖_∞ ≤ C ρ^{-1}‖X‖_{ρ,2;π}`. `s` is any real number. Constant: `C_K` depends on `K`
only (not on the components, the masses, `ρ`, `λ`, `s`). -/

/-- **Scaled Sobolev to profile** (Fourier Cauchy-Schwarz in dimension two at the radius `ρ`). -/
def SobolevProfileStatement : Prop :=
  ∀ K : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧
    ∀ {S : Finset Comp} (π : CompIn S → ℝ), (∀ v, 0 < π v) →
    ∀ (ρ lam s : ℝ), 0 < ρ → ρ ≤ 1 → 0 < lam →
    ∀ (X : ∀ v : CompIn S, TorusHk (K + 2) (ScalarH v.1.root))
      (g : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root),
      ContDiff ℝ (K : ℕ) (compField π g) → IsZ2Periodic (compField π g) →
      (∀ v, (X v).toFunction.jet (valueIndex2 (K + 2)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => g x v) →
      profileNorm lam K s (compField π g) ≤
        ENNReal.ofReal (CK * (∑ j ∈ Finset.range (K + 1),
          lam ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1)) * weightedNorm ρ π (fun _ => 1) X)

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.IterationPassage.Passage

/-! **The covariance correction `P_p - I` on `H^k` carriers** (the `D_E` step of the discarded profiles).

The analogue of `amplitude_covariance_difference_le` (for `covPolyQ`) for `covPolyP` (coefficients
`1/l!`, no sign) and an arbitrary output order `Ko`: if `W` is the carrier of `P_p` applied to the
carrier `Z` of order `Ko + 2p`, then `|W - Z|_{ρ,Ko} <= p M |Z|_{ρ,Ko+2p}` when
`fbCovConst ρ H (Ko+2p) <= M <= 1`.
Special cases: `p = 0` (`W = Z`); `M = 0`. -/

open CycleComparison.Coarse Construction.Preservation.FullLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def discTailCoeff (l : ℕ) : ℝ := 1 / ((l + 1).factorial : ℝ)

def discTailConst (M : ℝ) (p : ℕ) : ℝ :=
  ∑ l ∈ Finset.range p, |discTailCoeff l| * M ^ (l + 1)

theorem discTailCoeff_abs_le (l : ℕ) : |discTailCoeff l| ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((l + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (l + 1)
  unfold discTailCoeff
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one (by linarith)).mpr h1

theorem discTailConst_le {M : ℝ} (hM : 0 ≤ M) (hM1 : M ≤ 1) (p : ℕ) :
    discTailConst M p ≤ p * M := by
  calc
    discTailConst M p ≤ ∑ l ∈ Finset.range p, M := by
      apply Finset.sum_le_sum
      intro l _
      exact (mul_le_of_le_one_left (pow_nonneg hM _) (discTailCoeff_abs_le l)).trans
        (by rw [pow_succ]; exact mul_le_of_le_one_left hM (pow_le_one₀ hM hM1))
    _ = p * M := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem covPolyP_eq_id_tail (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (ψ : Vec 2 → E) : covPolyP Hc p ψ = ψ +
      fun x => ∑ l ∈ Finset.range p, discTailCoeff l • ((covOperator Hc)^[l + 1] ψ) x := by
  funext x
  unfold covPolyP
  rw [Finset.sum_apply, Finset.sum_range_succ']
  simp only [Pi.smul_apply, Pi.add_apply, discTailCoeff, Function.iterate_zero, id_eq,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, one_div]
  abel

def discTailAdj (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p Kc : ℕ) :
    TorusAdj (fun ψ : Vec 2 → E => fun x =>
      ∑ l ∈ Finset.range p, discTailCoeff l • ((covOperator Hc)^[l + 1] ψ) x)
      (2 * p) 0 Kc (discTailConst (covBound Hc) p) :=
  (TorusAdj.sumMem (Finset.range p) (fun l hl =>
    ((TorusAdj.covIter (E := E) Hc le_rfl (l + 1) 0 Kc).liftOrder
      (by have := Finset.mem_range.mp hl; omega)).smul (discTailCoeff l)))
      |>.ofOp (by funext ψ x; simp only [Pi.smul_apply])

theorem discTailAdj_bound {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p Kc : ℕ) :
    (discTailAdj (E := E) Hc p Kc).FBound ρ (discTailConst (fbCovConst ρ Hc Kc) p) := by
  have h := TorusAdj.FBound.sumMem (Finset.range p) (fun l hl =>
    ((TorusAdj.FBound.covIter (E := E) hρ Hc le_rfl (l + 1) 0 Kc).liftOrder (m' := 2 * p)
      (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) _) (by have := Finset.mem_range.mp hl; omega)).smul
        (discTailCoeff l))
  exact TorusAdj.FBound.ofOp _ h

/-- The covariance correction costs at most `p*M` of the input norm, at any output order. -/
theorem disc_cov_difference_le {ρ M : ℝ} {p Ko : ℕ}
    (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : fbCovConst ρ Hc (Ko + 2 * p) ≤ M) (hM1 : M ≤ 1)
    (Z : TorusHk (Ko + 2 * p) E) (W : TorusHk Ko E) (hW : IsCovImage (covPolyP Hc p) Z W) :
    Real.sqrt (factorialNormSq ρ
      (W - truncateTorusHk (Nat.le_add_right Ko (2 * p)) Z).val) ≤
        p * M * Real.sqrt (factorialNormSq ρ Z.val) := by
  let A := discTailAdj (E := E) Hc p (Ko + 2 * p)
  let Z0 := truncateTorusHk (Nat.le_add_right Ko (2 * p)) Z
  have hA : IsCovImage (covPolyP Hc p) Z (Z0 + A.adj Ko le_rfl Z) := by
    intro ψ hψ hp
    change cellInner (CycleComparison.Coarse.tval (Z0 + A.adj Ko le_rfl Z)) ψ =
      cellInner (CycleComparison.Coarse.tval Z) (covPolyP Hc p ψ)
    rw [cellInner_tval_add _ _ hψ.continuous,
      A.ident Ko le_rfl Z ψ (hψ.of_le (by exact_mod_cast le_top)) hp]
    rw [show CycleComparison.Coarse.tval Z0 = CycleComparison.Coarse.tval Z from
      tval_truncateTorusHk _ Z]
    rw [covPolyP_eq_id_tail]
    exact (cellInner_add_right _ (integrable_tval_inner Z hψ.continuous)
      (integrable_tval_inner Z (A.continuous_apply
        (hψ.of_le (by exact_mod_cast le_top)) hp))).symm
  have he := covImage_unique (covPolyP Hc p) Z W _ hW hA
  have htail0 : 0 ≤ discTailConst (fbCovConst ρ Hc (Ko + 2 * p)) p :=
    Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (pow_nonneg (fbCovConst_nonneg hρ Hc _) _)
  have hb := (discTailAdj_bound (E := E) hρ Hc p (Ko + 2 * p)) Ko le_rfl Z
  have hconst : discTailConst (fbCovConst ρ Hc (Ko + 2 * p)) p ≤ p * M := by
    calc
      _ ≤ discTailConst M p := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fbCovConst_nonneg hρ Hc _) hM _) (abs_nonneg _)
      _ ≤ _ := discTailConst_le ((fbCovConst_nonneg hρ Hc _).trans hM) hM1 p
  rw [he]
  change Real.sqrt (factorialNormSq ρ ((Z0 + A.adj Ko le_rfl Z) - Z0).val) ≤ _
  rw [add_sub_cancel_left]
  exact hb.trans (mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _))

end AVRegularity.IterationPassage.Passage
end
end
