-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
public import AVRegularity.CycleWords.MixedWords.Discard.Pair
public import AVRegularity.CycleWords.MixedWords.Discard.BlochBridge
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The negative-smoothing bound: smoothing from a negative order

Double duality. For a test `g` with `⟨z, g⟩ ≤ N ‖z‖_{H^j}`, the adjoint curve `Ψ` from `g` on
`[a, t]` has `‖Ψ(m)‖ ≤ C τ^{-j/2} N` at `m = a + τ/2` (the homogeneous propagator bound applied to the forward curve from
`Ψ(m)`), and `Ψ(a) ∈ H^s` with norm `≤ C τ^{-s/2} ‖Ψ(m)‖` (the adjoint propagator bound). Then
`⟨u(t), g⟩ = ⟨u(a), Ψ(a)⟩ ≤ M ‖Ψ(a)‖_{H^s}`. -/

/-- The pairing of a homogeneous forward curve with an adjoint curve is constant in time. -/
theorem pair_const {r t : ℝ} (hrt : r ≤ t)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {U Ψv : ℝ → ComplexCellL2} {slice Ψs : ℝ → TorusHk 1 ℂ}
    (hU : CellWeakHilbertCurve r t U slice (fun s => cellDualDerivative
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb s (slice s) 0 0))
    (hΨ : CellWeakHilbertCurve r t Ψv Ψs (fun s =>
        -cellDualDerivative (cellAdjointCoefficients ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩)
          hG V (cellDrift_neg hv).1 (cellDrift_neg_bound hb) s (Ψs s) 0 0)) :
    inner ℝ (U r) (Ψv r) = inner ℝ (U t) (Ψv t) := by
  have hpair := cellWeakAdjointPairing_forced hrt
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb
    (S := fun _ => 0) (F := fun _ _ => 0) hU hΨ
  have hint : ∫ s in r..t, cellComplexSource (fun k => (θ k : ℂ)) 0 (fun _ => 0) (Ψs s) = 0 := by
    simp [cellComplexSource_zero]
  rw [hint, sub_eq_zero] at hpair
  have hre := congrArg Complex.re hpair
  rw [cellComplexPair_re, cellComplexPair_re] at hre
  exact hre.symm

/-- Halving the time scale costs a factor `2 ^ (j + s)`. -/
theorem pow_scale (j s : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (τ / 2) ^ (-(j : ℝ) / 2) * (τ / 2) ^ (-(s : ℝ) / 2) ≤
      2 ^ (j + s) * τ ^ (-((j + s : ℕ) : ℝ) / 2) := by
  have hτ' : 0 < τ / 2 := by positivity
  rw [← Real.rpow_add hτ']
  have he : -(j : ℝ) / 2 + -(s : ℝ) / 2 = -(((j + s : ℕ) : ℝ) / 2) := by push_cast; ring
  rw [he, div_eq_mul_inv, Real.mul_rpow hτ.le (by norm_num), Real.inv_rpow (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have h1 : (2 : ℝ) ^ (((j + s : ℕ) : ℝ) / 2) ≤ 2 ^ (j + s) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (0 : ℝ) ≤ ((j + s : ℕ) : ℝ) := by positivity
      linarith)
  have h2 : τ ^ (-(((j + s : ℕ) : ℝ) / 2)) = τ ^ (-((j + s : ℕ) : ℝ) / 2) := by
    congr 1; ring
  rw [h2]
  nlinarith [Real.rpow_nonneg hτ.le (-((j + s : ℕ) : ℝ) / 2)]

/-- The negative-smoothing bound. -/
theorem cellNegativeSmoothing : CellNegativeSmoothingStatement := by
  intro j s ρ hρ
  obtain ⟨C1, Q1, hC1, hK1⟩ := cellKernelHs j ρ 1 hρ le_rfl
  obtain ⟨C2, Q2, hC2, hK2⟩ := cellAdjointKernelHs s ρ 1 hρ le_rfl
  refine ⟨C1 * C2 * 2 ^ (j + s), Q1 + Q2, by positivity, ?_⟩
  intro a b L G hG v hv V hb θ hab hb1 hL hθ hsm hjet u slice hu M hM hMu τ hτ t ht hat
  set P : ℝ := 1 + L with hP
  have hP0 : 0 ≤ P := by linarith
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hτ1 : τ ≤ 1 := by linarith [ht.2]
  set τ' : ℝ := τ / 2 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'1 : τ' ≤ 1 := by linarith
  set m : ℝ := a + τ' with hm
  have hmt : m + τ' ≤ t := by linarith
  have ham : a ≤ m := by linarith
  have hmt' : m ≤ t := by linarith
  have hpow := pow_scale j s hτ
  have hat' : a ≤ t := by linarith
  refine mem_of_dual_bound (torusHkValueCLM (E := ℂ) (K := j)) (u t)
    (C1 * C2 * 2 ^ (j + s) * P ^ (Q1 + Q2) * τ ^ (-((j + s : ℕ) : ℝ) / 2) * M)
    (by positivity) ?_
  intro g N hN hg
  obtain ⟨Ψv, Ψs, hΨ, hΨt⟩ := adjointCurve_exists hat' (fun s _ => G s) hG hv V hb
    (fun k => (θ k : ℂ)) g
  -- step A: `L²` size of the adjoint at the midpoint
  have hsubmt : Icc m t ⊆ Icc a t := Icc_subset_Icc ham le_rfl
  have hsubam : Icc a m ⊆ Icc a t := Icc_subset_Icc le_rfl hmt'
  obtain ⟨Um, slm, hUm, hUm0⟩ := forward_exists hmt' G hG hv V hb θ (Ψv m)
  have hk := hK1 m t L G hG hv V hb θ hmt' hL hθ (fun r hr => hsm r (hsub (hsubmt hr)))
    (fun l r hl hr x => hjet l r (by omega) (hsub (hsubmt hr)) x) (fun _ _ => 1)
    (plainKernel m t G hG hv V hb θ) Um slm hUm
  obtain ⟨z, hz, hzn⟩ := hk.2 τ' hτ'0 hτ'1 t ⟨hmt', le_rfl⟩ hmt
  have hc := pair_const hmt' G hG hv V hb θ hUm (hΨ.mono hsubmt)
  rw [hUm0, ← hz, hΨt] at hc
  have hsq : ‖Ψv m‖ ^ 2 ≤ N * (C1 * P ^ Q1 * τ' ^ (-(j : ℝ) / 2) * 1 * ‖Ψv m‖) := by
    have h1 : ‖Ψv m‖ ^ 2 = inner ℝ (Ψv m) (Ψv m) := (real_inner_self_eq_norm_sq _).symm
    rw [h1, hc]
    have := hg z
    rw [hUm0] at hzn
    calc inner ℝ (torusHkValueCLM z) g ≤ N * ‖z‖ := hg z
      _ ≤ _ := mul_le_mul_of_nonneg_left hzn hN
  have hmid : ‖Ψv m‖ ≤ N * (C1 * P ^ Q1 * τ' ^ (-(j : ℝ) / 2) * 1) := by
    rcases (norm_nonneg (Ψv m)).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [hsq]
  -- step B: smoothing of the adjoint on the first half
  obtain ⟨w', hw', hw'n⟩ := (hK2 a m L G hG hv V hb θ ham hL hθ
    (fun r hr => hsm r (hsub (hsubam hr)))
    (fun l r hl hr x => hjet l r (by omega) (hsub (hsubam hr)) x) (fun _ _ => 1)
    (plainKernel a m G hG hv V hb θ) Ψv Ψs (hΨ.mono hsubam)).2 τ' hτ'0 hτ'1 a
    ⟨le_rfl, ham⟩ (le_of_eq hm.symm)
  -- step C: the pairing with the datum
  have hc2 := pair_const hat' G hG hv V hb θ (hu.mono hsub) hΨ
  rw [hΨt] at hc2
  have hdat : inner ℝ (u a) (Ψv a) ≤ M * ‖w'‖ := by
    rw [← hw', ← cellComplexPair_re]
    exact (Complex.re_le_norm _).trans (hMu w')
  have hP1 : 0 ≤ C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) * 1 := by positivity
  have hX : 0 ≤ τ' ^ (-(j : ℝ) / 2) * τ' ^ (-(s : ℝ) / 2) := by positivity
  have hchain : inner ℝ (u t) g ≤
      (M * C1 * C2 * P ^ Q1 * P ^ Q2 * N) * (τ' ^ (-(j : ℝ) / 2) * τ' ^ (-(s : ℝ) / 2)) := by
    rw [← hc2]
    calc inner ℝ (u a) (Ψv a) ≤ M * ‖w'‖ := hdat
      _ ≤ M * (C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) * 1 * ‖Ψv m‖) :=
          mul_le_mul_of_nonneg_left hw'n hM
      _ ≤ M * (C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) * 1 *
            (N * (C1 * P ^ Q1 * τ' ^ (-(j : ℝ) / 2) * 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmid hP1) hM
      _ = _ := by ring
  have hpos : 0 ≤ M * C1 * C2 * P ^ Q1 * P ^ Q2 * N := by positivity
  calc inner ℝ (u t) g ≤ _ := hchain
    _ ≤ (M * C1 * C2 * P ^ Q1 * P ^ Q2 * N) * (2 ^ (j + s) * τ ^ (-((j + s : ℕ) : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hpow hpos
    _ = _ := by rw [pow_add P Q1 Q2]; ring

/-! # The negative-smoothing bound for families (`CellNegativeSmoothingFamilyStatement`)

Double duality for a family of tests `g_i` with per-curve dual norms `N_i`: adjoint curves `Ψ_i`
from each `g_i`; `‖Ψ_i(m)‖ ≤ C τ^{-j_i/2} N_i` (homogeneous propagator bound), `Ψ_i(a) = ι w'_i` with
`‖w'_i‖ ≤ C τ^{-s/2} ‖Ψ_i(m)‖` (adjoint propagator bound); the family bound on the data is applied once to `(w'_i)`.
The constants are uniform in `j_i ≤ jmax` and independent of the family. -/

/-- The negative-smoothing bound for families. -/
theorem cellNegativeSmoothingFamily : CellNegativeSmoothingFamilyStatement := by
  intro jmax s ρ hρ
  choose C1f Q1f hC1f hK1 using fun j : ℕ => cellKernelHs j ρ 1 hρ le_rfl
  obtain ⟨C1, Q1, hC1, hC1Q⟩ := uniform_const jmax C1f Q1f hC1f
  obtain ⟨C2, Q2, hC2, hK2⟩ := cellAdjointKernelHs s ρ 1 hρ le_rfl
  refine ⟨C1 * C2 * 2 ^ (jmax + s), Q1 + Q2, by positivity, ?_⟩
  intro a b L G hG v hv V hb θ hab hb1 hL hθ hsm hjet I _ j hj u slice hu M hM hMu τ hτ t ht hat
  set P : ℝ := 1 + L with hP
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hτ1 : τ ≤ 1 := by linarith [ht.2]
  set τ' : ℝ := τ / 2 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'1 : τ' ≤ 1 := by linarith
  set m : ℝ := a + τ' with hm
  have hmt : m + τ' ≤ t := by linarith
  have ham : a ≤ m := by linarith
  have hmt' : m ≤ t := by linarith
  have hpow := pow_scale jmax s hτ
  have hat' : a ≤ t := by linarith
  have hsubmt : Icc m t ⊆ Icc a t := Icc_subset_Icc ham le_rfl
  have hsubam : Icc a m ⊆ Icc a t := Icc_subset_Icc le_rfl hmt'
  set K : ℝ := C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) * (C1 * P ^ Q1 * τ' ^ (-(jmax : ℝ) / 2))
    with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine mem_of_family_dual_bound (fun i => torusHkValueCLM (E := ℂ) (K := j i))
    (fun i => u i t)
    (C1 * C2 * 2 ^ (jmax + s) * P ^ (Q1 + Q2) * τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M)
    (by positivity) ?_
  intro g N hN hg
  have hcurve : ∀ i, ∃ w' : TorusHk s ℂ, inner ℝ (u i t) (g i) =
      inner ℝ (u i a) (torusHkValueCLM w') ∧ ‖w'‖ ≤ K * N i := by
    intro i
    obtain ⟨Ψv, Ψs, hΨ, hΨt⟩ := adjointCurve_exists hat' (fun s _ => G s) hG hv V hb
      (fun k => (θ k : ℂ)) (g i)
    obtain ⟨Um, slm, hUm, hUm0⟩ := forward_exists hmt' G hG hv V hb θ (Ψv m)
    have hk := hK1 (j i) m t L G hG hv V hb θ hmt' hL hθ
      (fun r hr => hsm r (hsub (hsubmt hr)))
      (fun l r hl hr x => hjet l r (by have := hj i; omega) (hsub (hsubmt hr)) x) (fun _ _ => 1)
      (plainKernel m t G hG hv V hb θ) Um slm hUm
    obtain ⟨z, hz, hzn⟩ := hk.2 τ' hτ'0 hτ'1 t ⟨hmt', le_rfl⟩ hmt
    have hc := pair_const hmt' G hG hv V hb θ hUm (hΨ.mono hsubmt)
    rw [hUm0, ← hz, hΨt] at hc
    have hNi := hN i
    have hgi : ∀ z : TorusHk (j i) ℂ, inner ℝ (torusHkValueCLM z) (g i) ≤ N i * ‖z‖ := hg i
    have hsq : ‖Ψv m‖ ^ 2 ≤ N i * (C1f (j i) * P ^ Q1f (j i) * τ' ^ (-((j i : ℕ) : ℝ) / 2) * 1 *
        ‖Ψv m‖) := by
      have h1 : ‖Ψv m‖ ^ 2 = inner ℝ (Ψv m) (Ψv m) := (real_inner_self_eq_norm_sq _).symm
      rw [h1, hc]
      rw [hUm0] at hzn
      calc inner ℝ (torusHkValueCLM z) (g i) ≤ N i * ‖z‖ := hgi z
        _ ≤ _ := mul_le_mul_of_nonneg_left hzn hNi
    have hmid0 : ‖Ψv m‖ ≤ N i * (C1f (j i) * P ^ Q1f (j i) * τ' ^ (-((j i : ℕ) : ℝ) / 2) * 1) := by
      rcases (norm_nonneg (Ψv m)).eq_or_lt with h0 | hpos
      · rw [← h0]; have := hC1f (j i); positivity
      · refine le_of_mul_le_mul_right ?_ hpos
        nlinarith [hsq]
    have hexp : τ' ^ (-((j i : ℕ) : ℝ) / 2) ≤ τ' ^ (-(jmax : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hτ'0 hτ'1 (by
        have : ((j i : ℕ) : ℝ) ≤ (jmax : ℝ) := by exact_mod_cast hj i
        linarith)
    have hCP : C1f (j i) * P ^ Q1f (j i) ≤ C1 * P ^ Q1 := hC1Q P hP1 (j i) (hj i)
    have hmid : ‖Ψv m‖ ≤ N i * (C1 * P ^ Q1 * τ' ^ (-(jmax : ℝ) / 2)) := by
      refine hmid0.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hNi
      rw [mul_one]
      have := hC1f (j i)
      exact mul_le_mul hCP hexp (by positivity) (by positivity)
    obtain ⟨w', hw', hw'n⟩ := (hK2 a m L G hG hv V hb θ ham hL hθ
      (fun r hr => hsm r (hsub (hsubam hr)))
      (fun l r hl hr x => hjet l r (by have := hj i; omega) (hsub (hsubam hr)) x) (fun _ _ => 1)
      (plainKernel a m G hG hv V hb θ) Ψv Ψs (hΨ.mono hsubam)).2 τ' hτ'0 hτ'1 a
      ⟨le_rfl, ham⟩ (le_of_eq hm.symm)
    have hc2 := pair_const hat' G hG hv V hb θ (hu i |>.mono hsub) hΨ
    rw [hΨt] at hc2
    refine ⟨w', ?_, ?_⟩
    · rw [hw']; exact hc2.symm
    · have hP2 : 0 ≤ C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) := by positivity
      calc ‖w'‖ ≤ C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) * 1 * ‖Ψv m‖ := hw'n
        _ ≤ C2 * P ^ Q2 * τ' ^ (-(s : ℝ) / 2) * (N i * (C1 * P ^ Q1 * τ' ^ (-(jmax : ℝ) / 2))) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hmid hP2
        _ = K * N i := by rw [hKdef]; ring
  choose w' hid hw'n using hcurve
  have hre : ∑ i, inner ℝ (u i t) (g i) =
      (∑ i, cellComplexPair (u i a) (torusHkValueCLM (w' i))).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hid i, cellComplexPair_re]
  have hsq : Real.sqrt (∑ i, ‖w' i‖ ^ 2) ≤ K * Real.sqrt (∑ i, N i ^ 2) := by
    have h1 : ∑ i, ‖w' i‖ ^ 2 ≤ K ^ 2 * ∑ i, N i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hw'n i) 2
    calc Real.sqrt (∑ i, ‖w' i‖ ^ 2) ≤ Real.sqrt (K ^ 2 * ∑ i, N i ^ 2) := Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0]
  have hscale : K ≤ C1 * C2 * 2 ^ (jmax + s) * P ^ (Q1 + Q2) * τ ^ (-((jmax + s : ℕ) : ℝ) / 2) := by
    have hpos : 0 ≤ C1 * C2 * P ^ Q1 * P ^ Q2 := by positivity
    calc K = (C1 * C2 * P ^ Q1 * P ^ Q2) * (τ' ^ (-(jmax : ℝ) / 2) * τ' ^ (-(s : ℝ) / 2)) := by
          rw [hKdef]; ring
      _ ≤ (C1 * C2 * P ^ Q1 * P ^ Q2) * (2 ^ (jmax + s) * τ ^ (-((jmax + s : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hpow hpos
      _ = _ := by rw [pow_add P Q1 Q2]; ring
  have hSq := Real.sqrt_nonneg (∑ i, N i ^ 2)
  calc ∑ i, inner ℝ (u i t) (g i) ≤ ‖∑ i, cellComplexPair (u i a) (torusHkValueCLM (w' i))‖ := by
        rw [hre]; exact Complex.re_le_norm _
    _ ≤ M * Real.sqrt (∑ i, ‖w' i‖ ^ 2) := hMu w'
    _ ≤ M * (K * Real.sqrt (∑ i, N i ^ 2)) := mul_le_mul_of_nonneg_left hsq hM
    _ ≤ M * ((C1 * C2 * 2 ^ (jmax + s) * P ^ (Q1 + Q2) * τ ^ (-((jmax + s : ℕ) : ℝ) / 2)) *
          Real.sqrt (∑ i, N i ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale hSq) hM
    _ = _ := by ring

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the cell mean of a stage as a pairing with a constant

* `cellFourierCoeff_zero`: the zero mode is the cell mean.
* `marksMean_pair_const`: `⟨W, c⟩ = c̄ · mean W` for the constant test in `H^j`.
* `marksMean_order_le`: if the stages of an order `k` satisfy the plain-pass inequality against all
  tests, their squared terminal means are at most `B² ‖W₀‖²`; summed over the `M` stage orders,
  the squared terminal means are at most `M B² ‖W₀‖²`. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The zero Fourier mode is the cell mean. -/
theorem cellFourierCoeff_zero (f : Vec 2 → ℂ) : cellFourierCoeff f 0 = cellMean f := by
  unfold cellFourierCoeff cellMean
  simp

/-- The pairing with the constant test in `H^j` is the conjugated constant times the mean. -/
theorem marksMean_pair_const (j : ℕ) (c : ℂ) (W : ComplexCellL2) :
    cellComplexPair W (torusHkValueCLM (torusConstantCarrier j c)) =
      star c * cellMean (W : Vec 2 → ℂ) := by
  rw [sharpMean_value_const]
  have hc : cellConstantCLM c = cellScalarCLM c (cellConstantCLM 1) := by
    rw [AVRegularity.CycleDamping.cellScalar_constant, mul_one]
  rw [hc, cellComplexPair_scalar_right, cellComplexPair_one]

/-- The squared norm of a cell `L²` class as a lower integral. -/
theorem marksMean_ofReal_norm_sq (W : ComplexCellL2) :
    ENNReal.ofReal (‖W‖ ^ 2) = ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal (‖(W : Vec 2 → ℂ) z‖ ^ 2) := by
  have h := cellL2Norm_sq_eq_lintegral (f := (W : Vec 2 → ℂ)) (Lp.aestronglyMeasurable W)
  have hn : cellL2Norm (W : Vec 2 → ℂ) = ENNReal.ofReal ‖W‖ := by
    unfold cellL2Norm
    rw [ofReal_norm, Lp.enorm_def]
  rw [hn, ← ENNReal.ofReal_pow (norm_nonneg _)] at h
  rw [h]
  refine lintegral_congr fun z => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

section Mean

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- One stage order: testing the terminal means of the order against their own constants. -/
theorem marksMean_order_le (T : B1WIndex ι h Nw m Ks → ℝ) (hT : ∀ i, 0 ≤ T i)
    (W W₀ : B1WIndex ι h Nw m Ks → ComplexCellL2) (p : B1WIndex ι h Nw m Ks → ℂ)
    (hp : ∀ i, cellMean (W i : Vec 2 → ℂ) = p i) (term : B1WIndex ι h Nw m Ks → Prop)
    [DecidablePred term] (hTd : ∀ i, T i = if term i then ‖p i‖ ^ 2 else 0)
    (k j : ℕ) {B : ℝ}
    (hP : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk j ℂ,
      ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
        B * Real.sqrt (∑ i, ‖W₀ i‖ ^ 2) *
          Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) :
    ∑ i ∈ stageSet b1wSt k, T i ≤ B ^ 2 * ∑ i, ‖W₀ i‖ ^ 2 := by
  classical
  set R := ∑ i, ‖W₀ i‖ ^ 2 with hR
  set S := ∑ i ∈ stageSet b1wSt k, T i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hT i
  let c : B1WIndex ι h Nw m Ks → ℂ := fun i => if term i then p i else 0
  have hcn : ∀ i, ‖c i‖ ^ 2 = T i := by
    intro i
    rw [hTd i]
    by_cases hi : term i <;> simp [c, hi]
  have hpair : ∀ i, cellComplexPair (W i)
      (torusHkValueCLM (torusConstantCarrier j (c i))) = ((T i : ℝ) : ℂ) := by
    intro i
    rw [marksMean_pair_const, hp i, ← hcn i]
    by_cases hi : term i
    · simp [c, hi, Complex.conj_mul']
    · simp [c, hi]
  have h1 := hP (fun i => torusConstantCarrier j (c i))
  simp only [hpair, sharpMean_const_norm, hcn] at h1
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hS0] at h1
  by_cases hS' : S = 0
  · rw [hS']; positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS')
    have h2 : Real.sqrt S ≤ B * Real.sqrt R := by
      have : S ≤ B * Real.sqrt R * Real.sqrt S := h1
      have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
      have : S = Real.sqrt S * Real.sqrt S := (Real.mul_self_sqrt hS0).symm
      nlinarith
    have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rw [Real.sq_sqrt hS0, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h3
    exact h3

/-- The squared terminal means of a frame from the plain-pass inequality against all tests. -/
theorem marksMean_frame_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (W₀ W : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (hW₀ : IsScaledStage F θ F.a W₀) (hW : IsScaledStage F θ F.b W)
    (L : ℕ → ℕ) {B : ℝ}
    (hP : ∀ (k : ℕ) (ψ : B1WIndex ι h Nw m Ks → TorusHk (L k) ℂ),
      ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
        B * Real.sqrt (∑ i, ‖W₀ i‖ ^ 2) *
          Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) :
    stageTerminalMeanSq F m Ks θ ≤
      ENNReal.ofReal (↑(b1wM Nw m Ks) * B ^ 2) * stageDatumSq F m Ks θ := by
  classical
  set R := ∑ i, ‖W₀ i‖ ^ 2 with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdat : stageDatumSq F m Ks θ = ENNReal.ofReal R := by
    unfold stageDatumSq
    rw [hR, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [marksMean_ofReal_norm_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [hW₀ i] with z hz
    rw [hz]
  set p : B1WIndex ι h Nw m Ks → ℂ := fun i => cellMean (W i : Vec 2 → ℂ) with hp
  set T : B1WIndex ι h Nw m Ks → ℝ :=
    fun i => if i.1 = Fin.last Nw then ‖p i‖ ^ 2 else 0 with hT
  have hT0 : ∀ i, 0 ≤ T i := fun i => by
    by_cases hi : i.1 = Fin.last Nw <;> simp [hT, hi]
  have hcoef : ∀ i, cellFourierCoeff (stageScaled F θ i F.b) 0 = p i := by
    intro i
    rw [cellFourierCoeff_zero, hp]
    unfold cellMean
    exact integral_congr_ae ((hW i).mono fun z hz => hz.symm)
  have hmean : stageTerminalMeanSq F m Ks θ = ENNReal.ofReal (∑ i, T i) := by
    unfold stageTerminalMeanSq
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hT0 i]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.1 = Fin.last Nw
    · simp only [hi, ite_true, hT, hcoef]
    · simp [hi, hT]
  have hsplit : ∑ i, T i = ∑ k ∈ Finset.range (b1wM Nw m Ks), ∑ i ∈ stageSet b1wSt k, T i := by
    unfold stageSet
    exact (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (b1wM Nw m Ks))
      (g := b1wSt) (fun i _ => Finset.mem_range.2 (b1wSt_lt i)) T).symm
  have hk : ∀ k, ∑ i ∈ stageSet b1wSt k, T i ≤ B ^ 2 * R := fun k =>
    marksMean_order_le T hT0 W W₀ p (fun i => rfl) (fun i => i.1 = Fin.last Nw)
      (fun i => rfl) k (L k) (hP k)
  have hsum : ∑ i, T i ≤ ↑(b1wM Nw m Ks) * B ^ 2 * R := by
    rw [hsplit]
    calc _ ≤ ∑ k ∈ Finset.range (b1wM Nw m Ks), B ^ 2 * R := Finset.sum_le_sum fun k _ => hk k
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [hmean, hdat, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Mean

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the output means are the terminal stage means

For the endpoint `U x = planeValue (u_{N_w, x}(b))` of a frame whose word has `Θ_w ≠ 0`, the
output quantity `outMeanSq` of the band output statement is `Θ_w²` times the squared cell means of
the terminal stages: the scale of a terminal stage is `π_x^{-1/2} ϖ^{|β|}/β! · A_{N_w}⁻¹` and
`A_{N_w} = Θ_w`. -/

universe u v

theorem cellFourierCoeff_const_mul (c : ℂ) (g : Vec 2 → ℂ) (n : Fin 2 → ℤ) :
    cellFourierCoeff (fun y => c * g y) n = c * cellFourierCoeff g n := by
  unfold cellFourierCoeff
  simp only [mul_assoc]
  exact integral_const_mul _ _

theorem rpow_neg_half_sq_eq (p : ℝ) (hp : 0 < p) : (p ^ (-(1 / 2 : ℝ))) ^ 2 = p⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num
  exact Real.rpow_neg_one p

theorem b1wLevelMoments_last {Nw : ℕ} (m : ℕ) (Ks : Fin Nw → ℕ) :
    b1wLevelMoments m Ks (Fin.last Nw) = m := by
  unfold b1wLevelMoments
  have : ∀ l : Fin Nw, ¬ (Fin.last Nw).val ≤ l.val := fun l => by
    rw [Fin.val_last]; exact Nat.not_le.2 l.isLt
  simp

section Sum

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- One terminal stage: its squared scaled mean times `Θ_w²` is the output term. -/
theorem outMeanSq_term_eq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2) (hπ : ∀ x, 0 < F.π x) (hΘ : wordTheta F.ηg F.letters ≠ 0)
    (x : ι) (β : ℕ × ℕ) (hβ : β ∈ momentIndices (b1wLevelMoments m Ks (Fin.last Nw)))
    (e : Fin (Module.finrank ℝ (h x))) :
    ENNReal.ofReal (wordTheta F.ηg F.letters ^ 2) *
        ENNReal.ofReal (‖cellFourierCoeff (stageScaled F θ
          (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks) F.b) 0‖ ^ 2) =
      ENNReal.ofReal ((F.π x)⁻¹ *
        (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 *
        ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e)
            (planeValue (F.u (Fin.last Nw) x F.b) y))) 0‖ ^ 2) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hs : stageScaled F θ (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks) F.b =
      fun y => b1wScale F.π F.ϖ F.ηg F.letters (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks)
          * planeBlochC θ (fun y => momentWeight β y * inner ℝ (stdOrthonormalBasis ℝ (h x) e)
            (planeValue (F.u (Fin.last Nw) x F.b) y)) y := rfl
  rw [hs, cellFourierCoeff_const_mul, norm_mul, mul_pow]
  have hA : b1wAmp F.ηg F.letters (Fin.last Nw) = wordTheta F.ηg F.letters :=
    b1wAmp_last F.ηg F.letters
  have hsc : ‖b1wScale F.π F.ϖ F.ηg F.letters
      (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks)‖ ^ 2 =
      (F.π x)⁻¹ * (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 *
        (wordTheta F.ηg F.letters)⁻¹ ^ 2 := by
    unfold b1wScale
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    change ((F.π x ^ (-(1 / 2 : ℝ)) * F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
      (b1wAmp F.ηg F.letters (Fin.last Nw))⁻¹)) ^ 2 = _
    rw [hA, mul_pow, div_pow, mul_pow, rpow_neg_half_sq_eq _ (hπ x), div_pow]
    ring
  rw [hsc]
  field_simp

/-- The output means over the terminal stages. -/
theorem outMeanSq_eq_terminal {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2) (hπ : ∀ x, 0 < F.π x) (hΘ : wordTheta F.ηg F.letters ≠ 0) :
    outMeanSq F.π F.ϖ m θ (fun x => planeValue (F.u (Fin.last Nw) x F.b)) =
      ENNReal.ofReal (wordTheta F.ηg F.letters ^ 2) * stageTerminalMeanSq F m Ks θ := by
  classical
  unfold stageTerminalMeanSq outMeanSq
  rw [Finset.mul_sum]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last Nw)]
  · simp only [ite_true]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hm := b1wLevelMoments_last m Ks
    have key : ∀ (βs : {β // β ∈ momentIndices (b1wLevelMoments m Ks (Fin.last Nw))})
        (e : Fin (Module.finrank ℝ (h x))), ENNReal.ofReal (wordTheta F.ηg F.letters ^ 2) *
          ENNReal.ofReal (‖cellFourierCoeff (stageScaled F θ
            (⟨Fin.last Nw, x, βs, e⟩ : B1WIndex ι h Nw m Ks) F.b) 0‖ ^ 2) =
          ENNReal.ofReal ((F.π x)⁻¹ *
            (F.ϖ ^ (βs.1.1 + βs.1.2) / ((βs.1.1.factorial * βs.1.2.factorial : ℕ) : ℝ)) ^ 2 *
            ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight βs.1 y *
              inner ℝ (stdOrthonormalBasis ℝ (h x) e)
                (planeValue (F.u (Fin.last Nw) x F.b) y))) 0‖ ^ 2) :=
      fun βs e => outMeanSq_term_eq F m Ks θ hπ hΘ x βs.1 βs.2 e
    rw [Finset.sum_congr rfl fun βs _ => Finset.sum_congr rfl fun e _ => key βs e]
    rw [Finset.sum_coe_sort (momentIndices (b1wLevelMoments m Ks (Fin.last Nw)))
      (fun β => ∑ e : Fin (Module.finrank ℝ (h x)), ENNReal.ofReal ((F.π x)⁻¹ *
        (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 *
        ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e)
            (planeValue (F.u (Fin.last Nw) x F.b) y))) 0‖ ^ 2))]
    rw [hm]
  · intro j _ hj
    simp [hj]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

end Sum

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # `StageSourceHsStatement` from the forward bounds

`stageSourceHs`: `FwdSameStatement`, `FwdLetterStatement` and
`H1DensityStatement` give `StageSourceHsStatement`. The proof follows the route of
`b1w_stage_representation` with the transposed families: the stage expansion (proved) pairs the
earlier stage values with the test transforms; the forward bounds represent the pairing by an
`H^{n(i)}` element, the ladder arithmetic of `S143Ladder` supplies the loss `1` or `d_l`, and
the `H^1` tests are reached from the smooth ones by density and continuity. -/

section
universe u v

/-- Change the order index of a periodic Sobolev element along an equality. -/
def CastHk {a b : ℕ} (hab : a = b) (x : TorusHk a ℂ) : TorusHk b ℂ := hab ▸ x

theorem CastHk_value {a b : ℕ} (hab : a = b) (x : TorusHk a ℂ) :
    torusHkValueCLM (CastHk hab x) = torusHkValueCLM x := by
  subst hab
  rfl

theorem CastHk_norm {a b : ℕ} (hab : a = b) (x : TorusHk a ℂ) :
    ‖CastHk hab x‖ = ‖x‖ := by
  subst hab
  rfl

theorem pair_cont (u : ComplexCellL2) : Continuous (cellComplexPair u) := by
  have hre : Continuous fun w => (cellComplexPair u w).re := by
    simp_rw [cellComplexPair_re]
    exact continuous_const.inner continuous_id
  have him : Continuous fun w => (cellComplexPair u w).im := by
    simp_rw [cellComplexPair_im]
    exact continuous_const.inner (cellScalarCLM Complex.I).continuous
  have hw : cellComplexPair u = fun w => ((cellComplexPair u w).re : ℂ) +
      ((cellComplexPair u w).im : ℂ) * Complex.I := by
    funext w
    exact (Complex.re_add_im _).symm
  rw [hw]
  exact (Complex.continuous_ofReal.comp hre).add
    ((Complex.continuous_ofReal.comp him).mul continuous_const)

theorem source_cont (θ : Fin 2 → ℂ) (S : ComplexCellL2) (Fl : Fin 2 → ComplexCellL2) :
    Continuous (cellComplexSource θ S Fl) := by
  unfold cellComplexSource
  refine ((pair_cont S).comp (torusHkValueCLM (K := 1) (E := ℂ)).continuous).sub ?_
  exact continuous_finsetSum _ fun j _ => (pair_cont (Fl j)).comp
    (cellShiftedDerivativeCLM (fun i => star (θ i)) j).continuous

theorem eq_of_dense (hD : H1DensityStatement) {A B : TorusHk 1 ℂ → ℂ}
    (hA : Continuous A) (hB : Continuous B)
    (hsm : ∀ (z : TorusHk 1 ℂ) (ψ : Vec 2 → ℂ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      AVenhance.IsZ2Periodic ψ →
      (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] ψ → A z = B z)
    (z : TorusHk 1 ℂ) : A z = B z := by
  obtain ⟨zs, hzs, hφ⟩ := hD z
  have h1 : Filter.Tendsto (fun N => A (zs N)) Filter.atTop (nhds (A z)) :=
    (hA.tendsto z).comp hzs
  have h2 : Filter.Tendsto (fun N => B (zs N)) Filter.atTop (nhds (B z)) :=
    (hB.tendsto z).comp hzs
  have h3 : ∀ N, A (zs N) = B (zs N) := fun N => by
    obtain ⟨φ, hc, hp, hv⟩ := hφ N
    exact hsm _ φ hc hp hv
  exact tendsto_nhds_unique h1 (h2.congr fun N => (h3 N).symm)

section Main

/-- The source bound for the stages, from the forward bounds. -/
theorem stageSourceHs (hS : FwdSameStatement.{u, v}) (hL : FwdLetterStatement.{u, v})
    (hD : H1DensityStatement) : StageSourceHsStatement.{u, v} := by
  classical
  intro K Nw D m Kf d Ks pos
  choose CS hCS0 hCS using fun n => hS K Nw D m d Ks Real.pi n
  choose CL hCL0 hCL using fun n => hL K Nw D m d Ks pos Real.pi n
  set top := Kf + ∑ l, d l + (m + ∑ l, Ks l) with htop
  set Bt := ∑ n ∈ Finset.range (top + 1), (CS n + CL n) with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun n _ => add_nonneg (hCS0 n) (hCL0 n)
  have hCB : ∀ n ≤ top, CS n + CL n ≤ Bt := fun n hn =>
    Finset.single_le_sum (f := fun n => CS n + CL n)
      (fun n _ => add_nonneg (hCS0 n) (hCL0 n)) (Finset.mem_range.2 (by omega))
  have hM1 : (1 : ℝ) ≤ b1wM Nw m Ks := by
    have : 1 ≤ b1wM Nw m Ks := by
      unfold b1wM
      exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    exact_mod_cast this
  refine ⟨(b1wM Nw m Ks : ℝ) * Bt, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hθ
  have hρ : ∀ k, |θ k| ≤ Real.pi := hθ
  have hJtop : ∀ n ≤ top, n + Finset.univ.sup d ≤ F.J := by
    intro n hn
    have := hJ
    unfold wordReserveKstar wordReserveN at this
    omega
  have hslow : ∀ l, (F.letters l).slow = Ks l := fun l => (hlet l).2.1
  have hsupeq : (Finset.univ.sup fun l => (F.letters l).order) = Finset.univ.sup d :=
    Finset.sup_congr rfl fun l _ => (hlet l).1
  have hord : ∀ l, (F.letters l).order ≤ F.J := fun l => by
    rw [(hlet l).1]
    have h1 : d l ≤ Finset.univ.sup d := Finset.le_sup (f := d) (Finset.mem_univ l)
    have := hJtop 0 (Nat.zero_le _)
    omega
  have hπ : ∀ x, 0 < F.π x := F.piece.hπ
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.2 (div_pos F.piece.hη (by linarith [F.piece.hS]))
  have hLetAE := ae_all_iff.2 fun n : Fin (top + 1) =>
    hCL n.val g₁ F θ hlet (hJtop n.val (by have := n.2; omega)) hρ
  have hExpAE := stageExpansion K g₁ F θ m Ks hslow hord letterBloch (amplitudeIdMoments K g₁ F)
  filter_upwards [hExpAE, hLetAE, ae_restrict_mem measurableSet_Icc] with r hExp hLet hrmem
  intro k X hX S Fl hS' hFl'
  have hExp' : ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ),
      ContDiff ℝ ((Finset.univ.sup d : ℕ) + 1) φ → AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y := by
    intro i φ h1 h2
    refine hExp i φ ?_ h2
    rw [hsupeq]
    exact h1
  by_cases hne : (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k).Nonempty
  swap
  · refine ⟨fun _ => 0, fun i hi => absurd ⟨i, hi⟩ hne, ?_⟩
    have : stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k = ∅ :=
      Finset.not_nonempty_iff_eq_empty.1 hne
    rw [this]
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨n0, hn0⟩ := stage_ladder (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks) Kf d k
  obtain ⟨i0, hi0⟩ := hne
  have hn0top : n0 ≤ top := by
    rw [← hn0 i0 hi0]
    exact ladder_le_top Kf d i0
  have hpairs : ∀ k' < k, LadderBody (m := m) (Ks := Ks) Kf d F θ r k k' n0 (CS n0 + CL n0)
      (Finset.univ.sup d) := fun k' hk' =>
    pair Kf d (Finset.univ.sup d) F θ r CS CL hCS0 hCL0 top
      (fun n k k' hs N hN => hCS n g₁ F θ hρ r hrmem k k' hs N hN)
      (fun n hn l k k' h1 h2 N hN => hLet ⟨n, by omega⟩ l k k' h1 h2 N hN) hk' hn0 hn0top
  obtain ⟨Y, hY1, hY2⟩ := combine Kf d (Finset.univ.sup d) F θ r k n0 (CS n0 + CL n0)
    hpairs X
  refine ⟨fun i => if hi : b1wSt i = k then
      CastHk (hn0 i (mem_stage.2 hi)).symm (Y i) else 0, ?_, ?_⟩
  · intro i hi z
    have hik : b1wSt i = k := mem_stage.1 hi
    have hσ : (torusHkValueCLM (if hi : b1wSt i = k then
        CastHk (hn0 i (mem_stage.2 hi)).symm (Y i) else 0) : ComplexCellL2) =
        torusHkValueCLM (Y i) := by
      rw [dite_eq_left_of_eq_true (eq_true hik), CastHk_value]
    rw [hσ]
    refine eq_of_dense hD (source_cont _ (S i) (Fl i))
      ((pair_cont _).comp (torusHkValueCLM (K := 1) (E := ℂ)).continuous) ?_ z
    intro z' ψ hψ hper hzψ
    have hX' : ∀ i', b1wSt i' < k → (torusHkValueCLM (X i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube]
        fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y :=
      fun i' hi' => hX i' hi'
    have hearly : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
        ∀ i', ¬ b1wSt i' < k → ∀ φ, b1wTestTransform F θ i i' r φ = 0 := by
      intro i2 hi2 i' hi' φ
      refine stageTransformEarlier K g₁ F θ m Ks hslow i2 i' ?_ r φ
      rwa [mem_stage.1 hi2]
    rw [smooth_source F θ r k hπ hϖ (fun i' => torusHkValueCLM (X i')) hX' S Fl hS' hFl'
      (Finset.univ.sup d) hExp' hearly hi z' ψ hψ hper hzψ]
    have hsψ : ContDiff ℝ ((Finset.univ.sup d : ℕ) + 1) (fun y => star (ψ y)) :=
      Complex.conjCLE.toContinuousLinearMap.contDiff.comp
        (hψ.of_le (by exact_mod_cast le_top))
    have hsper : AVenhance.IsZ2Periodic (fun y => star (ψ y)) := fun n x => by
      simp only [hper n x]
    rw [← hY1 i hi _ hsψ hsper]
    unfold cellComplexPair
    refine integral_congr_ae ?_
    filter_upwards [hzψ] with y hy
    simp only [hy]
  · have hsum : ∑ i ∈ stageSet b1wSt k, ‖(if hi : b1wSt i = k then
        CastHk (hn0 i (mem_stage.2 hi)).symm (Y i) else 0 : TorusHk _ ℂ)‖ ^ 2 =
        ∑ i ∈ stageSet b1wSt k, ‖Y i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [dite_eq_left_of_eq_true (eq_true (mem_stage.1 hi)), CastHk_norm]
    rw [hsum]
    refine hY2.trans ?_
    have hC : CS n0 + CL n0 ≤ Bt := hCB n0 hn0top
    have hC0 : 0 ≤ CS n0 + CL n0 := add_nonneg (hCS0 n0) (hCL0 n0)
    have hsq : (CS n0 + CL n0) ^ 2 ≤ Bt ^ 2 := pow_le_pow_left₀ hC0 hC 2
    have hX0 : 0 ≤ ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have : (b1wM Nw m Ks : ℝ) * (CS n0 + CL n0) ^ 2 ≤ ((b1wM Nw m Ks : ℝ) * Bt) ^ 2 := by
      rw [mul_pow]
      calc (b1wM Nw m Ks : ℝ) * (CS n0 + CL n0) ^ 2 ≤ (b1wM Nw m Ks : ℝ) * Bt ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
        _ ≤ (b1wM Nw m Ks : ℝ) ^ 2 * Bt ^ 2 :=
            mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    calc (b1wM Nw m Ks : ℝ) * (CS n0 + CL n0) ^ 2 *
          ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2
        ≤ ((b1wM Nw m Ks : ℝ) * Bt) ^ 2 *
          ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this hX0
      _ = _ := rfl

end Main
end

/-! # The forward letter bound from the block operators

`FwdLetterStatement` follows from `FwdLetterOpsStatement` by the Schur test over the pairs
`(component, moment)` (`fibre_schur`), exactly as `letterTransformBoundAEZone_of_ops` does for the
tests, with the roles of the stages `i` and `i'` exchanged: the weights are the same and their row
and column sums are bounded in both directions. Hence `stageSourceHs_of_ops`. -/

section
universe u v

open Classical in
theorem fwdLetter_of_ops (hO : FwdLetterOpsStatement.{u, v}) :
    FwdLetterStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  obtain ⟨C0, hC0, hC⟩ := hO K Nw D m d Ks pos ρ n
  have hcnt0 : 0 ≤ ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine ⟨C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ),
    mul_nonneg hC0 hcnt0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [hC g₁ F θ hlet hJ hρ] with r hr
  intro l k k' hk hk' N hnN X
  obtain ⟨A, hAv, hAb⟩ := hr l N hnN
  refine ⟨fun i => if i ∈ stageSet b1wSt k then ∑ i' ∈ stageSet b1wSt k', A i i' (X i') else 0,
    ?_, ?_⟩
  · intro i hi φ hφ hper
    simp only [hi, ↓reduceIte, map_sum]
    rw [int_sum _ _ _ hφ.continuous]
    exact Finset.sum_congr rfl fun i' hi' => hAv i i' (hk i hi) (hk' i' hi') (X i') φ hφ hper
  · have hL := F.piece.hlet l
    have key := fibre_schur (G := ι × (ℕ × ℕ)) b1wKey
      (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k')
      (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k)
      (fun i' i => A i i' (X i')) (fun i' => ‖X i'‖)
      (fun g g' => C0 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g'.2 g.2
        then 1 else 0) * letterCompWeight (F.letters l) g'.1 g.1)
      (fun g g' => mul_nonneg (mul_nonneg hC0 (by split_ifs <;> simp))
        (letterCompWeight_nonneg hL _ _))
      (A := C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ))
      (Bc := C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ))
      (fun g _ => by
        have h1 := letterMom_col (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g.2
          ((stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k).image b1wKey)
          (fun x => letterCompWeight (F.letters l) x g.1)
          (fun x => letterCompWeight_nonneg hL _ _)
        have h2 := letterCompWeight_col hL g.1
        calc _ = C0 * ∑ g' ∈ (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks))
                k).image b1wKey, (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1)
                g'.2 g.2 then 1 else 0) * letterCompWeight (F.letters l) g'.1 g.1 := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun g' _ => by ring
          _ ≤ C0 * (_ * 1) := mul_le_mul_of_nonneg_left
              (h1.trans (mul_le_mul_of_nonneg_left h2 hcnt0)) hC0
          _ = _ := by ring)
      (fun g' _ => by
        have h1 := letterMom_row (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g'.2
          ((stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k').image b1wKey)
          (letterCompWeight (F.letters l) g'.1) (letterCompWeight_nonneg hL _)
        have h2 := letterCompWeight_row hL g'.1
        calc _ = C0 * ∑ g ∈ (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks))
                k').image b1wKey, (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1)
                g'.2 g.2 then 1 else 0) * letterCompWeight (F.letters l) g'.1 g.1 := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun g _ => by ring
          _ ≤ C0 * (_ * 1) := mul_le_mul_of_nonneg_left
              (h1.trans (mul_le_mul_of_nonneg_left h2 hcnt0)) hC0
          _ = _ := by ring)
      (mul_nonneg hC0 hcnt0)
      (fun g hg g' hg' => by
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hg'
        refine hAb _ _ (b1wKey i₁).1 (b1wKey i₀).1 (b1wKey i₁).2 (b1wKey i₀).2
          (fun i hi => ⟨hk i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
          (fun i' hi' => ⟨hk' i' (Finset.mem_filter.1 hi').1, (Finset.mem_filter.1 hi').2⟩) X)
    calc _ = ∑ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
          ‖∑ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
            A i i' (X i')‖ ^ 2 :=
          Finset.sum_congr rfl fun i hi => by simp only [hi, ↓reduceIte]
      _ ≤ _ := key
      _ = _ := by ring

/-- The stage source bound from the pairwise forward operators. -/
theorem stageSourceHs_of_ops (hS : FwdSameOpsStatement.{u, v})
    (hL : FwdLetterOpsStatement.{u, v}) : StageSourceHsStatement.{u, v} :=
  stageSourceHs (fwdSame_of_ops hS) (fwdLetter_of_ops hL) h1Density
end

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # the plain pass on one frame

`plain_stage_frame`: on a frame, at a frequency `θ`, with the measurable fibre clause of the
words, the transform families of size `B` at almost every time, a kernel `κ` and adjoint curves
from `H^{s_k}` tests with `H^{s_k}` representatives of size `C_a κ(r,t)`, the stage curves `W_i`
(`b1w_stage_curves`) represent the scaled stage values at every time and satisfy the bound of
`plain_pass`. The stage expansion, the earlier-stage clause, letterBloch and the moments are the
proved theorems. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The ladder is at least its base. -/
theorem le_b1wLadderAt (Nw s₀ : ℕ) (d Ks : Fin Nw → ℕ) (k : ℕ) : s₀ ≤ b1wLadderAt Nw s₀ d Ks k := by
  unfold b1wLadderAt
  omega

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The plain pass on one frame.** -/
theorem plain_stage_frame {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (d : Fin Nw → ℕ) (s₀ : ℕ) (hs₀ : (Finset.univ.sup d) + 3 ≤ s₀)
    (hlet : ∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l)
    (hJ : Finset.univ.sup d ≤ F.J)
    (hM : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
      ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
        (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        MemLp (Function.uncurry src) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
        (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
        (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
          src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
          Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
        IsCellSolution (Icc F.a F.b)
          (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
        ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)))
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (κ : ℝ → ℝ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hκ : IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b A κ)
    (Ca : ℝ) (hCa : 0 ≤ Ca)
    (hadj : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b, ∀ ψ : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ)
        (U : ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        CellWeakHilbertCurve F.a t Ψv Ψs (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv t = torusHkValueCLM ψ ∧
        ∀ r ∈ Icc F.a t, torusHkValueCLM (U r) = Ψv r ∧ ‖U r‖ ≤ Ca * κ r t * ‖ψ‖) :
    ∃ Wc : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2,
      (∀ i, ∀ t ∈ Icc F.a F.b,
        (Wc i t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i t) ∧
      ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b,
        ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (Wc i t) (torusHkValueCLM (ψ i))‖ ≤
          plainConst Ca A B k * (1 + (t - F.a)) ^ k * κ F.a t *
            Real.sqrt (∑ i, ‖Wc i F.a‖ ^ 2) *
            Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
  classical
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨Dθ, src, Fl, hcur, hval, hlit, hmem, hsl⟩ := b1w_stage_curves F m Ks θ hM V hb
    (b1wScale F.π F.ϖ F.ηg F.letters)
  -- the stage expansion at almost every time
  have hord : ∀ l, (F.letters l).order ≤ F.J := fun l => by
    rw [(hlet l).1]
    exact (Finset.le_sup (f := d) (Finset.mem_univ l)).trans hJ
  have hsup : (Finset.univ.sup fun l => (F.letters l).order) = Finset.univ.sup d := by
    congr 1
    funext l
    exact (hlet l).1
  have hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ (Finset.univ.sup d + 1 : ℕ) φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y := by
    filter_upwards [stageExpansion K g₁ F θ m Ks (fun l => (hlet l).2) hord letterBloch
      (amplitudeIdMoments K g₁ F)] with r hr i φ hφ hper
    refine hr i φ ?_ hper
    rw [hsup]
    exact_mod_cast hφ
  -- the inputs of the abstract pass
  have hW := fun i => cellWeakHilbertCurve_shift (b1wCoeff_eq_real F θ) (hcur i)
  have hrep : ∀ k < b1wM Nw m Ks, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ)
        (ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        (∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) →
      ∃ Φ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖Φ k' i'‖ ^ 2) ≤
          B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) ∧
        ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun k => ((θ k : ℝ) : ℂ))
            (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
            (fun j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
              (cellSourceSlice (fun r z => Fl i r z j) r)) (z i) =
          ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
            cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
              (cellRawTrace (Dθ i') r)) (torusHkValueCLM (Φ k' i')) := by
    intro k _
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_all_iff.2 hlit, ae_all_iff.2 hsl, hexp,
      hprov] with r hr hl hs he hp z ψ hzψ
    have hgood := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hr) (fun i => hmem i r hr)
      (fun i => ⟨(hs i).1, (hl i).1, (hs i).2, (hl i).2⟩)
    have hN : Finset.univ.sup d + 1 + 2 ≤ b1wLadderAt Nw s₀ d Ks k :=
      (by omega : Finset.univ.sup d + 1 + 2 ≤ s₀).trans (le_b1wLadderAt Nw s₀ d Ks k)
    obtain ⟨UΦ, Φall, hUΦval, hUΦn, hsum⟩ := b1w_repr_crude_at F θ r k F.piece.hπ hϖ
      (b1wLadderAt Nw s₀ d Ks) (Finset.univ.sup d + 1) (b1wLadderAt Nw s₀ d Ks k) (by omega) hN
      (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) r))
      (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
      (fun i j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellSourceSlice (fun r z => Fl i r z j) r))
      (fun i _ => hgood.1 i) (fun i _ j => hgood.2.1 i j) (fun i _ φ hφ hper => he i φ hφ hper)
      (fun i hi i' hi' φ => stageTransformEarlier K g₁ F θ m Ks (fun l => (hlet l).2) i i'
        (by rw [(Finset.mem_filter.1 hi).2]; exact hi') r φ)
      (fun i' => hgood.2.2 i') B (fun ψ k' hk' => hp k k' hk' ψ) z ψ hzψ
    refine ⟨UΦ, fun k' hk' => ?_, ?_⟩
    · calc Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i'‖ ^ 2)
          ≤ Real.sqrt (B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) :=
            Real.sqrt_le_sqrt (hUΦn k' hk')
        _ = B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]
    · rw [hsum]
      refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
      rw [hUΦval k' (Finset.mem_range.1 hk') i' hi']
  have hadj' : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b,
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ (Ψv : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2)
        (Ψs : B1WIndex ι h Nw m Ks → ℝ → TorusHk 1 ℂ)
        (U : B1WIndex ι h Nw m Ks → ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        (∀ i, CellWeakHilbertCurve F.a t (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r
            (Ψs i r) 0 0)) ∧
        (∀ i, Ψv i t = torusHkValueCLM (ψ i)) ∧
        (∀ i, ∀ r ∈ Icc F.a t, torusHkValueCLM (U i r) = Ψv i r) ∧
        ∀ r ∈ Icc F.a t, Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r‖ ^ 2) ≤
          Ca * κ r t * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
    intro k hk t ht ψ
    choose Ψv Ψs U hΨ using fun i => hadj k hk t ht (ψ i)
    refine ⟨Ψv, Ψs, U, fun i => (hΨ i).1, fun i => (hΨ i).2.1,
      fun i r hr => ((hΨ i).2.2 r hr).1, fun r hr => ?_⟩
    exact sqrt_sum_sq_le_mul _ (fun i => ‖U i r‖) (fun i => ‖ψ i‖)
      (mul_nonneg hCa (hκ.pos r t).le) (fun i _ => norm_nonneg _)
      (fun i _ => ((hΨ i).2.2 r hr).2)
  refine ⟨fun i t => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t),
    fun i t ht => ?_, ?_⟩
  · filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellRawTrace (Dθ i) t), cellRawTrace_ae (Dθ i) t (hmem i t ht), hval i t ht]
      with y h1 h2 h3
    rw [h1, h2, h3]
    rfl
  · exact plain_pass b1wSt (b1wLadderAt Nw s₀ d Ks) (b1wM Nw m Ks)
      ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩ F.piece.hGm V F.piece.hv hb _ _ _ _ hW
      κ A Ca B (fun r t => (hκ.pos r t).le)
      (fun r t h1 h2 h3 => hκ.mul_le F.a r t le_rfl h1 h2 h3) hA hCa hB hadj' hrep

end Frame

end AVRegularity.CycleWords.Discard
end
