-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.FluxFastDiscrepancy
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseChartIndex
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.CycleWords.CellTransitionGeometry
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleComparison.LiftSetting

/-! The scale fields of the lift setting of an observed pulse:
the lift window is nonempty, the scales `e = ε_m`, `E = ε_{m-1}`, `ν`, `B`, `ρ = √(Bτ_m'')` are
positive, `d_* = ℓ√B`, and `ε_c = d_*/ρ ≤ 1`, `λ_s = ρ/E ≤ 1`, `η = ν/B ≤ 1`.

The statements are phrased for the explicit expressions of `pulseLiftData` and of the conclusion
of `cycle_comparison`, with the window `[tA, tZ]` of the cover (`tA = t_p`, `tZ = t_p + T_obs`).
They do not mention the edge family. -/

/-- An observed pulse is odd. -/
theorem obsPulse_odd {α q : ℝ} {Λ m : ℕ} {tA tZ : ℝ} {k : ℤ}
    (hk : k ∈ ocObsPulses α q Λ m tA tZ) : Odd k := by
  classical
  unfold ocObsPulses at hk
  exact (Finset.mem_filter.1 hk).2.1

/-- The enlarged window of an observed pulse meets the observation window. -/
theorem obsPulse_nonempty {α q : ℝ} {Λ m : ℕ} {tA tZ : ℝ} {k : ℤ}
    (hk : k ∈ ocObsPulses α q Λ m tA tZ) :
    (ocPulseWindow α q Λ m k ∩ Set.Icc tA tZ).Nonempty := by
  classical
  unfold ocObsPulses at hk
  exact (Finset.mem_filter.1 hk).2.2

/-- `IsLiftSetting.window`: the lift window of an observed pulse, clipped to the observation
window, is nonempty. -/
theorem window {α q : ℝ} {Λ m : ℕ} (ν : ℝ) {tA tZ : ℝ} {k₁ : ℤ}
    (hk₁ : k₁ ∈ ocObsPulses α q Λ m tA tZ) :
    max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2 ≤
      min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2 := by
  obtain ⟨t, ht, ht'⟩ := obsPulse_nonempty hk₁
  have ht0 : t ∈ Set.Icc (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m)
      (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) := ht
  exact div_le_div_of_nonneg_right ((max_le ht0.1 ht'.1).trans (le_min ht0.2 ht'.2))
    (sq_nonneg _)

/-- `IsLiftSetting.e_pos`. -/
theorem e_pos (q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) : 0 < ocEpsilon q Λ m :=
  AVRegularity.Construction.Stream.ocEpsilon_pos hΛ

/-- `IsLiftSetting.E_pos`. -/
theorem E_pos (q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) : 0 < ocEpsilon q Λ (m - 1) :=
  AVRegularity.Construction.Stream.ocEpsilon_pos hΛ

/-- `IsLiftSetting.ν_pos`. -/
theorem ν_pos {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ}
    {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀) :
    0 < ν :=
  cov.pos.1

/-- `IsLiftSetting.B_pos`. -/
theorem B_pos {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ}
    {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀) :
    0 < B :=
  cov.pos.2.1

/-- `IsLiftSetting.ρ_pos`, with `ρ = √(Bτ_m'')`. -/
theorem ρ_pos (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {B : ℝ} (hB : 0 < B) :
    0 < Real.sqrt (B * ocTauPP α q Λ m) :=
  Real.sqrt_pos.2 (mul_pos hB (AVRegularity.Construction.Stream.ocTauPP_pos hΛ))

/-- `IsLiftSetting.dstar_eq`: `d_* = ℓ√B`. -/
theorem dstar_eq (q : ℝ) (Λ m : ℕ) {ν : ℝ} (hν : 0 ≤ ν) (B : ℝ) :
    ocDStar q Λ m ν B = ocEll q Λ m ν * Real.sqrt B := by
  unfold ocDStar ocEll
  rw [Real.sqrt_div' B hν]
  ring

/-- `IsLiftSetting.εc_le`: `ε_c = d_*/ρ ≤ 1`, from `ℓ² ≤ τ_m''` (`IsWindowCover.ellT`). -/
theorem εc_le (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {ν B : ℝ} (hν : 0 ≤ ν) (hB : 0 < B)
    (hellT : ocEll q Λ m ν ^ 2 ≤ ocTauPP α q Λ m) :
    ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m) ≤ 1 := by
  have hρ := ρ_pos α q hΛ m hB
  have hℓ : 0 ≤ ocEll q Λ m ν := by
    unfold ocEll
    exact div_nonneg (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg ν)
  have hmul : ocEll q Λ m ν ^ 2 * B ≤ B * ocTauPP α q Λ m :=
    calc ocEll q Λ m ν ^ 2 * B = B * ocEll q Λ m ν ^ 2 := mul_comm _ _
      _ ≤ B * ocTauPP α q Λ m := mul_le_mul_of_nonneg_left hellT hB.le
  rw [div_le_one hρ, dstar_eq q Λ m hν B]
  calc ocEll q Λ m ν * Real.sqrt B
      = Real.sqrt (ocEll q Λ m ν ^ 2) * Real.sqrt B := by rw [Real.sqrt_sq hℓ]
    _ = Real.sqrt (ocEll q Λ m ν ^ 2 * B) := (Real.sqrt_mul (sq_nonneg _) B).symm
    _ ≤ Real.sqrt (B * ocTauPP α q Λ m) := Real.sqrt_le_sqrt hmul

/-- `IsLiftSetting.lam_le`: `λ_s = ρ/E ≤ 1`, from `√(Bτ_m'') ≤ ε_{m-1}` (`IsWindowCover.RE`). -/
theorem lam_le (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {B : ℝ}
    (hRE : Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1)) :
    Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) ≤ 1 :=
  (div_le_one (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ)).2 hRE

/-- `IsLiftSetting.η_le`: `η = ν/B ≤ 1`, from the monotonicity of the diffusivity chain. -/
theorem η_le {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {M' : ℕ}
    {κ : ℕ → ℝ} (hband : IsOCBandChain α q Λ ζ M' κ) {m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M')
    {ν B : ℝ} (hν : κ m = ν) (hB : κ (m - 1) = B) : ν / B ≤ 1 := by
  subst hν
  subst hB
  have hstep := AVRegularity.CycleReference.bandChain_step_ge hΛ hζ hband hm hmM
  have hBpos := AVRegularity.CycleReference.bandChain_pos hΛ hζ hband
    (show m - 1 ≤ M' by omega)
  exact (div_le_one hBpos).2 hstep

/-! The renewal chart of an observed pulse, and the bound charts of a window cover.

With `τ = τ_m`, `h = τ_m''` and `τ ≤ h/25`, the chart index `l = ⌊kτ/h + ½⌋` of the pulse `k`
satisfies `(l - ½)h ≤ kτ < (l + ½)h`. Hence

* the enlarged pulse window `[(k - 61/48)τ, (k + 61/48)τ]` lies in the anchor window
  `[(l - 1)h, (l + 1)h]` of the chart, and so does the lift window in cell time;
* if the enlarged pulse window meets a cover `[tA, tZ]` with core blocks `l₀, …, l₀ + P - 1`
  (`IsWindowCover.window`), then `l` is one of the `P + 2` bound charts `l₀ - 1 + i`. -/

/-- `τ_m ≤ τ_m''/25`, because `L_m ≥ 5`. -/
theorem ocTau_le_div (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) :
    ocTau α q Λ m ≤ ocTauPP α q Λ m / 25 := by
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hL := AVRegularity.ChildInert.ocL_ge_five α q hΛ m
  have h25 : (25 : ℝ) ≤ (ocL α q Λ m : ℝ) ^ 2 :=
    calc (25 : ℝ) = 5 ^ 2 := by norm_num
      _ ≤ (ocL α q Λ m : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
  have he : ocTau α q Λ m = ocTauPP α q Λ m / (ocL α q Λ m : ℝ) ^ 2 := rfl
  rw [he]
  exact div_le_div_of_nonneg_left hh.le (by norm_num) h25

/-- The chart index of a pulse: `(l - ½)τ_m'' ≤ kτ_m < (l + ½)τ_m''`. -/
theorem pulseChartIndex_bounds (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) (k : ℤ) :
    ((ocPulseChartIndex α q Λ m k : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ (k : ℝ) * ocTau α q Λ m ∧
      (k : ℝ) * ocTau α q Λ m <
        ((ocPulseChartIndex α q Λ m k : ℝ) + 1 / 2) * ocTauPP α q Λ m := by
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have h1 : (ocPulseChartIndex α q Λ m k : ℝ) ≤
      (k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2 :=
    Int.floor_le ((k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2)
  have h2 : (k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2 <
      (ocPulseChartIndex α q Λ m k : ℝ) + 1 :=
    Int.lt_floor_add_one ((k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2)
  have h1' : (ocPulseChartIndex α q Λ m k : ℝ) - 1 / 2 ≤
      (k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m := by linarith
  have h2' : (k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m <
      (ocPulseChartIndex α q Λ m k : ℝ) + 1 / 2 := by linarith
  exact ⟨(le_div_iff₀ hh).1 h1', (div_lt_iff₀ hh).1 h2'⟩

/-- **Chart range.** The chart of an observed pulse is one of the `P + 2` bound charts of the
cover. The hypothesis `hwin` is `IsWindowCover.window`. -/
theorem exists_chartIndex (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {tA tZ : ℝ} {l₀ : ℤ} {P : ℕ}
    (hwin : ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tA ∧
      tA < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m ∧
      ((l₀ : ℝ) + P - 3 / 2) * ocTauPP α q Λ m < tZ ∧
      tZ ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m)
    {k₁ : ℤ} (hk₁ : k₁ ∈ ocObsPulses α q Λ m tA tZ) :
    ∃ i : Fin (P + 2), (l₀ - 1 + i : ℤ) = ocPulseChartIndex α q Λ m k₁ := by
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hτ := ocTau_le_div α q hΛ m
  obtain ⟨hf1, hf2⟩ := pulseChartIndex_bounds α q hΛ m k₁
  obtain ⟨t, ht, ht3, ht4⟩ := obsPulse_nonempty hk₁
  have ht0 : t ∈ Set.Icc (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m)
      (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) := ht
  obtain ⟨ht1, ht2⟩ := ht0
  obtain ⟨hw1, -, -, hw4⟩ := hwin
  have hlow : ((l₀ : ℝ) - 2) * ocTauPP α q Λ m <
      (ocPulseChartIndex α q Λ m k₁ : ℝ) * ocTauPP α q Λ m := by linarith
  have hupp : (ocPulseChartIndex α q Λ m k₁ : ℝ) * ocTauPP α q Λ m <
      ((l₀ : ℝ) + P + 1) * ocTauPP α q Λ m := by linarith
  have hlow' : (l₀ : ℝ) - 2 < (ocPulseChartIndex α q Λ m k₁ : ℝ) :=
    lt_of_mul_lt_mul_right hlow hh.le
  have hupp' : (ocPulseChartIndex α q Λ m k₁ : ℝ) < (l₀ : ℝ) + P + 1 :=
    lt_of_mul_lt_mul_right hupp hh.le
  have hlowZ : l₀ - 2 < ocPulseChartIndex α q Λ m k₁ := by exact_mod_cast hlow'
  have huppZ : ocPulseChartIndex α q Λ m k₁ < l₀ + (P : ℤ) + 1 := by exact_mod_cast hupp'
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le
    (show 0 ≤ ocPulseChartIndex α q Λ m k₁ - (l₀ - 1) by omega)
  refine ⟨⟨n, by omega⟩, ?_⟩
  show l₀ - 1 + (n : ℤ) = ocPulseChartIndex α q Λ m k₁
  omega

/-- **Window containment.** The lift window of a pulse, clipped to `[tA, tZ]`, lies in the
cell-time window of its chart `l = ocPulseChartIndex k₁`. -/
theorem liftWindow_subset_chartWindow (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) (ν tA tZ : ℝ)
    (k₁ : ℤ) :
    Set.Icc (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) ⊆
      Set.Icc
        (max tA (((ocPulseChartIndex α q Λ m k₁ : ℝ) - 1) * ocTauPP α q Λ m) /
          ocEll q Λ m ν ^ 2)
        (min tZ (((ocPulseChartIndex α q Λ m k₁ : ℝ) + 1) * ocTauPP α q Λ m) /
          ocEll q Λ m ν ^ 2) := by
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hτ := ocTau_le_div α q hΛ m
  obtain ⟨hf1, hf2⟩ := pulseChartIndex_bounds α q hΛ m k₁
  have hA : ((ocPulseChartIndex α q Λ m k₁ : ℝ) - 1) * ocTauPP α q Λ m ≤
      ((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m := by linarith
  have hB : ((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m ≤
      ((ocPulseChartIndex α q Λ m k₁ : ℝ) + 1) * ocTauPP α q Λ m := by linarith
  have hℓ : 0 ≤ ocEll q Λ m ν ^ 2 := sq_nonneg _
  refine Set.Icc_subset_Icc (div_le_div_of_nonneg_right ?_ hℓ)
    (div_le_div_of_nonneg_right ?_ hℓ)
  · exact max_le (le_max_right _ _) (hA.trans (le_max_left _ _))
  · exact le_min (min_le_right _ _) ((min_le_left _ _).trans hB)

/-- The chart range and the window containment together, in the form consumed by the fields of
`IsWindowCover`: the bound chart `i` of an observed pulse, and its lift window inside the window
on which the chart-dependent bounds of the cover hold. -/
theorem exists_chart (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) (ν : ℝ) {tA tZ : ℝ} {l₀ : ℤ}
    {P : ℕ}
    (hwin : ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tA ∧
      tA < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m ∧
      ((l₀ : ℝ) + P - 3 / 2) * ocTauPP α q Λ m < tZ ∧
      tZ ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m)
    {k₁ : ℤ} (hk₁ : k₁ ∈ ocObsPulses α q Λ m tA tZ) :
    ∃ i : Fin (P + 2), (l₀ - 1 + i : ℤ) = ocPulseChartIndex α q Λ m k₁ ∧
      Set.Icc (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
          (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) ⊆
        Set.Icc
          (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
          (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2) := by
  obtain ⟨i, hi⟩ := exists_chartIndex α q hΛ m hwin hk₁
  refine ⟨i, hi, ?_⟩
  rw [hi]
  exact liftWindow_subset_chartWindow α q hΛ m ν tA tZ k₁

end AVRegularity.CycleComparison.LiftSetting
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleComparison.LiftSetting

/-! The metric fields of the lift setting of an observed pulse: `3I/4 ≤ G ≤ 5I/4` and
`‖∂_X^β G‖_∞ ≤ C_β λ_s^{|β|}` through `q_s`, for the material metric of a renewal chart.

The metric of the lift is `G(𝗍, X) = G_l(ℓ²𝗍, ρX)`, the material metric of the chart
`l = ocPulseChartIndex k₁` in the slow variable `X = y/ρ`, `ρ = √(Bτ_m'')`. It is symmetric,
smooth in `X` and continuous in `𝗍` for every chart. On the lift window of an observed pulse the
window cover gives, in the cell variables `z = (y - Y)/e` of the bound chart `l₀ - 1 + i = l`
(`IsWindowCover.metric_near`, `IsWindowCover.metric_jets`, for every `z`, so the centre `Y` is
irrelevant):

* `|ξ·(G - I)ξ| ≤ g|ξ|²` with `g ≤ g₀ ≤ 1/4`, hence `3I/4 ≤ G ≤ 5I/4` and `|G_ij| ≤ 5/4`;
* `‖D_z^r G_ij‖ ≤ C_r g (e/E)^r`, hence `‖D_X^r G_ij‖ ≤ C_r g (ρ/E)^r = C_r g λ_s^r`.

The constants of the jets are `liftMetricConst g₀ CG`. -/

/-! ### Constants and elementary facts -/

/-- The constants of the slow metric jets of the lift setting: `5/4` at order zero (the sup norm
of the entries of `G`), and `|C_r| g₀` at the orders `r ≥ 1`. -/
def liftMetricConst (g₀ : ℝ) (CG : ℕ → ℝ) (r : ℕ) : ℝ := if r = 0 then 5 / 4 else |CG r| * g₀

theorem liftMetricConst_zero (g₀ : ℝ) (CG : ℕ → ℝ) : liftMetricConst g₀ CG 0 = 5 / 4 := by
  rw [liftMetricConst, ite_eq_left rfl]

theorem liftMetricConst_of_ne_zero (g₀ : ℝ) (CG : ℕ → ℝ) {r : ℕ} (hr : r ≠ 0) :
    liftMetricConst g₀ CG r = |CG r| * g₀ := by
  rw [liftMetricConst, ite_eq_right hr]

/-- The quadratic form of `M - I`. -/
theorem quadForm_sub_one (M : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Vec 2) :
    ∑ a, ∑ k, ξ a * (M - (1 : Matrix (Fin 2) (Fin 2) ℝ)) a k * ξ k =
      (∑ i, ∑ j, M i j * ξ i * ξ j) - ∑ i, ξ i ^ 2 := by
  have h00 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have h11 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have h01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  simp only [Fin.sum_univ_two, Matrix.sub_apply, h00, h01, h10, h11]
  ring

/-- `|Q - S| ≤ gS` with `g ≤ g₀ ≤ 1/4` gives `3S/4 ≤ Q ≤ 5S/4`. -/
theorem ellip_of_near {Qf S g g₀ : ℝ} (hS : 0 ≤ S) (hg : g ≤ g₀) (hg₀ : g₀ ≤ 1 / 4)
    (h : |Qf - S| ≤ g * S) : (3 / 4) * S ≤ Qf ∧ Qf ≤ (5 / 4) * S := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have h3 : g * S ≤ (1 / 4) * S := mul_le_mul_of_nonneg_right (hg.trans hg₀) hS
  constructor <;> linarith

/-- The ellipticity bounds at the vector `(x, y)`. -/
theorem ellip_at (M : Fin 2 → Fin 2 → ℝ)
    (hell : ∀ ξ : Vec 2, (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, M i j * ξ i * ξ j ∧
      ∑ i, ∑ j, M i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) (x y : ℝ) :
    (3 / 4) * (x ^ 2 + y ^ 2) ≤
        M 0 0 * x * x + M 0 1 * x * y + (M 1 0 * y * x + M 1 1 * y * y) ∧
      M 0 0 * x * x + M 0 1 * x * y + (M 1 0 * y * x + M 1 1 * y * y) ≤
        (5 / 4) * (x ^ 2 + y ^ 2) := by
  have e0 : (![x, y] : Vec 2) 0 = x := rfl
  have e1 : (![x, y] : Vec 2) 1 = y := rfl
  have h := hell ![x, y]
  simp only [Fin.sum_univ_two, e0, e1] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The entries of a symmetric matrix with `3I/4 ≤ M ≤ 5I/4` are at most `5/4`. -/
theorem entry_abs_le_of_ellip (M : Fin 2 → Fin 2 → ℝ) (hsymm : M 0 1 = M 1 0)
    (hell : ∀ ξ : Vec 2, (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, M i j * ξ i * ξ j ∧
      ∑ i, ∑ j, M i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) (a b : Fin 2) :
    |M a b| ≤ 5 / 4 := by
  obtain ⟨h10a, h10b⟩ := ellip_at M hell 1 0
  obtain ⟨h01a, h01b⟩ := ellip_at M hell 0 1
  obtain ⟨-, h11b⟩ := ellip_at M hell 1 1
  obtain ⟨-, hm1b⟩ := ellip_at M hell 1 (-1)
  have h00 : |M 0 0| ≤ 5 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
  have h11 : |M 1 1| ≤ 5 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
  have h01 : |M 0 1| ≤ 5 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
  have h10 : |M 1 0| ≤ 5 / 4 := by
    rw [← hsymm]
    exact h01
  exact (Fin.forall_fin_two (p := fun a => ∀ b, |M a b| ≤ 5 / 4)).2
    ⟨(Fin.forall_fin_two (p := fun b => |M 0 b| ≤ 5 / 4)).2 ⟨h00, h01⟩,
      (Fin.forall_fin_two (p := fun b => |M 1 b| ≤ 5 / 4)).2 ⟨h10, h11⟩⟩ a b

/-- Transfer of a jet bound from the cell scale `e` to the lift scale `ρ`. -/
theorem jet_scale_transfer {e ρ E a b c t : ℝ} (he : 0 < e) (hρ : 0 ≤ ρ) (r : ℕ)
    (hG : a = ρ ^ r * t) (hc : b = e ^ r * t) (hb : b ≤ c * (e / E) ^ r) :
    a ≤ c * (ρ / E) ^ r := by
  have h1 : e ^ r * t ≤ e ^ r * (c * E⁻¹ ^ r) :=
    calc e ^ r * t = b := hc.symm
      _ ≤ c * (e / E) ^ r := hb
      _ = e ^ r * (c * E⁻¹ ^ r) := by
          rw [div_eq_mul_inv, mul_pow]
          ring
  have h2 : t ≤ c * E⁻¹ ^ r := le_of_mul_le_mul_left h1 (pow_pos he r)
  calc a = ρ ^ r * t := hG
    _ ≤ ρ ^ r * (c * E⁻¹ ^ r) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hρ r)
    _ = c * (ρ / E) ^ r := by
        rw [div_eq_mul_inv, mul_pow]
        ring

/-- The point `y` in the cell variables of centre `Y` and scale `e`. -/
theorem centre_add_smul {e : ℝ} (he : e ≠ 0) (Y y : Vec 2) : Y + e • (e⁻¹ • (y - Y)) = y := by
  rw [smul_smul, mul_inv_cancel₀ he, one_smul, add_comm, sub_add_cancel]

/-! ### Jets under the affine changes of variables -/

/-- The jets of `z ↦ f(Y + e z)`. -/
theorem norm_iteratedFDeriv_comp_add_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (e : ℝ) (Y : Vec 2) (r : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun z' : Vec 2 => f (Y + e • z')) z‖ =
      |e| ^ r * ‖iteratedFDeriv ℝ r f (Y + e • z)‖ := by
  have htop : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hshift : ContDiff ℝ (r : ℕ∞) (fun w : Vec 2 => f (Y + w)) :=
    (hf.of_le htop).comp ((contDiff_const (c := Y)).add contDiff_id)
  have h := iteratedFDeriv_comp_smul_norm r (fun w : Vec 2 => f (Y + w)) hshift e z
  rw [iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) r Y (e • z)] at h
  exact h

/-- Entrywise jet bounds control the jet of a `2 × 2` array in the supremum norm. -/
theorem norm_iteratedFDeriv_pi2_le_of_entries (A : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (n : ℕ) (x : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i j, ‖iteratedFDeriv ℝ n (fun y => A y i j) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n A x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro w
  have hprod : 0 ≤ C * ∏ k, ‖w k‖ := mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hprod).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hprod).mpr
  intro j
  let L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
  have he := L.iteratedFDeriv_comp_left (hA.contDiffAt (x := x)) (i := n) (by simp)
  have hev := congrArg (fun G => G w) he
  change iteratedFDeriv ℝ n (fun y => A y i j) x w = (iteratedFDeriv ℝ n A x w) i j at hev
  rw [← hev]
  exact (ContinuousMultilinearMap.le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right (hb i j) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

/-! ### The material metric of a chart -/

/-- The material metric is symmetric. -/
theorem materialMetric_symm (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (s : ℝ) (y : Vec 2) (i j : Fin 2) :
    ocMaterialMetric α q Λ m φ hφ l s y i j = ocMaterialMetric α q Λ m φ hφ l s y j i := by
  have h : (ocMaterialMetric α q Λ m φ hφ l s y).IsSymm := by
    unfold ocMaterialMetric
    exact Matrix.isSymm_mul_transpose_self _
  exact h.apply j i

/-- The entries of the material metric are smooth in the label. -/
theorem materialMetric_entry_contDiff (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (s : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => ocMaterialMetric α q Λ m φ hφ l s y i j) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (s, y)) := by fun_prop
  have hs := (AVRegularity.CycleWords.ocMaterialMetric_joint_contDiff α q Λ m hφ l i j).comp hm
  simpa only [Function.comp_def] using hs

/-- From the cell form at any centre to the material form: nearness to the identity. -/
theorem near_of_cell {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {l : ℤ} {ν : ℝ} (he : 0 < ocEpsilon q Λ m) {Y : Vec 2} {t g : ℝ}
    (hcell : ∀ z (ξ : Vec 2), |∑ a', ∑ k, ξ a' *
      (ocCellMetric α q Λ m φ hφ l ν Y t z - (1 : Matrix (Fin 2) (Fin 2) ℝ)) a' k * ξ k| ≤
        g * ∑ a', ξ a' ^ 2) (y ξ : Vec 2) :
    |(∑ i, ∑ j, ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t) y i j * ξ i * ξ j) -
        ∑ i, ξ i ^ 2| ≤ g * ∑ i, ξ i ^ 2 := by
  have hM : ocCellMetric α q Λ m φ hφ l ν Y t ((ocEpsilon q Λ m)⁻¹ • (y - Y)) =
      ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t) y := by
    show ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t)
      (Y + ocEpsilon q Λ m • ((ocEpsilon q Λ m)⁻¹ • (y - Y))) = _
    rw [centre_add_smul he.ne']
  have h := hcell ((ocEpsilon q Λ m)⁻¹ • (y - Y)) ξ
  rw [hM, quadForm_sub_one (ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t) y) ξ] at h
  exact h

/-- From the cell form at any centre to the lift form: the jets of one entry. -/
theorem entry_jet_of_cell {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {l : ℤ} {ν : ℝ} (he : 0 < ocEpsilon q Λ m) {Y : Vec 2} {t c E : ℝ} {r : ℕ} {a' k : Fin 2}
    (hcell : ∀ z : Vec 2, ‖iteratedFDeriv ℝ r
      (fun z' => ocCellMetric α q Λ m φ hφ l ν Y t z' a' k) z‖ ≤
        c * (ocEpsilon q Λ m / E) ^ r)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X' : Vec 2 =>
        ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t) (ρ • X') a' k) X‖ ≤
      c * (ρ / E) ^ r := by
  have hMt := materialMetric_entry_contDiff α q Λ m hφ l (ocEll q Λ m ν ^ 2 * t) a' k
  have htop : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have h1 := iteratedFDeriv_comp_smul_norm r
    (fun y : Vec 2 => ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t) y a' k)
    (hMt.of_le htop) ρ X
  have h2 := norm_iteratedFDeriv_comp_add_smul
    (fun y : Vec 2 => ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * t) y a' k) hMt
    (ocEpsilon q Λ m) Y r ((ocEpsilon q Λ m)⁻¹ • (ρ • X - Y))
  rw [centre_add_smul he.ne'] at h2
  have h3 : ‖iteratedFDeriv ℝ r (fun z' : Vec 2 => ocMaterialMetric α q Λ m φ hφ l
      (ocEll q Λ m ν ^ 2 * t) (Y + ocEpsilon q Λ m • z') a' k)
      ((ocEpsilon q Λ m)⁻¹ • (ρ • X - Y))‖ ≤ c * (ocEpsilon q Λ m / E) ^ r := hcell _
  rw [abs_of_nonneg hρ] at h1
  rw [abs_of_pos he] at h2
  exact jet_scale_transfer he hρ r h1 h2 h3

/-! ### The bound charts of a window cover -/

/-- On the window of the bound chart `i`, the material metric is `g`-near the identity. -/
theorem materialMetric_near {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {m : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream (Φ (m - 1))}
    {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
    {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀)
    (i : Fin (P + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc
      (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2))
    (y ξ : Vec 2) :
    |(∑ i', ∑ j, ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i)
          (ocEll q Λ m ν ^ 2 * t) y i' j * ξ i' * ξ j) - ∑ i', ξ i' ^ 2| ≤
      g * ∑ i', ξ i' ^ 2 :=
  near_of_cell (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) (cov.metric_near i t ht) y ξ

/-- On the window of the bound chart `i`, `3I/4 ≤ G_l ≤ 5I/4`. -/
theorem materialMetric_ellip {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {m : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream (Φ (m - 1))}
    {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
    {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀)
    (hg₀ : g₀ ≤ 1 / 4) (i : Fin (P + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc
      (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2))
    (y ξ : Vec 2) :
    (3 / 4) * ∑ i', ξ i' ^ 2 ≤ ∑ i', ∑ j, ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i)
        (ocEll q Λ m ν ^ 2 * t) y i' j * ξ i' * ξ j ∧
      ∑ i', ∑ j, ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i)
        (ocEll q Λ m ν ^ 2 * t) y i' j * ξ i' * ξ j ≤ (5 / 4) * ∑ i', ξ i' ^ 2 :=
  ellip_of_near (Finset.sum_nonneg fun i' _ => sq_nonneg (ξ i')) cov.g_range.2 hg₀
    (materialMetric_near hΛ cov i ht y ξ)

/-- On the window of the bound chart `i`, the jets of one entry in the slow variable `X = y/ρ`. -/
theorem materialMetric_entry_jet {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {m : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream (Φ (m - 1))}
    {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
    {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀)
    (i : Fin (P + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc
      (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2))
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ qJ) {ρ : ℝ} (hρ : 0 ≤ ρ) (X : Vec 2) (a' k : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun X' : Vec 2 => ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i)
        (ocEll q Λ m ν ^ 2 * t) (ρ • X') a' k) X‖ ≤
      CG r * g * (ρ / ocEpsilon q Λ (m - 1)) ^ r :=
  entry_jet_of_cell (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ)
    (fun z => cov.metric_jets i t ht z r hr1 hr a' k) hρ X

/-- On the window of the bound chart `i`, the jets of the metric array in the slow variable
`X = y/ρ`, in the supremum norm of the entries. -/
theorem materialMetric_pi_jet {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {m : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream (Φ (m - 1))}
    {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
    {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀)
    (hg₀ : g₀ ≤ 1 / 4) (i : Fin (P + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc
      (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2))
    {r : ℕ} (hr : r ≤ qJ) {ρ : ℝ} (hρ : 0 ≤ ρ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X' : Vec 2 => fun a' k : Fin 2 =>
        ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) (ocEll q Λ m ν ^ 2 * t)
          (ρ • X') a' k) X‖ ≤
      liftMetricConst g₀ CG r * (ρ / ocEpsilon q Λ (m - 1)) ^ r := by
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X' : Vec 2 => fun a' k : Fin 2 =>
      ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) (ocEll q Λ m ν ^ 2 * t)
        (ρ • X') a' k) := by
    apply contDiff_pi.mpr
    intro a'
    apply contDiff_pi.mpr
    intro k
    exact (materialMetric_entry_contDiff α q Λ m hφ (l₀ - 1 + i) (ocEll q Λ m ν ^ 2 * t)
      a' k).comp (contDiff_const_smul ρ)
  by_cases hr0 : r = 0
  · subst hr0
    rw [norm_iteratedFDeriv_zero, liftMetricConst_zero, pow_zero, mul_one]
    have h54 : (0 : ℝ) ≤ 5 / 4 := by norm_num
    apply (pi_norm_le_iff_of_nonneg h54).mpr
    intro a'
    apply (pi_norm_le_iff_of_nonneg h54).mpr
    intro k
    rw [Real.norm_eq_abs]
    exact entry_abs_le_of_ellip
      (fun a b : Fin 2 => ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i)
        (ocEll q Λ m ν ^ 2 * t) (ρ • X) a b)
      (materialMetric_symm α q Λ m hφ (l₀ - 1 + i) (ocEll q Λ m ν ^ 2 * t) (ρ • X) 0 1)
      (fun ξ => materialMetric_ellip hΛ cov hg₀ i ht (ρ • X) ξ) a' k
  · have hr1 : 1 ≤ r := by omega
    have hg0 : 0 ≤ g := cov.g_range.1
    have hgg : g ≤ g₀ := cov.g_range.2
    have hpow : 0 ≤ (ρ / ocEpsilon q Λ (m - 1)) ^ r := pow_nonneg (div_nonneg hρ hE.le) r
    have hCG : CG r * g ≤ |CG r| * g₀ :=
      (mul_le_mul_of_nonneg_right (le_abs_self (CG r)) hg0).trans
        (mul_le_mul_of_nonneg_left hgg (abs_nonneg (CG r)))
    rw [liftMetricConst_of_ne_zero g₀ CG hr0]
    refine norm_iteratedFDeriv_pi2_le_of_entries _ hA r X _
      (mul_nonneg (mul_nonneg (abs_nonneg (CG r)) (hg0.trans hgg)) hpow) fun a' k => ?_
    exact (materialMetric_entry_jet hΛ cov i ht hr1 hr hρ X a' k).trans
      (mul_le_mul_of_nonneg_right hCG hpow)

/-! ### The fields of the lift setting -/

/-- `IsLiftSetting.G_symm`. -/
theorem G_symm (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B : ℝ) (k₁ : ℤ) (t : ℝ) (X : Vec 2) (i j : Fin 2) :
    ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k₁)
        (ocEll q Λ m ν ^ 2 * t) (Real.sqrt (B * ocTauPP α q Λ m) • X) i j =
      ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k₁)
        (ocEll q Λ m ν ^ 2 * t) (Real.sqrt (B * ocTauPP α q Λ m) • X) j i :=
  materialMetric_symm α q Λ m hφ _ _ _ i j

/-- `IsLiftSetting.G_meas`: the metric is continuous in the cell time. -/
theorem G_meas (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B : ℝ) (k₁ : ℤ) (X : Vec 2) (i j : Fin 2) :
    Measurable fun t : ℝ => ocMaterialMetric α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k₁) (ocEll q Λ m ν ^ 2 * t)
      (Real.sqrt (B * ocTauPP α q Λ m) • X) i j := by
  have hm : Continuous (fun t : ℝ =>
      (ocEll q Λ m ν ^ 2 * t, Real.sqrt (B * ocTauPP α q Λ m) • X)) := by fun_prop
  exact ((AVRegularity.CycleWords.ocMaterialMetric_joint_contDiff α q Λ m hφ
    (ocPulseChartIndex α q Λ m k₁) i j).continuous.comp hm).measurable

/-- `IsLiftSetting.G_smooth`: the metric is smooth in the slow variable. -/
theorem G_smooth (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B : ℝ) (k₁ : ℤ) (qs : ℕ) (t : ℝ) (i j : Fin 2) :
    ContDiff ℝ (qs : ℕ∞) fun X : Vec 2 => ocMaterialMetric α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k₁) (ocEll q Λ m ν ^ 2 * t)
      (Real.sqrt (B * ocTauPP α q Λ m) • X) i j := by
  have htop : ((qs : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  exact ((materialMetric_entry_contDiff α q Λ m hφ (ocPulseChartIndex α q Λ m k₁)
    (ocEll q Λ m ν ^ 2 * t) i j).comp
      (contDiff_const_smul (Real.sqrt (B * ocTauPP α q Λ m)))).of_le htop

/-- `IsLiftSetting.G_ellip`: `3I/4 ≤ G ≤ 5I/4` on the lift window of an observed pulse. -/
theorem G_ellip {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ}
    {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀)
    (hg₀ : g₀ ≤ 1 / 4) {k₁ : ℤ} (hk₁ : k₁ ∈ ocObsPulses α q Λ m tA tZ) :
    ∀ t ∈ Set.Icc (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      ∀ X : Vec 2, ∀ ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ocMaterialMetric α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k₁) (ocEll q Λ m ν ^ 2 * t)
            (Real.sqrt (B * ocTauPP α q Λ m) • X) i j * ξ i * ξ j ∧
          ∑ i, ∑ j, ocMaterialMetric α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k₁) (ocEll q Λ m ν ^ 2 * t)
            (Real.sqrt (B * ocTauPP α q Λ m) • X) i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2 := by
  obtain ⟨i, hi, hsub⟩ := exists_chart α q hΛ m ν cov.window hk₁
  intro t ht X ξ
  have h := materialMetric_ellip hΛ cov hg₀ i (hsub ht)
    (Real.sqrt (B * ocTauPP α q Λ m) • X) ξ
  rw [hi] at h
  exact h

/-- `IsLiftSetting.G_jets`: `‖D_X^r G‖_∞ ≤ C_r λ_s^r` through `q_s ≤ q_J` on the lift window of
an observed pulse, with `C = liftMetricConst g₀ CG` and `λ_s = ρ/E`. -/
theorem G_jets {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tA tZ ρs g g₀ a B₀ lam₀ Cb : ℝ} {qJ Kmax : ℕ}
    {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g₀ a B₀ lam₀ Cb qJ Kmax CG l₀ P y₀)
    (hg₀ : g₀ ≤ 1 / 4) {k₁ : ℤ} (hk₁ : k₁ ∈ ocObsPulses α q Λ m tA tZ) {qs : ℕ}
    (hqs : qs ≤ qJ) :
    ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
          (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
        ⨆ X : Vec 2, ‖iteratedFDeriv ℝ r (fun X' : Vec 2 => fun i j : Fin 2 =>
          ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k₁)
            (ocEll q Λ m ν ^ 2 * t) (Real.sqrt (B * ocTauPP α q Λ m) • X') i j) X‖ₑ) ≤
        ENNReal.ofReal (liftMetricConst g₀ CG r *
          (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ^ r) := by
  obtain ⟨i, hi, hsub⟩ := exists_chart α q hΛ m ν cov.window hk₁
  intro r hr
  refine iSup₂_le fun t ht => iSup_le fun X => ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := materialMetric_pi_jet hΛ cov hg₀ i (hsub ht) (hr.trans hqs)
    (Real.sqrt_nonneg (B * ocTauPP α q Λ m)) X
  rw [hi] at h
  exact h

end AVRegularity.CycleComparison.LiftSetting
end
end
