-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.SourceLocalMetricCongruence
public import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Velocity.Port.Section2FlowRegularityCore
import AVRegularity.CycleReference.TorusStreamFluxEquation
public import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.Definitions.Construction.Preparation
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.Floor

section
section
/-! A measurable-window extension of coefficients, identical on the original closed window. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def windowEdges (a b : ℝ) (edge : ConstituentEdges D h) : ConstituentEdges D h :=
  fun v u d => (edge v u d).map fun γ =>
    { γ with coeff := fun α t X z => γ.coeff α (max a (min b t)) X z
             periodic := fun α t X => γ.periodic α (max a (min b t)) X }

theorem windowEdges_agree (a b : ℝ) (edge : ConstituentEdges D h)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    EntryWeakProofs.SlowOpenEdgeEq Set.univ t edge (windowEdges a b edge) := by
  intro v u d
  unfold windowEdges
  induction edge v u d with
  | nil => exact List.Forall₂.nil
  | cons γ l ih =>
    apply List.Forall₂.cons ?_ ih
    refine ⟨rfl, ?_⟩
    intro α X _ z
    simp only [min_eq_right ht.2, max_eq_right ht.1]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Identify the long columns of the actual fresh axes with the sampled flow derivatives. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem fresh_axes_long_columns_on_quiet_margin (D : OCData) (b : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : 0 < D.κ (b + 1))
    (H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2) (haxes : IsFreshAxes D b H₁ H₂) (l : ℤ) :
    let s := ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)
    ∃ (tH tV : ℝ) (lH lV : ℤ), IsPulseSample D b s tH tV lH lV ∧
    ∀ t ∈ Set.Ico s (((l : ℝ) + 3 / 2) * ocTauPP D.α D.q D.Λ (b + 1)),
      let aScale := Real.sqrt ((D.κ b)⁻¹ *
        ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tH 0 0)
      H₁ t (basisVec 0) = aScale •
        fderiv ℝ (fun y => D.flowOf b t y s) 0
          (sampledFlowDerivative D b s tH lH (basisVec 0)) ∧
      H₂ t (basisVec 1) = aScale •
        fderiv ℝ (fun y => D.flowOf b t y s) 0
          (sampledFlowDerivative D b s tV lV (basisVec 1)) := by
  dsimp only
  let s := ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)
  obtain ⟨tH, tV, lH, lV, hs, hmat⟩ := haxes l
  refine ⟨tH, tV, lH, lV, hs, ?_⟩
  intro t ht
  obtain ⟨hH₁, hH₂⟩ := hmat t ht
  constructor
  · rw [hH₁]
    exact transported_sampledEllipse_apply_basis D b s tH lH 0
      (fun y => D.flowOf b t y s) 0
  · rw [hH₂]
    have hh := transported_sampledEllipse_apply_basis D b s tV lV 1
      (fun y => D.flowOf b t y s) 0
    rw [pulseSample_vertical_eq_horizontal D b hΛ hζ hκ s tH tV lH lV hs] at hh
    exact hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Measurable coefficients on a closed window admit a literal measurable clamped extension. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem windowEdges_coefficient_measurable (a b : ℝ) (hab : a ≤ b)
    (edge : ConstituentEdges D h)
    (hm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z,
      Measurable (fun t : Set.Icc a b => γ.coeff α t X z)) :
    ∀ v u d, ∀ γ ∈ windowEdges a b edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α t X z) := by
  intro v u d γ hγ α X z
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  let clock : ℝ → Set.Icc a b := fun t =>
    ⟨max a (min b t), le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hc : Measurable clock :=
    ((continuous_const.max (continuous_const.min continuous_id)).measurable).subtype_mk
  exact (hm v u d δ hδ α X z).comp hc

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Time extension preserves the source graph and its spatial certificates on the original window. -/
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem windowEdges_empty_iff (a b : ℝ) (edge : ConstituentEdges D h)
    (v u : ι) (d : Finset.Icc 2 D) :
    windowEdges a b edge v u d = [] ↔ edge v u d = [] := by
  simp only [windowEdges, List.map_eq_nil_iff]

theorem windowEdges_depth (a b : ℝ) (edge : ConstituentEdges D h) {H : ℕ}
    (hdepth : HasDepthAtMost edge H) : HasDepthAtMost (windowEdges a b edge) H := by
  intro path
  obtain ⟨k, hk⟩ := hdepth path
  exact ⟨k, fun d => (windowEdges_empty_iff a b edge _ _ d).mpr (hk d)⟩

theorem windowEdges_transverse (a b : ℝ) (edge : ConstituentEdges D h) (par : Fin 2)
    (htrans : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsTransverseOn par (Set.Icc a b) (γ.coeff α)) :
    ∀ v u d, ∀ γ ∈ windowEdges a b edge v u d, ∀ α,
      IsTransverseOn par (Set.Icc a b) (γ.coeff α) := by
  intro v u d γ hγ α t ht X z s
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  simpa only [min_eq_right ht.2, max_eq_right ht.1] using htrans v u d δ hδ α t ht X z s

theorem windowEdges_boxSmooth (a b : ℝ) (edge : ConstituentEdges D h) (sX sZ : ℕ)
    (hs : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, ∀ t ∈ Set.Icc a b,
      IsBoxSmooth sX sZ (γ.coeff α t)) :
    ∀ v u d, ∀ γ ∈ windowEdges a b edge v u d, ∀ α, ∀ t ∈ Set.Icc a b,
      IsBoxSmooth sX sZ (γ.coeff α t) := by
  intro v u d γ hγ α t ht
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  simpa only [min_eq_right ht.2, max_eq_right ht.1] using hs v u d δ hδ α t ht

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Clamping the source time preserves every mixed supremum and envelope on the original window. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem jetSup_clamped_time_eq (a b : ℝ) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) :
    jetSup (Set.Icc a b) r q (fun t X z => f (max a (min b t)) X z) =
      jetSup (Set.Icc a b) r q f := by
  unfold jetSup
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  simp only [min_eq_right ht.2, max_eq_right ht.1]

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem windowEdges_scaled_envelope (a b lam : ℝ) (π : ι → ℝ)
    (edge : ConstituentEdges D h) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (price : ι → ι → ℝ) (Θ : ℝ)
    (he : IsScaledJetEnvelope π edge (Set.Icc a b) lam Cj qs qf price Θ) :
    IsScaledJetEnvelope π (windowEdges a b edge) (Set.Icc a b) lam Cj qs qf price Θ := by
  refine ⟨he.nonneg, he.row_sum, he.col_sum, ?_⟩
  intro v u r hr q hq
  simpa only [windowEdges, List.map_map, Function.comp_def, jetSup_clamped_time_eq] using
    he.jets v u r hr q hq

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The fine and parent band comparisons give a uniform balanced drift amplitude before the data. -/
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.CycleReference

theorem bandChain_balanced_peclet_bound {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m < M →
          Real.sqrt (κ m / κ (m - 1)) * (ocEpsilon q Λ m ^ (1 + α) / κ m) ≤ C := by
  obtain ⟨Cf, hCf, Lf, hLf, hf⟩ := bandChain_interior_diffusivities hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cp, hCp, Lp, hLp, hp⟩ := bandChain_parent_comparisons hα₀ hα₁ hs₀ hs₁ hq hζ
  have hCfp : 0 < Cf := zero_lt_one.trans_le hCf
  have hCpp : 0 < Cp := zero_lt_one.trans_le hCp
  have hprod : 1 ≤ Cf * Cp := by nlinarith only [hCf, hCp]
  have hCs : 1 ≤ Real.sqrt (Cf * Cp) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hprod
  refine ⟨Real.sqrt (Cf * Cp), hCs, max Lf Lp, hLf.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛf : Lf ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛp : Lp ≤ Λ := (le_max_right _ _).trans hΛ
  have hΛ₁ : 1 ≤ Λ := by have hh := hLf.trans hΛf; omega
  have he : 0 < ocEpsilon q Λ m := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ₁
  have hx := hf Λ hΛf M hM κ hκ m (by omega) hmM
  have hy := (hp Λ hΛp M hM κ hκ m hm (by omega)).2
  have hh := asymp_mul hCfp hCpp (Real.rpow_nonneg he.le _) (Real.rpow_nonneg he.le _) hx hy
  have hpower : ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) *
      ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) = (ocEpsilon q Λ m ^ (1 + α)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add he, ← Real.rpow_add he]
    congr 1
    ring
  rw [hpower] at hh
  have hs := asymp_sqrt (mul_pos hCfp hCpp) (sq_nonneg _) hh
  rw [Real.sqrt_sq (Real.rpow_nonneg he.le _)] at hs
  have hCpos : 0 < Real.sqrt (Cf * Cp) := zero_lt_one.trans_le hCs
  apply balanced_peclet_le _ _ _ _
    (bandChain_pos hΛ₁ hζ hκ (by omega)) (bandChain_pos hΛ₁ hζ hκ (by omega))
  calc
    _ = Real.sqrt (Cf * Cp) * ((Real.sqrt (Cf * Cp))⁻¹ * ocEpsilon q Λ m ^ (1 + α)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hCpos.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs.1 hCpos.le

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Copy-adapt the entry width ledger to every interior passage of a longer band chain.
The terminal index is independent of the passage index. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.CycleReference AVRegularity.EntryScales

theorem band_interior_width_ratios {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ σw tT c₀ cr : ℝ,
      0 < σw → 0 < tT → 0 < c₀ → 0 < cr →
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ T κ →
      ∀ M : ℕ, 3 ≤ M → M ≤ T →
      ocEpsilon q Λ M ^ (1 + σw) /
          (c₀ * min (ocEpsilon q Λ (M - 1))
            (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1)))) ≤
        C * ocEpsilon q Λ (M - 1) ^ (q * ocGamma α q + 4 * ocDelta α q + q * σw) ∧
      cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * ocEpsilon q Λ (M - 1) ^ tT /
          (c₀ * min (ocEpsilon q Λ (M - 1))
            (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1)))) ≤
        C * ocEpsilon q Λ (M - 1) ^ (ocDelta α q + tT) ∧
      ocEpsilon q Λ M ^ (1 + σw) /
          (cr * Real.sqrt (κ (M - 1 - 1) * ocTauPP α q Λ (M - 1))) ≤
        C * ocEpsilon q Λ (M - 1 - 1) ^ (q ^ 2 * (1 + σw) - 1 - ocC α q) ∧
      cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * ocEpsilon q Λ (M - 1) ^ tT /
          (cr * Real.sqrt (κ (M - 1 - 1) * ocTauPP α q Λ (M - 1))) ≤
        C * ocEpsilon q Λ (M - 1 - 1) ^ (q * (1 + ocC α q + tT) - 1 - ocC α q) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K1, hK1, L1, hL1, h1⟩ := epsilon_power_scale_asymp hq.1 1
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hCip : 0 < Ci := by linarith
  have hK1p : 0 < K1 := by linarith
  refine ⟨max Li L1, hLi.trans (le_max_left _ _), fun Λ hΛ σw tT c₀ cr hσ ht hc₀ hcr => ?_⟩
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ1 : L1 ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hLi.trans hΛi
  have hΛpos : 1 ≤ Λ := by omega
  -- constants depending only on the data
  set Cρ : ℝ := Real.sqrt (Ci * 2 ^ (26 : ℕ)) * max cr cr⁻¹ with hCρ
  have hCρp : 0 < Cρ := mul_pos (Real.sqrt_pos.2 (by positivity)) (lt_max_of_lt_left hcr)
  set Cm : ℝ := (Real.sqrt (Ci * 1))⁻¹ ⊓ 1 with hCm
  have hCmp : 0 < Cm := lt_min (inv_pos.2 (Real.sqrt_pos.2 (by positivity))) one_pos
  have hmul1 : 0 < c₀ * Cm := mul_pos hc₀ hCmp
  have hsr : 0 < Real.sqrt (Ci * 1) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf =
      (K1 ^ (1 + σw) * (c₀ * Cm)⁻¹) + (Cρ * (c₀ * Cm)⁻¹) +
      (K1 ^ (1 + σw) * K1 ^ (q * (1 + σw)) * Cρ) + (Cρ * K1 ^ (1 + ocC α q + tT) * Cρ) :=
    ⟨_, rfl⟩
  have hp1 : 0 < K1 ^ (1 + σw) := Real.rpow_pos_of_pos hK1p _
  have hp2 : 0 < K1 ^ (q * (1 + σw)) := Real.rpow_pos_of_pos hK1p _
  have hp3 : 0 < K1 ^ (1 + ocC α q + tT) := Real.rpow_pos_of_pos hK1p _
  have hinvp : 0 < (c₀ * Cm)⁻¹ := inv_pos.2 hmul1
  have hCfp : 0 < Cf := by rw [hCfdef]; positivity
  refine ⟨Cf, hCfp, fun T κ hκ M hM hMT => ?_⟩
  have hE0 := AVRegularity.Scales.epsilon_basic (m := M - 1) hq.1 h128
  have hY0 := AVRegularity.Scales.epsilon_basic (m := M - 1 - 1) hq.1 h128
  have hx0 := AVRegularity.Scales.epsilon_basic (m := M) hq.1 h128
  have hB0 : 0 < κ (M - 1) := bandChain_pos hΛpos hζ hκ (by omega)
  have hB20 : 0 < κ (M - 1 - 1) := bandChain_pos hΛpos hζ hκ (by omega)
  have hh0 : 0 < ocTauPP α q Λ M := AVRegularity.Construction.Stream.ocTauPP_pos hΛpos
  have hh10 : 0 < ocTauPP α q Λ (M - 1) := AVRegularity.Construction.Stream.ocTauPP_pos hΛpos
  have hx : ocEpsilon q Λ M ≤ K1 * ocEpsilon q Λ (M - 1) ^ q := by
    have := (h1 Λ M hΛ1 (by omega)).2
    simpa using this
  have hEY : ocEpsilon q Λ (M - 1) ≤ K1 * ocEpsilon q Λ (M - 1 - 1) ^ q := by
    have := (h1 Λ (M - 1) hΛ1 (by omega)).2
    simpa using this
  have hB := hi Λ hΛi T (by omega) κ hκ (M - 1) (by omega) (by omega)
  have hB2 := hi Λ hΛi T (by omega) κ hκ (M - 1 - 1) (by omega) (by omega)
  have hhM := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := M)
  have hhM1 := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := M - 1)
  have hρ := rho_asymp (α := α) (q := q) hE0.1 hCip (by positivity) hcr hB hhM
  have hρn := rho_asymp (α := α) (q := q) hY0.1 hCip (by positivity) hcr hB2 hhM1
  set E := ocEpsilon q Λ (M - 1) with hEd
  set Y := ocEpsilon q Λ (M - 1 - 1) with hYd
  set x := ocEpsilon q Λ M with hxd
  have hEn : ∀ r : ℝ, 0 ≤ E ^ r := fun r => Real.rpow_nonneg hE0.1.le r
  have hYn : ∀ r : ℝ, 0 ≤ Y ^ r := fun r => Real.rpow_nonneg hY0.1.le r
  have hid := prepared_radius_exponent_identity (α := α) hq.1
  have hcdef : ocC α q = ocGamma α q / 2 + ocDelta α q := rfl
  -- molecular radius lower bound
  have hA : ocA α q Λ (M - 1) = E ^ ((1 + α) - 2) := rfl
  have hApos : 0 < ocA α q Λ (M - 1) := by rw [hA]; exact Real.rpow_pos_of_pos hE0.1 _
  have hAas : ocAsymp 1 (ocA α q Λ (M - 1)) (E ^ ((1 + α) - 2)) := by
    rw [hA]; exact asymp_one_self _
  have hBA := aPow_div hE0.1 hCip one_pos hApos hB hAas
  have hS := aPow_sqrt hE0.1 (by positivity) hBA
  have hS' : ocAsymp (Real.sqrt (Ci * 1)) (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1)))
      (E ^ (1 + ocGamma α q / 2)) := aPow_congr (by ring) hS
  have hEw : E ^ (1 + ocGamma α q / 2) ≤ E := by
    have := Real.rpow_le_rpow_of_exponent_ge hE0.1 hE0.2.1
      (show (1 : ℝ) ≤ 1 + ocGamma α q / 2 by linarith)
    simpa using this
  have hmin : Cm * E ^ (1 + ocGamma α q / 2) ≤
      min E (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1))) := by
    refine le_min ?_ ?_
    · have hC1 : Cm ≤ 1 := min_le_right _ _
      calc Cm * E ^ (1 + ocGamma α q / 2) ≤ 1 * E ^ (1 + ocGamma α q / 2) :=
            mul_le_mul_of_nonneg_right hC1 (hEn _)
        _ ≤ E := by rw [one_mul]; exact hEw
    · have hC1 : Cm ≤ (Real.sqrt (Ci * 1))⁻¹ := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right hC1 (hEn _)).trans hS'.1
  have hρs : (((c₀ * Cm)⁻¹)⁻¹) * E ^ (1 + ocGamma α q / 2) ≤
      c₀ * min E (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1))) := by
    rw [inv_inv]
    calc c₀ * Cm * E ^ (1 + ocGamma α q / 2) = c₀ * (Cm * E ^ (1 + ocGamma α q / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin hc₀.le
  have hρs0 : 0 < c₀ * min E (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1))) := by
    refine mul_pos hc₀ (lt_min hE0.1 (Real.sqrt_pos.2 (div_pos hB0 hApos)))
  -- numerators
  have hxσ : x ^ (1 + σw) ≤ K1 ^ (1 + σw) * E ^ (q * (1 + σw)) :=
    pow_bound hE0.1.le hK1p.le hx0.1.le hx (by linarith)
  have t2 : 0 < Cρ * (c₀ * Cm)⁻¹ := mul_pos hCρp hinvp
  have t3 : 0 < K1 ^ (1 + σw) * K1 ^ (q * (1 + σw)) * Cρ := by positivity
  have t4 : 0 < Cρ * K1 ^ (1 + ocC α q + tT) * Cρ := by positivity
  have t1 : 0 < K1 ^ (1 + σw) * (c₀ * Cm)⁻¹ := mul_pos hp1 hinvp
  have hww : ∀ r : ℝ, E ^ r / E ^ (1 + ocGamma α q / 2) = E ^ (r - (1 + ocGamma α q / 2)) :=
    fun r => (Real.rpow_sub hE0.1 _ _).symm
  have hρpos : 0 < cr * Real.sqrt (κ (M - 1 - 1) * ocTauPP α q Λ (M - 1)) :=
    mul_pos hcr (Real.sqrt_pos.2 (mul_pos hB20 hh10))
  -- (1)
  have hq1 := quotient_upper_bound hp1 hinvp (hEn (q * (1 + σw)))
    (Real.rpow_pos_of_pos hE0.1 (1 + ocGamma α q / 2)) hρs0 hxσ hρs
  have e1 : E ^ (q * (1 + σw)) / E ^ (1 + ocGamma α q / 2) =
      E ^ (q * ocGamma α q + 4 * ocDelta α q + q * σw) := by
    rw [hww]; congr 1; rw [hcdef] at hid; linarith [hid]
  rw [e1] at hq1
  -- (2)
  have hn2 : cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * E ^ tT ≤
      Cρ * E ^ ((1 + ocC α q) + tT) := by
    rw [Real.rpow_add hE0.1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hρ.2 (hEn _)
  have hq2 := quotient_upper_bound hCρp hinvp (hEn ((1 + ocC α q) + tT))
    (Real.rpow_pos_of_pos hE0.1 (1 + ocGamma α q / 2)) hρs0 hn2 hρs
  have e2 : E ^ ((1 + ocC α q) + tT) / E ^ (1 + ocGamma α q / 2) =
      E ^ (ocDelta α q + tT) := by
    rw [hww]; congr 1; rw [hcdef]; ring
  rw [e2] at hq2
  -- (3)
  have hEq : E ^ (q * (1 + σw)) ≤ K1 ^ (q * (1 + σw)) * Y ^ (q * (q * (1 + σw))) :=
    pow_bound hY0.1.le hK1p.le hE0.1.le hEY (mul_nonneg (by linarith [hq.1]) (by linarith))
  have hn3 : x ^ (1 + σw) ≤
      (K1 ^ (1 + σw) * K1 ^ (q * (1 + σw))) * Y ^ (q * (q * (1 + σw))) := by
    rw [mul_assoc]
    exact hxσ.trans (mul_le_mul_of_nonneg_left hEq hp1.le)
  have hq3 := quotient_upper_bound (by positivity) hCρp (hYn (q * (q * (1 + σw))))
    (Real.rpow_pos_of_pos hY0.1 (1 + ocC α q)) hρpos hn3 hρn.1
  have e3 : Y ^ (q * (q * (1 + σw))) / Y ^ (1 + ocC α q) =
      Y ^ (q ^ 2 * (1 + σw) - 1 - ocC α q) := by
    rw [← Real.rpow_sub hY0.1]; congr 1; ring
  rw [e3] at hq3
  -- (4)
  have hEr : E ^ ((1 + ocC α q) + tT) ≤
      K1 ^ ((1 + ocC α q) + tT) * Y ^ (q * ((1 + ocC α q) + tT)) :=
    pow_bound hY0.1.le hK1p.le hE0.1.le hEY (by rw [hcdef]; linarith)
  have hn4 : cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * E ^ tT ≤
      (Cρ * K1 ^ ((1 + ocC α q) + tT)) * Y ^ (q * ((1 + ocC α q) + tT)) := by
    exact hn2.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hEr hCρp.le)
  have hq4 := quotient_upper_bound (by positivity) hCρp (hYn (q * ((1 + ocC α q) + tT)))
    (Real.rpow_pos_of_pos hY0.1 (1 + ocC α q)) hρpos hn4 hρn.1
  have e4 : Y ^ (q * ((1 + ocC α q) + tT)) / Y ^ (1 + ocC α q) =
      Y ^ (q * (1 + ocC α q + tT) - 1 - ocC α q) := by
    rw [← Real.rpow_sub hY0.1]; congr 1; ring
  rw [e4] at hq4
  refine ⟨hq1.trans ?_, hq2.trans ?_, hq3.trans ?_, hq4.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hEn _)
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hEn _)
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hYn _)
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hYn _)


end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The enhanced radius is small relative to the parent wavelength, uniformly over band chains. -/
@[expose] public section
open Homogenization AVenhance Filter Topology
open AVRegularity.CycleReference AVRegularity.EntryScales
namespace AVRegularity.Construction.Preservation.FullLift

theorem enhanced_radius_parent_ratio {E ρ C c : ℝ}
    (hE : 0 < E) (hbound : ρ ≤ C * E ^ (1 + c)) :
    ρ / E ≤ C * E ^ c := by
  apply (div_le_div_of_nonneg_right hbound hE.le).trans_eq
  rw [mul_div_assoc]
  calc
    _ = C * (E ^ (1 + c) / E ^ (1 : ℝ)) :=
      congrArg (fun z => C * (E ^ (1 + c) / z)) (Real.rpow_one E).symm
    _ = C * E ^ c := by
      rw [← Real.rpow_sub hE]
      congr 2
      ring

theorem band_enhanced_radius_parent_price {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, 2 ≤ m → m ≤ M →
        (cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) / ocEpsilon q Λ (m - 1) ≤
          C * ocEpsilon q Λ (m - 1) ^ ocC α q := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Li, hLi, ?_⟩
  intro Λ hΛ cr hcr
  have hCip : 0 < Ci := lt_of_lt_of_le (by norm_num) hCi
  let C := Real.sqrt (Ci * 2 ^ (26 : ℕ)) * max cr cr⁻¹
  have hC : 0 < C := mul_pos (Real.sqrt_pos.2 (mul_pos hCip (by positivity)))
    (lt_max_of_lt_left hcr)
  refine ⟨C, hC, ?_⟩
  intro M κ hκ m hm hmM
  have h128 := hLi.trans hΛ
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hband := hi Λ hΛ M (by omega) κ hκ (m - 1) (by omega) (by omega)
  have htime := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)
  have hrho := rho_asymp hE hCip (by positivity) hcr hband htime
  exact enhanced_radius_parent_ratio hE hrho.2

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Time continuity of the literal flow derivative and of its products with fixed matrices. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem flow_spatial_derivative_time_continuous (D : OCData) (b : ℕ) (s : ℝ) (x : Vec 2) :
    Continuous (fun t => fderiv ℝ (fun y => D.flowOf b t y s) x) := by
  let F : ℝ × Vec 2 → Vec 2 := fun tx => D.flowOf b tx.1 tx.2 s
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ b)).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  change Continuous (fun t => fderiv ℝ (fun y => F (t, y)) x)
  exact (Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff F hF).continuous.comp
    (continuous_id.prodMk continuous_const)

theorem jacMatrix_mul_toContinuousLinearMap (f : Vec 2 → Vec 2) (y : Vec 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.toLin' (jacMatrix f y * A)).toContinuousLinearMap =
      (fderiv ℝ f y).comp (Matrix.toLin' A).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLin' (jacMatrix f y * A) x = fderiv ℝ f y (Matrix.toLin' A x)
  rw [Matrix.toLin'_mul_apply]
  exact congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (Matrix.toLin' A x))
    (jacMatrix_toContinuousLinearMap f y)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Measurability of the actual fresh axes on their countable quiet margin partition. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

def freshQuietMarginIndex (D : OCData) (b : ℕ) (t : ℝ) : ℤ :=
  ⌊t / ocTauPP D.α D.q D.Λ (b + 1) - 1 / 2⌋

theorem freshQuietMarginIndex_measurable (D : OCData) (b : ℕ) :
    Measurable (freshQuietMarginIndex D b) :=
  ((measurable_id.div_const _).sub_const _).floor

theorem freshQuietMarginIndex_mem (D : OCData) (b : ℕ) (hΛ : 1 ≤ D.Λ) (t : ℝ) :
    t ∈ Set.Ico
      ((((freshQuietMarginIndex D b t : ℤ) : ℝ) + 1 / 2) *
        ocTauPP D.α D.q D.Λ (b + 1))
      ((((freshQuietMarginIndex D b t : ℤ) : ℝ) + 3 / 2) *
        ocTauPP D.α D.q D.Λ (b + 1)) := by
  let h := ocTauPP D.α D.q D.Λ (b + 1)
  have hh : 0 < h := Stream.ocTauPP_pos hΛ
  constructor
  · have hf := Int.floor_le (t / h - 1 / 2)
    have he : (⌊t / h - 1 / 2⌋ : ℝ) + 1 / 2 ≤ t / h := by linarith
    exact (le_div_iff₀ hh).mp he
  · have hf := Int.lt_floor_add_one (t / h - 1 / 2)
    have he : t / h < (⌊t / h - 1 / 2⌋ : ℝ) + 3 / 2 := by linarith
    exact (div_lt_iff₀ hh).mp he

theorem fresh_axes_measurable (D : OCData) (b : ℕ) (hΛ : 1 ≤ D.Λ)
    (H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2) (haxes : IsFreshAxes D b H₁ H₂) :
    Measurable H₁ ∧ Measurable H₂ := by
  choose tH tV lH lV hsample hmat using haxes
  let s : ℤ → ℝ := fun l => ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)
  let F : ℤ × ℝ → (Vec 2 →L[ℝ] Vec 2) × (Vec 2 →L[ℝ] Vec 2) := fun lt =>
    ((fderiv ℝ (fun y => D.flowOf b lt.2 y (s lt.1)) 0).comp
      (Matrix.toLin' (sampledEllipse D b (s lt.1) (tH lt.1) (lH lt.1))).toContinuousLinearMap,
     (fderiv ℝ (fun y => D.flowOf b lt.2 y (s lt.1)) 0).comp
      (Matrix.toLin' (sampledEllipse D b (s lt.1) (tV lt.1) (lV lt.1))).toContinuousLinearMap)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro l
    change Measurable (fun t =>
      ((fderiv ℝ (fun y => D.flowOf b t y (s l)) 0).comp
        (Matrix.toLin' (sampledEllipse D b (s l) (tH l) (lH l))).toContinuousLinearMap,
       (fderiv ℝ (fun y => D.flowOf b t y (s l)) 0).comp
        (Matrix.toLin' (sampledEllipse D b (s l) (tV l) (lV l))).toContinuousLinearMap))
    exact (((flow_spatial_derivative_time_continuous D b (s l) 0).clm_comp
      (continuous_const : Continuous (fun _ : ℝ =>
        (Matrix.toLin' (sampledEllipse D b (s l) (tH l) (lH l))).toContinuousLinearMap))).prodMk
      ((flow_spatial_derivative_time_continuous D b (s l) 0).clm_comp
      (continuous_const : Continuous (fun _ : ℝ =>
        (Matrix.toLin' (sampledEllipse D b (s l) (tV l) (lV l))).toContinuousLinearMap)))).measurable
  have hpair : (fun t => (H₁ t, H₂ t)) =
      (fun t => F (freshQuietMarginIndex D b t, t)) := by
    funext t
    obtain ⟨h₁, h₂⟩ := hmat (freshQuietMarginIndex D b t) t (freshQuietMarginIndex_mem D b hΛ t)
    rw [h₁, h₂, jacMatrix_mul_toContinuousLinearMap, jacMatrix_mul_toContinuousLinearMap]
  have hm : Measurable (fun t => (H₁ t, H₂ t)) := by
    rw [hpair]
    exact hF.comp ((freshQuietMarginIndex_measurable D b).prodMk measurable_id)
  exact ⟨hm.fst, hm.snd⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The actual cell length fits the enhanced preparation radius at a uniform deep-level threshold. -/
@[expose] public section
open Filter Topology
open AVRegularity.CycleReference
namespace AVRegularity.Construction.Preservation.FullLift

theorem band_enhanced_cell_ratio_eventually_small {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr →
      ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m ≤ M →
        ocDStar q Λ m (κ m) (κ (m - 1)) /
          (cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) ≤ 1 := by
  obtain ⟨C, _hC, Λ₀, hΛ₀, hcell⟩ :=
    bandChain_prepared_cell_length hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ cr hcr
  have hδ := (Scales.admissible_delta_mu_positive hα0 hα1 hs0 hs1 hq).1
  have hlim : Tendsto (fun m : ℕ => (C / cr) *
      ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (Buffer.preparation_parent_power_tendsto_zero hq.1 (hΛ₀.trans hΛ)
        (mul_pos (by norm_num) hδ))
  obtain ⟨n, hn⟩ := eventually_atTop.1
    (hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  intro M κ hκ m hm hmM
  have hm2 : 2 ≤ m := (le_max_left 2 n).trans hm
  have hb := (hcell Λ hΛ M (by omega) κ hκ m hm2 hmM).2.1
  calc
    _ = (ocDStar q Λ m (κ m) (κ (m - 1)) /
        ocRh α q Λ m (κ (m - 1))) / cr := by unfold ocRh; ring
    _ ≤ (C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q)) / cr :=
      div_le_div_of_nonneg_right hb hcr.le
    _ = (C / cr) * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) := by ring
    _ ≤ 1 := hn m ((le_max_right 2 n).trans hm)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Lowering the represented order preserves the certified kernel Schur budget. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]


theorem kernelSchurMatrix_order_mono {a b R ν : ℝ} {L K D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν K D (h := h) (Γ := Γ) (G := G))
    (hLK : L ≤ K) (i j : ι) :
    kernelSchurMatrix ν R P.π L D a b P.c P.r P.C P.B i j ≤
      kernelSchurMatrix ν R P.π K D a b P.c P.r P.C P.B i j := by
  unfold kernelSchurMatrix
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Finset.sum_le_sum
  intro α _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro d _
  have hc : 0 ≤ P.c (d.1 - 2) := (P.hS i j α).2.2.1 _
    (by have hd := Finset.mem_Icc.mp d.property; omega)
  apply div_le_div_of_nonneg_right _
    (mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr i j α).le _))
  apply mul_le_mul_of_nonneg_right _ hc
  exact ENNReal.toReal_mono (P.hB_fin i j α d)
    (coefficientSeminorm_order_mono R hLK a b (P.B i j α d))

theorem kernelSchurBound_order_mono {a b R ν : ℝ} {L K D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν K D (h := h) (Γ := Γ) (G := G))
    (hLK : L ≤ K) :
    SchurBound P.θ (kernelSchurMatrix ν R P.π L D a b P.c P.r P.C P.B) := by
  constructor
  · intro i
    exact (Finset.sum_le_sum fun j _ => kernelSchurMatrix_order_mono P hLK i j).trans
      (P.hschur.1 i)
  · intro j
    exact (Finset.sum_le_sum fun i _ => kernelSchurMatrix_order_mono P hLK i j).trans
      (P.hschur.2 j)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Restrict the represented order without changing the actual kernel operator data. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]



def kernelOperator_order_restrict {a b R ν : ℝ} {l k D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν k D (h := h) (Γ := Γ) (G := G))
    (hlk : l ≤ k)
    (hS : ∀ i j α, IsSpatialRegularizerTorus R l D a b P.c (P.r i j α) (P.S i j α)) :
    KernelEnergy.TorusKernelOperator a b R ν l D (h := h) (Γ := Γ) (G := G) where
  htime := P.htime
  radius_pos := P.radius_pos
  diffusivity_pos := P.diffusivity_pos
  order_ge_two := P.order_ge_two
  π := P.π
  hπ := P.hπ
  B := P.B
  hB_meas := P.hB_meas
  hB_smooth := fun i j α d t ht => (P.hB_smooth i j α d t ht).of_le
    (by exact_mod_cast hlk)
  hB_per := P.hB_per
  hB_fin := fun i j α d => ne_top_of_le_ne_top (P.hB_fin i j α d)
    (coefficientSeminorm_order_mono R hlk a b (P.B i j α d))
  C := P.C
  S := P.S
  c := P.c
  r := P.r
  hr := P.hr
  hS := hS
  θ := P.θ
  hθ := P.hθ
  hschur := kernelSchurBound_order_mono P hlk

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open Homogenization Filter Topology
namespace AVRegularity.Construction.Preservation.FullLift

/-! The passage enhanced radius eventually lies below the parent's molecular radius uniformly in the band chain. -/

theorem uniform_enhanced_radius_le_parent_molecular {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (c₀ cr : ℝ), 0 < c₀ → 0 < cr →
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ m : ℕ, m₀ ≤ m → m ≤ D.term → rhoEnh D cr m ≤ rhoStar D c₀ (m - 1) := by
  obtain ⟨Λ₀, hΛ₀, hratio⟩ := band_enhanced_radius_parent_price hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ c₀ cr hc₀ hcr
  have h128 := hΛ₀.trans hΛ
  obtain ⟨C, _hC, hCratio⟩ := hratio Λ hΛ (cr / c₀) (div_pos hcr hc₀)
  have hc : 0 < ocC α q := by
    simpa only [ocC, Scales.ocC] using
      (Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.2.2.2.2
  have hpow := Buffer.preparation_parent_power_tendsto_zero hq.1 h128 hc
  have hlim : Tendsto (fun m : ℕ => C * ocEpsilon q Λ (m - 1) ^ ocC α q) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  obtain ⟨nr, hnr⟩ := eventually_atTop.1
    (hlim.eventually (eventually_le_nhds zero_lt_one))
  obtain ⟨ns, hns, hstrain⟩ := parent_drift_time_eventually_small hα0 hα1 hs0 hs1 hq h128
    ((cr / c₀) ^ 2) (sq_nonneg _) 1 zero_lt_one
  refine ⟨max nr ns, by omega, ?_⟩
  intro D hDα hDq hDΛ hDζ hband m hm hmterm
  have hband' : IsOCBandChain α q Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hband
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos (by omega)
  have hB : 0 ≤ D.κ (m - 1) :=
    (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hband'
      ((Nat.sub_le m 1).trans hmterm)).le
  have hτ : 0 ≤ ocTauPP α q Λ m := (Construction.Stream.ocTauPP_pos (by omega)).le
  have ha : 0 < ocA α q Λ (m - 1) := Real.rpow_pos_of_pos hE _
  have hEp : (cr / c₀) * Real.sqrt (D.κ (m - 1) * ocTauPP α q Λ m) ≤
      ocEpsilon q Λ (m - 1) := by
    apply (div_le_one hE).mp
    exact (hCratio D.term D.κ hband' m (by omega) hmterm).trans (hnr m (by omega))
  have hh := enhanced_radius_le_molecular_of_prices hB hτ ha hc₀ hEp (hstrain m (by omega))
  simpa only [rhoEnh, rhoStar, OCData.eps, hDα, hDq, hDΛ] using hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Actual covariance images inherit time measurability from the continuous adjoint. -/

open CycleComparison.Coarse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covImage_aestronglyMeasurable {K p : ℕ} (a b : ℝ)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) (Set.Icc a b))
    (Z : ℝ → TorusHk (K + 2 * p) E) (W : ℝ → TorusHk K E)
    (hZ : AEStronglyMeasurable Z (volume.restrict (Set.Icc a b)))
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), IsCovImage (covPolyP (Hc t) p) (Z t) (W t)) :
    AEStronglyMeasurable W (volume.restrict (Set.Icc a b)) := by
  let : NormedAddCommGroup (TorusHk (K + 2 * p) E) := inferInstance
  let : NormedAddCommGroup (TorusHk K E) := inferInstance
  let : NormedSpace ℝ (TorusHk (K + 2 * p) E) := inferInstance
  let : NormedSpace ℝ (TorusHk K E) := inferInstance
  let A := fun t => (TorusAdj.covPolyP (E := E) (Hc t) le_rfl p 0 (K + 2 * p)).adj K le_rfl
  have hA : ContinuousOn A (Set.Icc a b) :=
    CycleComparison.Reconstruction.covPolyP_adj_continuousOn Hc (fun t => covBound (Hc t))
      (fun _ => le_rfl) hH p 0 (K + 2 * p) K le_rfl
  have hAm := hA.aestronglyMeasurable_of_isCompact (μ := volume) isCompact_Icc measurableSet_Icc
  have hm : AEStronglyMeasurable (fun t => A t (Z t)) (volume.restrict (Set.Icc a b)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hAm.prodMk hZ)
  apply hm.congr
  filter_upwards [hW] with t ht
  apply (covImage_unique (covPolyP (Hc t) p) (Z t) _ _ ?_ ht)
  intro ψ hψ hp
  exact (TorusAdj.covPolyP (E := E) (Hc t) le_rfl p 0 (K + 2 * p)).ident K le_rfl
    (Z t) ψ (hψ.of_le (by exact_mod_cast le_top)) hp

theorem covImage_aestronglyMeasurable_of_reserve {K L p : ℕ} (hKL : K + 2 * p ≤ L)
    (a b : ℝ) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) (Set.Icc a b))
    (Z : ℝ → TorusHk L E) (W : ℝ → TorusHk K E)
    (hZ : AEStronglyMeasurable Z (volume.restrict (Set.Icc a b)))
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), IsCovImage (covPolyP (Hc t) p) (Z t) (W t)) :
    AEStronglyMeasurable W (volume.restrict (Set.Icc a b)) := by
  apply covImage_aestronglyMeasurable a b Hc hH
    (fun t => truncateTorusHk hKL (Z t)) W
    ((truncateTorusHk hKL).continuous.comp_aestronglyMeasurable hZ)
  filter_upwards [hW] with t ht
  intro ψ hψ hp
  have hi := ht ψ hψ hp
  change cellInner (tval (W t)) ψ = cellInner (tval (Z t)) (covPolyP (Hc t) p ψ) at hi
  change cellInner (tval (W t)) ψ = cellInner (tval (truncateTorusHk hKL (Z t)))
    (covPolyP (Hc t) p ψ)
  simpa only [tval_truncateTorusHk] using hi

end AVRegularity.Construction.Preservation.FullLift
end
end
