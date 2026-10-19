-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeDifferentialOperators
import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
import AVRegularity.CycleWords.CellTransitionLipschitz
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeTimeReadout
public import AVRegularity.EntryWeak.IndependentParameterNormContinuity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-! Reserved Sobolev time curves have one classical derivative field and pointwise
primitives for every permitted spatial word. All constructions are independent of a menu. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Spatial jets of a smooth chart remain jointly smooth in time and the label. -/
theorem native_smooth_chart_spatial_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : ℝ → Vec 2 → V) (hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ)) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => iteratedFDeriv ℝ n (Φ p.1) p.2) := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (continuousMultilinearCurryFin0 ℝ (Vec 2) V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hΦ
  | succ n ih =>
    have hi : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × Vec 2) × Vec 2 =>
        iteratedFDeriv ℝ n (Φ p.1.1) p.2) :=
      ih.comp ((contDiff_fst.fst).prodMk contDiff_snd)
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
        fderiv ℝ (fun x => iteratedFDeriv ℝ n (Φ p.1) x) p.2) :=
      hi.fderiv contDiff_snd (by simp)
    have hc := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + 1) => Vec 2) V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hd
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hc

/-- A smooth chart has one finite bound for its finitely many spatial jets on
any compact moving label set and compact time window. -/
theorem native_smooth_chart_compact_jet_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : ℝ → Vec 2 → V) (hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ))
    (label : ℝ → Vec 2 → Vec 2)
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (a b : ℝ) (K : Set (Vec 2)) (hK : IsCompact K) (R : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n ≤ R, ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (Φ t) (label t x)‖ ≤ B := by
  classical
  have hc (n : ℕ) : Continuous (fun Z : ℝ × Vec 2 =>
      iteratedFDeriv ℝ n (Φ Z.1) (label Z.1 Z.2)) :=
    (native_smooth_chart_spatial_jet Φ hΦ n).continuous.comp
      (continuous_fst.prodMk hlabel.continuous)
  choose C hC using fun n => (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hc n).continuousOn
  let B := 1 + ∑ n ∈ Finset.range (R + 1), |C n|
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => abs_nonneg (C n)))
  refine ⟨B, hB, fun n hn t ht x hx => ?_⟩
  have hs : |C n| ≤ ∑ j ∈ Finset.range (R + 1), |C j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_range.mpr (by omega))
  exact (hC n (t, x) ⟨ht, hx⟩).trans ((le_abs_self (C n)).trans (hs.trans (by dsimp [B]; linarith)))

/-- A fixed bilinear operation preserves finite uniform spatial jet budgets on
a compact label set. Both factor budgets precede the time and spatial points. -/
theorem native_uniform_bilinear_jet_bound
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : V →L[ℝ] W →L[ℝ] Z) {a b : ℝ} (R : ℕ) (K : Set (Vec 2))
    (f : ℝ → Vec 2 → V) (g : ℝ → Vec 2 → W)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ (R : ℕ∞) (f t))
    (hg : ∀ t ∈ Icc a b, ContDiff ℝ (R : ℕ∞) (g t))
    (hfb : ∀ k ≤ R, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (f t) x‖ ≤ B)
    (hgb : ∀ k ≤ R, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (g t) x‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ R (fun y => L (f t y) (g t y)) x‖ ≤ B := by
  classical
  choose C hC hc using fun k : Fin (R + 1) => hfb k.1 (by omega)
  choose D hD hd using fun k : Fin (R + 1) => hgb k.1 (by omega)
  let Csum := ∑ k : Fin (R + 1), C k
  let Dsum := ∑ k : Fin (R + 1), D k
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun k _ => hC k)
  have hDsum : 0 ≤ Dsum := Finset.sum_nonneg (fun k _ => hD k)
  let B := ‖L‖ * ∑ k ∈ Finset.range (R + 1), (R.choose k : ℝ) * Csum * Dsum
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg L) (Finset.sum_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCsum) hDsum))
  refine ⟨B, hB, fun t ht x hx => ?_⟩
  apply (L.norm_iteratedFDeriv_le_of_bilinear (hf t ht) (hg t ht) x (by simp)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
  apply Finset.sum_le_sum
  intro k hk
  have hkR : k < R + 1 := Finset.mem_range.mp hk
  have hcf := (hc ⟨k, hkR⟩ t ht x hx).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))
  have hcg := (hd ⟨R - k, by omega⟩ t ht x hx).trans
    (Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ _))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hcf (Nat.cast_nonneg _))
    hcg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hCsum)

/-- Finite sums preserve uniform spatial jet budgets with all constants chosen
before time and space. -/
theorem native_uniform_finset_jet_bound
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} (R : ℕ) (K : Set (Vec 2)) (s : Finset ι) (f : ι → ℝ → Vec 2 → V)
    (hf : ∀ i ∈ s, ∀ t ∈ Icc a b, ContDiff ℝ (R : ℕ∞) (f i t))
    (hb : ∀ i ∈ s, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ R (f i t) x‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ R (fun y => ∑ i ∈ s, f i t y) x‖ ≤ B := by
  classical
  choose C hC hc using fun i : s => hb i.1 i.2
  let B := ∑ i ∈ s, if hi : i ∈ s then C ⟨i, hi⟩ else 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by
    simp only [dite_eq_left hi]
    exact hC ⟨i, hi⟩)
  refine ⟨B, hB, fun t ht x hx => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hf i hi t ht).contDiffAt)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [dite_eq_left hi]
  exact hc ⟨i, hi⟩ t ht x hx

/-- Spatial smoothness and a finite uniform highest-jet budget on a compact
label set. Time is only a parameter in this static estimate. -/
structure NativeCompactSpatialBudget {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b : ℝ) (R : ℕ) (X : Set (Vec 2)) (f : ℝ → Vec 2 → V) : Prop where
  smooth : ∀ t ∈ Icc a b, ContDiff ℝ (R : ℕ∞) (f t)
  bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ X,
    ‖iteratedFDeriv ℝ R (f t) x‖ ≤ B

/-- The spatial budgets of a finite sum are chosen before time and labels. -/
theorem NativeCompactSpatialBudget.sum
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {R : ℕ} {X : Set (Vec 2)} (s : Finset ι) (f : ι → ℝ → Vec 2 → V)
    (Q : ∀ i ∈ s, NativeCompactSpatialBudget a b R X (f i)) :
    NativeCompactSpatialBudget a b R X (fun t x => ∑ i ∈ s, f i t x) := by
  refine ⟨fun t ht => ContDiff.sum (fun i hi => (Q i hi).smooth t ht), ?_⟩
  exact native_uniform_finset_jet_bound R X s f
    (fun i hi => (Q i hi).smooth) (fun i hi => (Q i hi).bound)

/-- A fixed scalar preserves the same compact spatial reserve. -/
theorem NativeCompactSpatialBudget.const_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {R : ℕ} {X : Set (Vec 2)} {f : ℝ → Vec 2 → V}
    (Q : NativeCompactSpatialBudget a b R X f) (c : ℝ) :
    NativeCompactSpatialBudget a b R X (fun t x => c • f t x) := by
  refine ⟨fun t ht => (Q.smooth t ht).const_smul c, ?_⟩
  obtain ⟨B, hB, hb⟩ := Q.bound
  refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun t ht x hx => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' (Q.smooth t ht).contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (hb t ht x hx) (norm_nonneg c)

/-- Finite addition preserves compact spatial budgets at the same reserve. -/
theorem NativeCompactSpatialBudget.add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {R : ℕ} {X : Set (Vec 2)} {f g : ℝ → Vec 2 → V}
    (Qf : NativeCompactSpatialBudget a b R X f)
    (Qg : NativeCompactSpatialBudget a b R X g) :
    NativeCompactSpatialBudget a b R X (fun t x => f t x + g t x) := by
  refine ⟨fun t ht => (Qf.smooth t ht).add (Qg.smooth t ht), ?_⟩
  obtain ⟨Bf, hBf, hf⟩ := Qf.bound
  obtain ⟨Bg, hBg, hg⟩ := Qg.bound
  refine ⟨Bf + Bg, add_nonneg hBf hBg, fun t ht x hx => ?_⟩
  rw [show (fun y => f t y + g t y) = f t + g t by
    funext y
    simp only [Pi.add_apply], iteratedFDeriv_add_apply (Qf.smooth t ht).contDiffAt (Qg.smooth t ht).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf t ht x hx) (hg t ht x hx))

/-- Only literal values on the time window enter a compact spatial budget. -/
theorem NativeCompactSpatialBudget.congr_window
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {R : ℕ} {X : Set (Vec 2)} {f g : ℝ → Vec 2 → V}
    (Q : NativeCompactSpatialBudget a b R X f)
    (he : ∀ t ∈ Icc a b, ∀ x, f t x = g t x) :
    NativeCompactSpatialBudget a b R X g := by
  have hf (t : ℝ) (ht : t ∈ Icc a b) : f t = g t := funext (he t ht)
  refine ⟨fun t ht => hf t ht ▸ Q.smooth t ht, ?_⟩
  obtain ⟨B, hB, hb⟩ := Q.bound
  exact ⟨B, hB, fun t ht x hx => hf t ht ▸ hb t ht x hx⟩

/-- Uniform spatial budgets and separate time continuity produce the literal
joint measurability and time-integrable budgets of a periodic window field. -/
theorem native_classical_window_bound_of_uniform_jets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V}
    (Q : ∀ n ≤ K, NativeCompactSpatialBudget a b n AVenhance.unitCube f)
    (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (f t))
    (htime : ∀ x, ContinuousOn (fun t => f t x) (Icc a b)) :
    ClassicalWindowBound a b K f := by
  refine ⟨fun t ht => ((Q K le_rfl).smooth t ht).of_le (by simp), hp, ?_, ?_⟩
  · have hm (x : Vec 2) : Measurable (fun t : Icc a b => f t x) :=
      (continuousOn_iff_continuous_domRestrict.mp (htime x)).measurable
    have hj := (measurable_uncurry_of_continuous_of_measurable
      (fun t : Icc a b => ((Q K le_rfl).smooth t t.2).continuous) hm).comp measurable_swap
    exact hj.comp (((measurable_fst.comp measurable_subtype_coe).subtype_mk
      (h := fun z => z.2)).prodMk (measurable_snd.comp measurable_subtype_coe))
  · intro n hn w
    obtain ⟨B, _hB, hb⟩ := (Q n hn).bound
    refine ⟨fun _ => B, integrableOn_const isCompact_Icc.measure_ne_top, fun t ht x hx => ?_⟩
    exact (ChartTransport.norm_orderedDerivative_le ((Q n hn).smooth t ht) w x).trans (hb t ht x hx)

/-- All local coefficient reserves control their literal sampling in a smooth
physical chart, uniformly on each compact spatial set. No time smoothness of the
coefficient is required. -/
theorem native_local_reserve_sample_jet_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} {f : ℝ → Vec 2 → Vec 2 → V} (R : ℕ)
    (hmodel : ∀ Y : Vec 2, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z)
    (Γ : ℝ → Vec 2 → Vec 2 × Vec 2)
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ))
    (K : Set (Vec 2)) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ R (fun y => f t (Γ t y).1 (Γ t y).2) x‖ ≤ B := by
  classical
  let L := (fun p : ℝ × Vec 2 => (Γ p.1 p.2).2) '' (Icc a b ×ˢ K)
  have hL : IsCompact L := (isCompact_Icc.prod hK).image (continuous_snd.comp hΓ.continuous)
  obtain ⟨hf, hbounds⟩ := native_local_reserve_joint_data (Ω := univ) R f
    (fun Y _ => hmodel Y)
  choose C hC hb using fun n : Fin (R + 1) =>
    hbounds n.1 (by omega) L hL (subset_univ _)
  let Csum := ∑ n : Fin (R + 1), C n
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun n _ => hC n)
  obtain ⟨D, hD, hd⟩ := native_smooth_chart_compact_jet_bounds Γ hΓ
    (fun _ x => x) contDiff_snd a b K hK R
  refine ⟨(R.factorial : ℝ) * Csum * D ^ R,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCsum) (pow_nonneg (le_trans zero_le_one hD) _), ?_⟩
  intro t ht x hx
  have hft : ContDiff ℝ (R : ℕ∞) (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) := by
    have hh := hf t ht
    rw [univ_prod_univ] at hh
    exact contDiffOn_univ.mp hh
  have hΓt : ContDiff ℝ (R : ℕ∞) (Γ t) :=
    (hΓ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  apply norm_iteratedFDeriv_comp_le hft hΓt (by simp) x
  · intro n hn
    have hy : (Γ t x).2 ∈ L := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    exact (hb ⟨n, by omega⟩ t ht (Γ t x).2 hy (Γ t x).1).trans
      (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))
  · intro n hn hnR
    exact (hd n hnR t ht x hx).trans (le_self_pow₀ hD (by omega))

/-- The Faà di Bruno chart factor is a smooth operator on the full prepared
jet. The time coordinate remains outside the prepared field. -/
theorem native_pullback_word_smooth_operator
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (w : DerivativeWord2 n) (c : OrderedFinpartition n)
    (Φ Ψ : ℝ → Vec 2 → Vec 2)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ))
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Ψ)) :
    ∃ L : ℝ → Vec 2 →
        ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) V →L[ℝ] V,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry L) ∧
      ∀ t x A,
        L t x A = (c.compAlongOrderedFinpartition A
          (fun i => iteratedFDeriv ℝ (c.partSize i) (Φ t) (Ψ t x)))
          (fun i => basisVec (w (Fin.rev i))) := by
  let B := fun p : ℝ × Vec 2 => fun i : Fin c.length =>
    iteratedFDeriv ℝ (c.partSize i) (Φ p.1) (Ψ p.1 p.2)
  let J := c.compAlongOrderedFinpartitionL ℝ (Vec 2) (Vec 2) V
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) V
    (fun i => basisVec (w (Fin.rev i)))
  let L := fun t x => E.comp (J.flipMultilinear (B (t, x)))
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := contDiff_pi.mpr (fun i =>
    (native_smooth_chart_spatial_jet Φ hΦ (c.partSize i)).comp
      (contDiff_fst.prodMk hΨ))
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J.flipMultilinear :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (E := fun i : Fin c.length => ContinuousMultilinearMap ℝ
        (fun _ : Fin (c.partSize i) => Vec 2) (Vec 2))
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) V →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V)
      (f := J.flipMultilinear)
  refine ⟨L, contDiff_const.clm_comp (hJ.comp hB), ?_⟩
  intro t x A
  rfl

/-- A smooth chart factor has a smooth literal time derivative at every point. -/
theorem native_smooth_time_partial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : ℝ → Vec 2 → V) (hL : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry L)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => deriv (fun t => L t p.2) p.1) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      fderiv ℝ (Function.uncurry L) p (1, 0)) :=
    (hL.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry L) p (1, 0)) =
      fun p => deriv (fun t => L t p.2) p.1 := by
    funext p
    have hh := ((hL.differentiable (by simp) p).hasFDerivAt).comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    exact hh.deriv.symm
  rw [he] at hd
  exact hd

/-- Finite spatial smoothness suffices for the chart word expansion. The formula
keeps the prepared jets multilinear, so it applies to every Hilbert root. -/
theorem native_pullback_word_eq_faa
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (w : DerivativeWord2 n) (f : Vec 2 → V) (Φ : Vec 2 → Vec 2)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hΦ : ContDiff ℝ (n : ℕ∞) Φ) (x : Vec 2) :
    orderedDerivative w (f ∘ Φ) x = ∑ c : OrderedFinpartition n,
      (c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f (Φ x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) Φ x))
        (fun i => basisVec (w (Fin.rev i))) := by
  simp only [orderedDerivative_eq_iteratedFDeriv w (hf.comp hΦ)]
  rw [iteratedFDeriv_comp hf.contDiffAt hΦ.contDiffAt le_rfl]
  simp only [FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The bounded evaluation map itself supplies the canonical classical representative. -/
theorem native_classical_evaluation_rep {K r : ℕ} (hKr : r + 2 ≤ K) (U : TorusHk K E) :
    IsClassicalRep U (fun x => nativeClassicalEvaluationCLM K (by omega) x U) r := by
  obtain ⟨f, hf⟩ := hilbert_classicalRep_exists K r hKr U
  have he : (fun x => nativeClassicalEvaluationCLM K (by omega) x U) = f :=
    funext fun x => nativeClassicalEvaluationCLM_rep (by omega) U f hf x
  rw [he]
  exact hf

/-- Canonical values of a strongly measurable native curve are jointly measurable. -/
theorem native_classical_evaluation_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    {K : ℕ} (hK : 2 ≤ K) (U : T → TorusHk K E) (hU : StronglyMeasurable U) :
    StronglyMeasurable (fun p : T × Vec 2 => nativeClassicalEvaluationCLM K hK p.2 (U p.1)) := by
  have hc (t : T) : Continuous (fun x => nativeClassicalEvaluationCLM K hK x (U t)) :=
    (native_classical_evaluation_rep (K := K) (r := 0) hK (U t)).2.1.continuous
  have hm (x : Vec 2) : StronglyMeasurable (fun t => nativeClassicalEvaluationCLM K hK x (U t)) :=
    (nativeClassicalEvaluationCLM (E := E) K hK x).continuous.comp_stronglyMeasurable hU
  have hj : StronglyMeasurable (fun p : Vec 2 × T =>
      nativeClassicalEvaluationCLM (E := E) K hK p.1 (U p.2)) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun x t => nativeClassicalEvaluationCLM (E := E) K hK x (U t)) hc hm
  have hj' : StronglyMeasurable ((fun p : Vec 2 × T =>
      nativeClassicalEvaluationCLM (E := E) K hK p.1 (U p.2)) ∘
      (Prod.swap : T × Vec 2 → Vec 2 × T)) :=
    hj.comp_measurable (measurable_swap (α := T) (β := Vec 2))
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using hj'

/-- Native evaluation has a uniform bound, independent of the point of the torus. -/
theorem native_classical_evaluation_uniform_bound (K : ℕ) (hK : 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec 2) (U : TorusHk K E),
      ‖nativeClassicalEvaluationCLM K hK x U‖ ≤ C * ‖U‖ := by
  classical
  let e := stdOrthonormalBasis ℝ E
  let L := fun i : Fin (Module.finrank ℝ E) =>
    CoupledEnergy.Variational.mapTorusHkCLM K (InnerProductSpace.toDual ℝ E (e i))
  let C := ∑ i, EntryWeakProofs.classicalSobolevConstant 0 * ‖L i‖ * ‖e i‖
  have hC0 : 0 ≤ EntryWeakProofs.classicalSobolevConstant 0 := by
    unfold EntryWeakProofs.classicalSobolevConstant
    positivity
  refine ⟨C, Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg hC0 (norm_nonneg (L _))) (norm_nonneg (e _))), fun x U => ?_⟩
  have hb (i : Fin (Module.finrank ℝ E)) :
      ‖CycleWords.realClassicalEvaluationCLM K hK x (L i U)‖ ≤
        EntryWeakProofs.classicalSobolevConstant 0 * ‖L i‖ * ‖U‖ := by
    have h := EntryWeakProofs.realClassicalLift_derivative_norm_le K (L i U) 0 (by omega) x
    simp only [norm_iteratedFDeriv_zero] at h
    exact h.trans ((mul_le_mul_of_nonneg_left ((L i).le_opNorm U) hC0).trans_eq (mul_assoc _ _ _).symm)
  simp only [nativeClassicalEvaluationCLM, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]
  calc
    _ ≤ ∑ i, ‖CycleWords.realClassicalEvaluationCLM K hK x (L i U) • e i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (EntryWeakProofs.classicalSobolevConstant 0 * ‖L i‖ * ‖e i‖) * ‖U‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans_eq (by ring)
    _ = C * ‖U‖ := (Finset.sum_mul _ _ _).symm

omit [FiniteDimensional ℝ E] in
/-- Classical ordered differentiation agrees with the corresponding native derivative map. -/
theorem native_classical_derivative_rep {K n r : ℕ} (U : TorusHk (K + n) E)
    (f : Vec 2 → E) (hf : IsClassicalRep U f (n + r)) (w : DerivativeWord2 n) :
    IsClassicalRep (derivativeTorusHk w U) (orderedDerivative w f) r := by
  have hrK : r ≤ K := by have h := hf.1; omega
  refine ⟨hrK, CycleComparison.Lift.orderedDerivative_contDiff w r f
    (hf.2.1.of_le (by exact_mod_cast (show r + n ≤ n + r by omega))),
    orderedDerivative_periodic w f (hf.2.1.of_le (by exact_mod_cast Nat.le_add_right n r))
      hf.2.2.1, ?_⟩
  intro m hm β
  have hmK : m ≤ K := hm.trans hrK
  have hnm : n + m ≤ K + n := by omega
  have hj := hf.2.2.2 (n + m) (Nat.add_le_add_left hm n) (Fin.append w β)
  have hleft := periodicJetRepresentative_ae (derivativeTorusHk w U).val
    (⟨⟨m, Nat.lt_succ_of_le hmK⟩, β⟩ : JetIndex2 K)
  have hright := periodicJetRepresentative_ae U.val
    (prefixJetIndex w (⟨⟨m, Nat.lt_succ_of_le hmK⟩, β⟩ : JetIndex2 K))
  rw [derivativeTorusHk_apply] at hleft
  unfold torusJetOrder at hj ⊢
  simp only [hmK, hnm, ↓reduceDIte] at hj ⊢
  rw [CycleWords.orderedDerivative_append] at hj
  exact hleft.trans (hright.symm.trans hj)

/-- Every permitted classical word has a uniform Sobolev bound on the whole torus. -/
theorem native_classical_word_uniform_bound {K n : ℕ} (hK : 2 ≤ K)
    (w : DerivativeWord2 n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TorusHk (K + n) E) (f : Vec 2 → E),
      IsClassicalRep U f n → ∀ x, ‖orderedDerivative w f x‖ ≤ C * ‖U‖ := by
  obtain ⟨C, hC, hb⟩ := native_classical_evaluation_uniform_bound (E := E) K hK
  let L := derivativeTorusHk (E := E) (K := K) w
  refine ⟨C * ‖L‖, mul_nonneg hC (norm_nonneg L), fun U f hf x => ?_⟩
  have hf' : IsClassicalRep U f (n + 0) := by simpa only [Nat.add_zero] using hf
  have he := nativeClassicalEvaluationCLM_rep hK (L U) (orderedDerivative w f)
    (native_classical_derivative_rep U f hf' w) x
  rw [← he]
  exact (hb x (L U)).trans ((mul_le_mul_of_nonneg_left (L.le_opNorm U) hC).trans_eq
    (mul_assoc _ _ _).symm)

/-- Truncation supplies the same word budget from any larger native reserve. -/
theorem native_classical_word_reserved_bound {K n : ℕ} (hn : n ≤ K)
    (w : DerivativeWord2 n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TorusHk (K + 2) E) (f : Vec 2 → E),
      IsClassicalRep U f K → ∀ x, ‖orderedDerivative w f x‖ ≤ C * ‖U‖ := by
  obtain ⟨C, hC, hb⟩ := native_classical_word_uniform_bound (E := E) (K := 2) (by omega) w
  let L := truncateTorusHk (E := E) (K := 2 + n) (L := K + 2) (by omega)
  refine ⟨C * ‖L‖, mul_nonneg hC (norm_nonneg L), fun U f hf x => ?_⟩
  have hrep := classicalRep_truncate (show 2 + n ≤ K + 2 by omega) (by omega)
    U f (classicalRep_order_mono _ _ hf hn)
  exact (hb (L U) f hrep x).trans
    ((mul_le_mul_of_nonneg_left (L.le_opNorm U) hC).trans_eq (mul_assoc _ _ _).symm)

/-- Integrable Sobolev norms give the spatial budgets used in the residual assembly. -/
theorem native_classical_window_bound {K : ℕ} {a b : ℝ}
    (U : ℝ → TorusHk (K + 2) E) (f : ℝ → Vec 2 → E)
    (hf : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) K)
    (hU : StronglyMeasurable (fun t : Icc a b => U t))
    (hUn : IntegrableOn (fun t => ‖U t‖) (Icc a b)) :
    ClassicalWindowBound a b K f := by
  refine ⟨fun t ht => (hf t ht).2.1, fun t ht => (hf t ht).2.2.1, ?_, ?_⟩
  · have hm := (native_classical_evaluation_stronglyMeasurable (E := E)
      (K := K + 2) (by omega) (fun t : Icc a b => U t) hU).measurable
    have hz : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} =>
        ((⟨z.1.1, z.2⟩ : Icc a b), z.1.2)) :=
      (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
        (measurable_snd.comp measurable_subtype_coe)
    have hj := hm.comp hz
    convert hj using 1
    funext z
    exact (nativeClassicalEvaluationCLM_rep (by omega) (U z.1.1) (f z.1.1)
      (hf z.1.1 z.2) z.1.2).symm
  · intro n hn w
    obtain ⟨C, _hC, hb⟩ := native_classical_word_reserved_bound (E := E) hn w
    exact ⟨fun t => C * ‖U t‖, hUn.const_mul C, fun t ht x _ => hb (U t) (f t) (hf t ht) x⟩

/-- Continuous native curves give a time-uniform budget for each permitted word. -/
theorem native_classical_word_uniform_window {K n : ℕ} (hn : n ≤ K)
    {a b : ℝ} (U : ℝ → TorusHk (K + 2) E) (f : ℝ → Vec 2 → E)
    (hf : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) K)
    (hU : ContinuousOn U (Icc a b)) (w : DerivativeWord2 n) :
    ∃ B : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖orderedDerivative w (f t) x‖ ≤ B := by
  obtain ⟨C, hC, hb⟩ := native_classical_word_reserved_bound (E := E) hn w
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  exact ⟨C * B, fun t ht x => (hb (U t) (f t) (hf t ht) x).trans
    (mul_le_mul_of_nonneg_left (hB t ht) hC)⟩

/-- A reserved spatial word has the derivative and primitive of the same time curve. -/
theorem native_classical_word_time {K n r : ℕ} (hK : 2 ≤ K) {a b : ℝ} (hab : a ≤ b)
    (U dU : ℝ → TorusHk (K + n) E)
    (hU : CycleEvolution.StrongTimeRegularity a b U dU)
    (hdU : IntervalIntegrable dU volume a b) (f df : ℝ → Vec 2 → E)
    (hf : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) (n + r))
    (hdf : ∀ t ∈ Icc a b, IsClassicalRep (dU t) (df t) (n + r))
    (w : DerivativeWord2 n) :
    (∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
      HasDerivAt (fun s => orderedDerivative w (f s) x) (orderedDerivative w (df t) x) t) ∧
    ∀ t ∈ Icc a b, ∀ x,
      orderedDerivative w (f t) x - orderedDerivative w (f a) x =
        ∫ s in Ioc a t, orderedDerivative w (df s) x := by
  let L := derivativeTorusHk (E := E) (K := K) w
  have hf' := fun t ht => native_classical_derivative_rep (U t) (f t) (hf t ht) w
  have hdf' := fun t ht => native_classical_derivative_rep (dU t) (df t) (hdf t ht) w
  have hd : IntervalIntegrable (fun s => L (dU s)) volume a b :=
    ⟨L.integrable_comp hdU.1, L.integrable_comp hdU.2⟩
  have he (t : ℝ) (ht : t ∈ Icc a b) (x : Vec 2) :
      nativeClassicalEvaluationCLM K hK x (L (dU t)) = orderedDerivative w (df t) x :=
    nativeClassicalEvaluationCLM_rep hK _ _ (hdf' t ht) x
  refine ⟨?_, ?_⟩
  · filter_upwards [native_classical_time_derivative hK hab (fun s => L (U s))
      (fun s => L (dU s)) (hU.map L) (fun s => orderedDerivative w (f s)) hf',
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    intro x
    have hx := ht x
    rw [he t hmem x] at hx
    exact hx
  · intro t ht x
    have hi := native_classical_time_increment hK hab (fun s => L (U s))
      (fun s => L (dU s)) (hU.map L) hd (fun s => orderedDerivative w (f s)) hf' t ht x
    refine hi.trans (setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_)
    exact he s ⟨hs.1.le, hs.2.trans ht.2⟩ x

/-- Replace a time-L² derivative by one globally strongly measurable version.
Only the derivative changes on a null set; the actual curve and its endpoints stay fixed. -/
theorem native_strong_time_measurable_derivative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {a b : ℝ} (hab : a ≤ b) (U dU : ℝ → H)
    (hd : MemLp dU 2 (volume.restrict (Icc a b)))
    (hU : CycleEvolution.StrongTimeRegularity a b U dU) :
    ∃ V : ℝ → H, StronglyMeasurable V ∧
      MemLp V 2 (volume.restrict (Icc a b)) ∧
      CycleEvolution.StrongTimeRegularity a b U V := by
  let V := hd.aestronglyMeasurable.mk dU
  have he : dU =ᵐ[volume.restrict (Icc a b)] V := hd.aestronglyMeasurable.ae_eq_mk
  refine ⟨V, hd.aestronglyMeasurable.stronglyMeasurable_mk,
    (memLp_congr_ae he).mp hd, hU.ac, ?_⟩
  rw [uIcc_of_le hab]
  have hder := hU.derivative
  rw [uIcc_of_le hab] at hder
  filter_upwards [hder, he] with t ht het
  rwa [← het]

section FrameCurves
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Assemble the exact classical time package from a reserved native Sobolev curve.
The derivative is evaluated once in the native space, before selecting any test. -/
theorem native_classical_time_curve_of_sobolev (F : Frame D hr Dm bw j₀) (K : ℕ)
    (hab : F.tp ≤ F.tf)
    (U : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K + 4) (hr v.1.root))
    (dU : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K + 2) (hr v.1.root)) (f : F.Field)
    (hf : ∀ v t, t ∈ Icc F.tp F.tf → IsClassicalRep (U v t) (fun x => f t x v) (K + 2))
    (hU : ∀ v, ContinuousOn (U v) (Icc F.tp F.tf))
    (hdm : ∀ v, StronglyMeasurable (fun t : Icc F.tp F.tf => dU v t))
    (hdi : ∀ v, IntervalIntegrable (dU v) volume F.tp F.tf)
    (hd : ∀ v, CycleEvolution.StrongTimeRegularity F.tp F.tf
      (fun t => truncateTorusHk (show K + 2 ≤ K + 4 by omega) (U v t)) (dU v)) :
    ClassicalTimeCurve F (K + 4) f
      (fun t x v => nativeClassicalEvaluationCLM (K + 2) (by omega) x (dU v t)) := by
  let df : F.Field := fun t x v => nativeClassicalEvaluationCLM (K + 2) (by omega) x (dU v t)
  let V := fun v t => truncateTorusHk (E := hr v.1.root)
    (show K + 2 ≤ K + 4 by omega) (U v t)
  have hfr (v : CompIn F.G.comps) (t : ℝ) (ht : t ∈ Icc F.tp F.tf) :
      IsClassicalRep (V v t) (fun x => f t x v) (K + 2) :=
    classicalRep_truncate (by omega) le_rfl (U v t) _ (hf v t ht)
  have hdfr (v : CompIn F.G.comps) (t : ℝ) :
      IsClassicalRep (dU v t) (fun x => df t x v) K :=
    native_classical_evaluation_rep le_rfl (dU v t)
  have hf0 (v : CompIn F.G.comps) (t : ℝ) (ht : t ∈ Icc F.tp F.tf) :
      IsClassicalRep (V v t) (fun x => f t x v) 0 :=
    classicalRep_order_mono _ _ (hfr v t ht) (Nat.zero_le _)
  have hder (v : CompIn F.G.comps) := native_classical_time_derivative
    (K := K + 2) (by omega) hab (V v) (dU v) (hd v) (fun t x => f t x v) (hf0 v)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    let nativeCurveTimeSecondCountable : SecondCountableTopologyEither
        (Icc F.tp F.tf) (TorusHk (K + 4) (hr v.1.root)) :=
      secondCountableTopologyEither_of_left _ _
    have hM : StronglyMeasurable (fun t : Icc F.tp F.tf => U v t) :=
      (continuousOn_iff_continuous_domRestrict.mp (hU v)).stronglyMeasurable
    simpa only [show K + 4 - 2 = K + 2 by omega] using
      native_classical_window_bound (U v) (fun t x => f t x v) (hf v) hM
        (hU v).norm.integrableOn_Icc
  · intro v n hn w
    obtain ⟨B, hB⟩ := native_classical_word_uniform_window (show n ≤ K + 2 by omega)
      (U v) (fun t x => f t x v) (hf v) (hU v) w
    exact ⟨B, fun t ht x _ => hB t ht x⟩
  · filter_upwards [ae_all_iff.mpr hder] with t ht
    intro x
    exact hasDerivAt_pi.mpr (fun v => ht v x)
  · intro v
    have hi : IntegrableOn (fun t => ‖dU v t‖) (Icc F.tp F.tf) := by
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hdi v).norm
    simpa only [show K + 4 - 4 = K by omega] using
      native_classical_window_bound (dU v) (fun t x => df t x v)
        (fun t _ => hdfr v t) (hdm v) hi
  · intro n hn w v t ht x
    have hnK : n ≤ K := by omega
    let L := truncateTorusHk (E := hr v.1.root) (show 2 + n ≤ K + 2 by omega)
    have hfn (s : ℝ) (hs : s ∈ Icc F.tp F.tf) :
        IsClassicalRep (L (V v s)) (fun y => f s y v) (n + 0) :=
      classicalRep_truncate (by omega) (by omega) _ _
        (classicalRep_order_mono _ _ (hfr v s hs) (by omega))
    have hdfn (s : ℝ) (_hs : s ∈ Icc F.tp F.tf) :
        IsClassicalRep (L (dU v s)) (fun y => df s y v) (n + 0) :=
      classicalRep_truncate (by omega) (by omega) _ _
        (classicalRep_order_mono _ _ (hdfr v s) (by omega))
    exact (native_classical_word_time (K := 2) (r := 0) (by omega) hab
      (fun s => L (V v s)) (fun s => L (dU v s)) ((hd v).map L)
      ⟨L.integrable_comp (hdi v).1, L.integrable_comp (hdi v).2⟩
      (fun s y => f s y v) (fun s y => df s y v) hfn hdfn w).2 t ht x
  · intro v t ht x
    exact native_classical_time_increment (by omega) hab (V v) (dU v) (hd v) (hdi v)
      (fun s y => f s y v) (hf0 v) t ht x

/-- Choose the classical derivative field from native time-L² derivatives at
an arbitrary full reserve. This also fixes a strongly measurable derivative version. -/
theorem native_classical_time_curve_exists (F : Frame D hr Dm bw j₀) (L : ℕ)
    (hL : 4 ≤ L) (hab : F.tp ≤ F.tf)
    (U : ∀ v : CompIn F.G.comps, ℝ → TorusHk L (hr v.1.root))
    (dU : ∀ v : CompIn F.G.comps, ℝ → TorusHk (L - 2) (hr v.1.root)) (f : F.Field)
    (hf : ∀ v t, t ∈ Icc F.tp F.tf → IsClassicalRep (U v t) (fun x => f t x v) (L - 2))
    (hU : ∀ v, ContinuousOn (U v) (Icc F.tp F.tf))
    (hdLp : ∀ v, MemLp (dU v) 2 (volume.restrict (Icc F.tp F.tf)))
    (hd : ∀ v, CycleEvolution.StrongTimeRegularity F.tp F.tf
      (fun t => truncateTorusHk (Nat.sub_le L 2) (U v t)) (dU v)) :
    ∃ df : F.Field, ClassicalTimeCurve F L f df := by
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 4 := ⟨L - 4, by omega⟩
  have he : K + 4 - 2 = K + 2 := by omega
  simp only [he] at dU hf hdLp hd
  choose V hVm hVLp hVtime using fun v =>
    native_strong_time_measurable_derivative hab _ (dU v) (hdLp v) (hd v)
  refine ⟨fun t x v => nativeClassicalEvaluationCLM (K + 2) (by omega) x (V v t), ?_⟩
  apply native_classical_time_curve_of_sobolev F K hab U V f hf hU
  · exact fun v => (hVm v).comp_measurable measurable_subtype_coe
  · exact fun v => (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((hVLp v).integrable (by norm_num))
  · exact hVtime

/-- The prepared Sobolev time package transports each permitted spatial word
along arbitrary moving charts, with one exceptional set before choosing a chart. -/
theorem native_classical_curve_moving_word (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hab : F.tp ≤ F.tf) (w : DerivativeWord2 n) (hn : n + 4 ≤ K)
    (v : CompIn F.G.comps) :
    ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ γ : ℝ → Vec 2, ∀ V : Vec 2,
      HasDerivAt γ V t →
      HasDerivAt (fun s => orderedDerivative w (fun y => f s y v) (γ s))
        (orderedDerivative w (fun y => df t y v) (γ t) +
          fderiv ℝ (orderedDerivative w (fun y => f t y v)) (γ t) V) t := by
  let fw := fun t => orderedDerivative w (fun y => f t y v)
  let dw := fun t => orderedDerivative w (fun y => df t y v)
  have hfw : ClassicalWindowBound F.tp F.tf 1 fw := (Q.field v).word w (by omega)
  have hdw : ClassicalWindowBound F.tp F.tf 0 dw := (Q.derivativeBound v).word w (by omega)
  have hp (t : ℝ) (ht : t ∈ Icc F.tp F.tf) (x : Vec 2) :
      fw t x - fw F.tp x = ∫ s in Ioc F.tp t, dw s x := Q.primitive n hn w v t ht x
  have hmove := native_window_global_moving_derivative hab fw dw
    (fun t ht => (hfw.smooth t ht).continuous) (fun t ht => (hdw.smooth t ht).continuous)
    hdw.measurable_zero_extension (fun _ _ => by
      obtain ⟨B, hB, hb⟩ := hdw.global_bound 0 le_rfl (fun i => Fin.elim0 i)
      exact ⟨B, hB, fun t ht x _ => by simpa only [orderedDerivative_zero] using hb t ht x⟩) hp
  filter_upwards [hmove, ae_restrict_mem measurableSet_Icc] with t ht hmem
  intro γ V hγ
  exact ht γ _ hγ.continuousAt
    (((hfw.smooth t hmem).differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ)

/-- The prepared time primitive holds in the full finite-dimensional spatial
jet space, so arbitrary multilinear directions use the same primitive. -/
theorem native_classical_curve_spatial_jet_primitive (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hab : F.tp ≤ F.tf) (hn : n + 4 ≤ K) (v : CompIn F.G.comps)
    (t : ℝ) (ht : t ∈ Icc F.tp F.tf) (x : Vec 2) :
    iteratedFDeriv ℝ n (fun y => f t y v) x -
      iteratedFDeriv ℝ n (fun y => f F.tp y v) x =
      ∫ s in Ioc F.tp t, iteratedFDeriv ℝ n (fun y => df s y v) x := by
  classical
  let nativeSpatialJetMeasurable : MeasurableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := borel _
  let nativeSpatialJetBorel : BorelSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := ⟨rfl⟩
  have hdw := (Q.derivativeBound v).spatial_jet (n := n) (L := 0) (by omega)
  have hi := (hdw.integrable_section x).mono_set
    (show Ioc F.tp t ⊆ Icc F.tp F.tf from fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩)
  have he (s : ℝ) (hs : s ∈ Icc F.tp F.tf) (w : DerivativeWord2 n) :
      iteratedFDeriv ℝ n (fun y => f s y v) x (fun i => basisVec (w (Fin.rev i))) =
        orderedDerivative w (fun y => f s y v) x :=
    (congrFun (orderedDerivative_eq_iteratedFDeriv w
      (((Q.field v).smooth s hs).of_le (Nat.cast_le.mpr (show n ≤ K - 2 by omega)))) x).symm
  have hde (s : ℝ) (hs : s ∈ Icc F.tp F.tf) (w : DerivativeWord2 n) :
      iteratedFDeriv ℝ n (fun y => df s y v) x (fun i => basisVec (w (Fin.rev i))) =
        orderedDerivative w (fun y => df s y v) x :=
    (congrFun (orderedDerivative_eq_iteratedFDeriv w
      (((Q.derivativeBound v).smooth s hs).of_le (Nat.cast_le.mpr (show n ≤ K - 4 by omega)))) x).symm
  obtain ⟨R, hR⟩ := native_multilinear_word_retraction (V := hr v.1.root) n
  rw [← hR (iteratedFDeriv ℝ n (fun y => f t y v) x -
    iteratedFDeriv ℝ n (fun y => f F.tp y v) x), ← hR (∫ s in Ioc F.tp t,
      iteratedFDeriv ℝ n (fun y => df s y v) x)]
  congr 1
  funext w
  rw [sub_apply, he t ht w, he F.tp ⟨le_rfl, hab⟩ w, Q.primitive n hn w v t ht x,
    ContinuousMultilinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (hde s ⟨hs.1.le, hs.2.trans ht.2⟩ w).symm

/-- The full multilinear prepared jet differentiates along every moving chart
on a common time set, with no infinite time-smoothness assumption. -/
theorem native_classical_curve_spatial_jet_moving (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hab : F.tp ≤ F.tf) (hn : n + 4 ≤ K) (v : CompIn F.G.comps) :
    ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ γ : ℝ → Vec 2, ∀ V : Vec 2,
      HasDerivAt γ V t →
      HasDerivAt (fun s => iteratedFDeriv ℝ n (fun y => f s y v) (γ s))
        (iteratedFDeriv ℝ n (fun y => df t y v) (γ t) +
          fderiv ℝ (fun x => iteratedFDeriv ℝ n (fun y => f t y v) x) (γ t) V) t := by
  let nativeSpatialJetMeasurable : MeasurableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := borel _
  let nativeSpatialJetBorel : BorelSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := ⟨rfl⟩
  let fw := fun s x => iteratedFDeriv ℝ n (fun y => f s y v) x
  let dw := fun s x => iteratedFDeriv ℝ n (fun y => df s y v) x
  have hfw : ClassicalWindowBound F.tp F.tf 1 fw := (Q.field v).spatial_jet (by omega)
  have hdw : ClassicalWindowBound F.tp F.tf 0 dw := (Q.derivativeBound v).spatial_jet (by omega)
  have hmove := native_window_global_moving_derivative hab fw dw
    (fun t ht => (hfw.smooth t ht).continuous) (fun t ht => (hdw.smooth t ht).continuous)
    hdw.measurable_zero_extension (fun _ _ => by
      obtain ⟨B, hB, hb⟩ := hdw.global_bound 0 le_rfl (fun i => Fin.elim0 i)
      exact ⟨B, hB, fun t ht x _ => by simpa only [orderedDerivative_zero] using hb t ht x⟩)
    (native_classical_curve_spatial_jet_primitive F Q hab hn v)
  filter_upwards [hmove, ae_restrict_mem measurableSet_Icc] with t ht hmem
  intro γ V hγ
  exact ht γ _ hγ.continuousAt
    (((hfw.smooth t hmem).differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ)

/-- All chart pullback words have common-time derivatives. The prepared field
needs only the finite Sobolev reserve already present in the native package. -/
theorem native_classical_curve_pullback_word_moving_differentiable (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hab : F.tp ≤ F.tf) (hn : n + 4 ≤ K) (v : CompIn F.G.comps)
    (Φ : ℝ → Vec 2 → Vec 2) (hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ))
    (w : DerivativeWord2 n) :
    ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ γ : ℝ → Vec 2, ∀ V : Vec 2,
      HasDerivAt γ V t →
      DifferentiableAt ℝ (fun s => orderedDerivative w ((fun y => f s y v) ∘ Φ s) (γ s)) t := by
  classical
  have hjets : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ j : ℕ, j ≤ n →
      ∀ γ : ℝ → Vec 2, ∀ V : Vec 2, HasDerivAt γ V t →
        DifferentiableAt ℝ (fun s => iteratedFDeriv ℝ j (fun y => f s y v) (γ s)) t := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j ≤ n
    · filter_upwards [native_classical_curve_spatial_jet_moving F (n := j) Q hab (by omega) v] with t ht
      exact fun _ γ V hγ => (ht γ V hγ).differentiableAt
    · exact ae_of_all _ (fun _ hj' => (hj hj').elim)
  have hinside : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), t ∈ Ioo F.tp F.tf := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hjets, hinside] with t ht hti
  intro γ V hγ
  have hcurve : HasDerivAt (fun s => (s, γ s)) (1, V) t := (hasDerivAt_id t).prodMk hγ
  have hΦγ : DifferentiableAt ℝ (fun s => Φ s (γ s)) t := by
    have hd : HasFDerivAt (Function.uncurry Φ)
        (fderiv ℝ (Function.uncurry Φ) (t, γ t)) (t, γ t) :=
      (hΦ.differentiable (by simp) (t, γ t)).hasFDerivAt
    simpa only [Function.comp_def, Function.uncurry] using
      (hd.comp_hasDerivAt t hcurve).differentiableAt
  have hterm (c : OrderedFinpartition n) : DifferentiableAt ℝ (fun s =>
      (c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (fun y => f s y v) (Φ s (γ s)))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Φ s) (γ s)))
        (fun i => basisVec (w (Fin.rev i)))) t := by
    have hA := ht c.length c.length_le (fun s => Φ s (γ s)) _ hΦγ.hasDerivAt
    have hB (i : Fin c.length) : DifferentiableAt ℝ
        (fun s => iteratedFDeriv ℝ (c.partSize i) (Φ s) (γ s)) t := by
      have hj := native_smooth_chart_spatial_jet Φ hΦ (c.partSize i)
      have hd : HasFDerivAt (fun p : ℝ × Vec 2 => iteratedFDeriv ℝ (c.partSize i) (Φ p.1) p.2)
          (fderiv ℝ (fun p : ℝ × Vec 2 => iteratedFDeriv ℝ (c.partSize i) (Φ p.1) p.2)
            (t, γ t)) (t, γ t) := (hj.differentiable (by simp) (t, γ t)).hasFDerivAt
      simpa only [Function.comp_def] using (hd.comp_hasDerivAt t hcurve).differentiableAt
    have hD (i : Fin c.length) : DifferentiableAt ℝ (fun s =>
        iteratedFDeriv ℝ (c.partSize i) (Φ s) (γ s)
          (fun j => basisVec (w (Fin.rev (c.emb i j))))) t :=
      ((hB i).hasFDerivAt.continuousMultilinear_apply_const _).differentiableAt
    have hL := hA.hasFDerivAt.continuousMultilinearMap_apply (fun i => (hD i).hasFDerivAt)
    simpa only [OrderedFinpartition.compAlongOrderFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply, Function.comp_def] using hL.differentiableAt
  apply (DifferentiableAt.fun_sum (fun c _ => hterm c)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hti] with s hs
  exact native_pullback_word_eq_faa w (fun y => f s y v) (Φ s)
    (((Q.field v).smooth s (Ioo_subset_Icc_self hs)).of_le
      (Nat.cast_le.mpr (show n ≤ K - 2 by omega)))
    ((hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) (γ s)

/-- The prepared time curve's uniform word budgets control the full spatial jet
on the whole plane, by periodicity and finite-dimensional reconstruction. -/
theorem native_classical_curve_spatial_jet_uniform (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hn : n + 2 ≤ K) (v : CompIn F.G.comps) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc F.tp F.tf, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => f t y v) x‖ ≤ B := by
  classical
  choose B hb using Q.uniform v n hn
  let C := ∑ w : DerivativeWord2 n, |B w|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨R, hR⟩ := native_multilinear_word_retraction (V := hr v.1.root) n
  refine ⟨‖R‖ * C, mul_nonneg (norm_nonneg R) hC, fun t ht x => ?_⟩
  have hfn : ContDiff ℝ (n : ℕ∞) (fun y => f t y v) :=
    ((Q.field v).smooth t ht).of_le (Nat.cast_le.mpr (show n ≤ K - 2 by omega))
  have hw (w : DerivativeWord2 n) : ‖orderedDerivative w (fun y => f t y v) x‖ ≤ C := by
    have hglobal := native_periodic_norm_le_of_cube _
      (CycleComparison.Lift.orderedDerivative_contDiff w 0 _
        (by simpa only [Nat.zero_add] using hfn)).continuous
      (orderedDerivative_periodic w _ hfn ((Q.field v).periodic t ht)) (B w) (hb w t ht) x
    have hsingle : |B w| ≤ C := by
      change |B w| ≤ ∑ w : DerivativeWord2 n, |B w|
      exact Finset.single_le_sum (fun z _ => abs_nonneg (B z)) (Finset.mem_univ w)
    exact hglobal.trans ((le_abs_self _).trans hsingle)
  have he : R (fun w => orderedDerivative w (fun y => f t y v) x) =
      iteratedFDeriv ℝ n (fun y => f t y v) x := by
    simp_rw [AVRegularity.orderedDerivative_eq_iteratedFDeriv _ hfn]
    exact hR _
  rw [← he]
  exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((pi_norm_le_iff_of_nonneg hC).mpr hw) (norm_nonneg R))

/-- Finite prepared Sobolev reserves give uniform spatial budgets after taking a
chart word and evaluating it in a second smooth chart on a compact spatial set. -/
theorem native_classical_curve_pullback_word_compact_jet_bound (F : Frame D hr Dm bw j₀)
    {K m : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (v : CompIn F.G.comps) (w : DerivativeWord2 m) (n : ℕ) (hn : n + m + 2 ≤ K)
    (Φ label : ℝ → Vec 2 → Vec 2)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (X : Set (Vec 2)) (hX : IsCompact X) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc F.tp F.tf, ∀ x ∈ X,
      ‖iteratedFDeriv ℝ n
        (fun y => orderedDerivative w ((fun z => f t z v) ∘ Φ t) (label t y)) x‖ ≤ B := by
  classical
  choose C hC hb using fun j : Fin (n + m + 1) =>
    native_classical_curve_spatial_jet_uniform F Q (n := j.1) (by omega) v
  let Csum := ∑ j : Fin (n + m + 1), C j
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hC j)
  obtain ⟨D, hD, hd⟩ := native_smooth_chart_compact_jet_bounds Φ hΦ label hlabel
    F.tp F.tf X hX (n + m)
  obtain ⟨E, hE, he⟩ := native_smooth_chart_compact_jet_bounds label hlabel
    (fun _ x => x) contDiff_snd F.tp F.tf X hX n
  let U := fun j : ℕ => (j.factorial : ℝ) * Csum * D ^ j
  let Usum := ∑ j ∈ Finset.range (n + m + 1), U j
  have hU (j : ℕ) : 0 ≤ U j := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCsum)
    (pow_nonneg (le_trans zero_le_one hD) _)
  have hUsum : 0 ≤ Usum := Finset.sum_nonneg (fun j _ => hU j)
  refine ⟨(n.factorial : ℝ) * Usum * E ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hUsum) (pow_nonneg (le_trans zero_le_one hE) _), ?_⟩
  intro t ht x hx
  have hft : ContDiff ℝ ((n + m : ℕ) : ℕ∞) (fun y => f t y v) :=
    ((Q.field v).smooth t ht).of_le (Nat.cast_le.mpr (by omega))
  have hΦt : ContDiff ℝ ((n + m : ℕ) : ℕ∞) (Φ t) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hlt : ContDiff ℝ (n : ℕ∞) (label t) :=
    (hlabel.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hg := hft.comp hΦt
  have hw : ContDiff ℝ (n : ℕ∞) (orderedDerivative w ((fun y => f t y v) ∘ Φ t)) :=
    CycleComparison.Lift.orderedDerivative_contDiff w n _
      (by simpa only [Nat.add_comm] using hg)
  have hcomp (j : ℕ) (hj : j ≤ n + m) :
      ‖iteratedFDeriv ℝ j ((fun y => f t y v) ∘ Φ t) (label t x)‖ ≤ U j := by
    apply norm_iteratedFDeriv_comp_le hft hΦt (Nat.cast_le.mpr hj) (label t x)
    · intro k hk
      exact (hb ⟨k, by omega⟩ t ht _).trans
        (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))
    · intro k hk hkj
      exact (hd k (hkj.trans hj) t ht x hx).trans (le_self_pow₀ hD (by omega))
  apply norm_iteratedFDeriv_comp_le hw hlt (by simp) x
  · intro j hj
    have hword := norm_iteratedFDeriv_orderedDerivative_le (p := j) w
      (hg.of_le (Nat.cast_le.mpr (show j + m ≤ n + m by omega))) (label t x)
    exact (hword.trans (hcomp (j + m) (by omega))).trans
      (Finset.single_le_sum (fun k _ => hU k) (Finset.mem_range.mpr (by omega)))
  · intro j hj hjn
    exact (he j hjn t ht x hx).trans (le_self_pow₀ hE (by omega))

/-- Reserved prepared spatial jets remain absolutely continuous along any
absolutely continuous spatial label, using only integrable time budgets. -/
theorem native_classical_curve_spatial_jet_moving_ac (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hab : F.tp ≤ F.tf) (hn : n + 4 ≤ K) (v : CompIn F.G.comps)
    (γ : ℝ → Vec 2) (hγ : AbsolutelyContinuousOnInterval γ F.tp F.tf) :
    AbsolutelyContinuousOnInterval
      (fun t => iteratedFDeriv ℝ n (fun y => f t y v) (γ t)) F.tp F.tf := by
  let nativeSpatialJetMeasurable : MeasurableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := borel _
  let nativeSpatialJetBorel : BorelSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)) := ⟨rfl⟩
  have hfw := (Q.field v).spatial_jet (n := n) (L := 1) (by omega)
  have hdw := (Q.derivativeBound v).spatial_jet (n := n) (L := 0) (by omega)
  obtain ⟨L, hL, hl⟩ := native_classical_curve_spatial_jet_uniform F (n := n + 1) Q (by omega) v
  have hLip (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : LipschitzWith (⟨L, hL⟩ : NNReal)
      (fun x => iteratedFDeriv ℝ n (fun y => f t y v) x) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      ((hfw.smooth t ht).differentiable (by simp))
    intro x
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ (fun x => iteratedFDeriv ℝ n (fun y => f t y v) x) x‖ ≤ L
    rw [norm_fderiv_iteratedFDeriv]
    exact hl t ht x
  apply native_window_global_moving_ac hab _ _
    (fun t ht => (hfw.smooth t ht).continuous) (fun t ht => (hdw.smooth t ht).continuous)
    hdw.measurable_zero_extension (fun _ _ => ?_)
    (native_classical_curve_spatial_jet_primitive F Q hab hn v) γ hγ ⟨L, hL⟩ hLip
  obtain ⟨B, hB, hb⟩ := hdw.global_bound 0 le_rfl (fun i => Fin.elim0 i)
  exact ⟨B, hB, fun t ht x _ => by simpa only [orderedDerivative_zero] using hb t ht x⟩

/-- A prepared pullback word is absolutely continuous along any smooth label.
The finite Faà di Bruno expression uses the full prepared jets and smooth
bounded linear chart factors. -/
theorem native_classical_curve_pullback_word_smooth_label_ac (F : Frame D hr Dm bw j₀)
    {K n : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (hab : F.tp ≤ F.tf) (hn : n + 4 ≤ K) (v : CompIn F.G.comps)
    (Φ : ℝ → Vec 2 → Vec 2) (hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ))
    (γ : ℝ → Vec 2) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (w : DerivativeWord2 n) :
    AbsolutelyContinuousOnInterval
      (fun t => orderedDerivative w ((fun y => f t y v) ∘ Φ t) (γ t)) F.tp F.tf := by
  classical
  have hcurve : ContDiff ℝ (⊤ : ℕ∞) (fun s => Φ s (γ s)) :=
    hΦ.comp (contDiff_id.prodMk hγ)
  let T := fun (c : OrderedFinpartition n) s =>
    (c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (fun y => f s y v) (Φ s (γ s)))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (Φ s) (γ s)))
      (fun i => basisVec (w (Fin.rev i)))
  have hterm (c : OrderedFinpartition n) : AbsolutelyContinuousOnInterval (T c) F.tp F.tf := by
    let B := fun s (i : Fin c.length) => iteratedFDeriv ℝ (c.partSize i) (Φ s) (γ s)
    let J := c.compAlongOrderedFinpartitionL ℝ (Vec 2) (Vec 2) (hr v.1.root)
    let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) (hr v.1.root)
      (fun i => basisVec (w (Fin.rev i)))
    let L := fun s => E.comp (J.flipMultilinear (B s))
    have hB : ContDiff ℝ (⊤ : ℕ∞) B := contDiff_pi.mpr (fun i =>
      (native_smooth_chart_spatial_jet Φ hΦ (c.partSize i)).comp
        (contDiff_id.prodMk hγ))
    have hJ : ContDiff ℝ (⊤ : ℕ∞) J.flipMultilinear :=
      ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
        (E := fun i : Fin c.length => ContinuousMultilinearMap ℝ
          (fun _ : Fin (c.partSize i) => Vec 2) (Vec 2))
        (F := ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr v.1.root) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) (hr v.1.root))
        (f := J.flipMultilinear)
    have hL : ContDiff ℝ (⊤ : ℕ∞) L := contDiff_const.clm_comp (hJ.comp hB)
    have hA := native_classical_curve_spatial_jet_moving_ac F (n := c.length) Q hab
      (by have := c.length_le; omega) v (fun s => Φ s (γ s))
      (hcurve.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    have hp := native_bilinear_time_ac ((ContinuousLinearMap.apply ℝ (hr v.1.root)).flip)
      (hL.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval hA
    convert hp using 1
    funext s
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flipMultilinear_apply_apply,
      OrderedFinpartition.compAlongOrderedFinpartitionL_apply, E, L, B, J, T,
      ContinuousMultilinearMap.apply_apply]
  have hsum := native_time_finset_sum Finset.univ T (fun c _ => hterm c)
  apply hsum.congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact (native_pullback_word_eq_faa w (fun y => f t y v) (Φ t)
    (((Q.field v).smooth t ht).of_le (Nat.cast_le.mpr (show n ≤ K - 2 by omega)))
    ((hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) (γ t)).symm

/-- The physical pulse is a finite sum of component prepared words at its
literal physical time. The time clock and Pi derivatives are both explicit. -/
theorem native_classical_pulse_expansion (F : Frame D hr Dm bw j₀)
    {K : ℕ} {f df : F.Field} (Q : ClassicalTimeCurve F K f df)
    (c ρ e ε : ℝ) (hc : c ≠ 0) (N H : ℕ) (hN : N + 2 ≤ K)
    (Cc : ℕ → ℕ → LiftCoeff (CompIn F.G.comps) (fun v => hr v.1.root))
    (chart label : ℝ → Vec 2 → Vec 2) (t : ℝ) (ht : t ∈ Icc F.tp F.tf)
    (hchart : ContDiff ℝ (N : ℕ∞) (chart t)) (x : Vec 2) (v : CompIn F.G.comps) :
    pulsePhysicalLift c ρ e ε N H Cc chart label f t x v =
      ∑ g ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        ε ^ n • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
          Cc g n m α (c⁻¹ * t) (ρ⁻¹ • label t x) (e⁻¹ • label t x) v u
            (orderedDerivative α (fun Y => f t (chart t (ρ • Y)) u) (ρ⁻¹ • label t x)) := by
  classical
  have ha : ContDiff ℝ (N : ℕ∞) (f t) := contDiff_pi.mpr
    (fun u => ((Q.field u).smooth t ht).of_le (Nat.cast_le.mpr (by omega)))
  have hpull : ContDiff ℝ (N : ℕ∞) (fun Y => f t (chart t (ρ • Y))) :=
    (ha.comp hchart).comp ((contDiff_const (c := ρ)).smul contDiff_id)
  rw [FullLift.pulsePhysicalLift_freeze_time,
    show c * (c⁻¹ * t) = t by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul],
    FullLift.pulsePhysicalLift_static_expansion]
  simp only [liftApply]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  have hmN : m ≤ N := by
    have := Finset.mem_range.mp hn
    have := Finset.mem_range.mp hm
    omega
  rw [ChartTransport.orderedDerivative_apply α (hpull.of_le (Nat.cast_le.mpr hmN)) u]

end FrameCurves

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
