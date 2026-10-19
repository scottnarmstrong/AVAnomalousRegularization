-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WSourceL2
public import AVRegularity.CycleJoint.Assembly.BlockTransitionJets
import AVRegularity.CycleJoint.Assembly.WordGeometryOfRetained
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Proofs.QuietAtlas.QuietPulse
import AVRegularity.CycleJoint.PlaneTorus.Superposition
import AVRegularity.CycleJoint.PreparationReferenceCellInitialHomogeneousResponsePair
import AVRegularity.CycleJoint.WindowCoverConstructedRetainedActualTaylorLinearEndpointAllMomentsBound
public import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap
import AVRegularity.CycleComparison.LiftSetting.Main
import Mathlib.CategoryTheory.Countable

section
/-! **Uniqueness of word chains with finite moment energies**.

Induction on the level: at each level both chains have the same previous-letter flux, hence (the
energies of the first chain give a time-`L²` source `V` matching it) the same scalar component
problem with the same source; the Duhamel step identifies the values, and the truncation
injectivity identifies the `H^{κ+1}` fields. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.Weighted AVRegularity.CycleWords.Assembly

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

section Levels

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- Two chains with the same source at level `j` agree at level `j`. -/
theorem wordChain_level_of_source (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2)
    (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b) (vd : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift vd)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U U' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw Uw' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (hsol' : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U' (j, x)) (fun j x => Uw' (j, x)))
    (j : Fin (N + 1))
    (V : ∀ x : ι, ℝ → PlaneHk Set.univ (κ (j, x).1 (j, x).2)
      (PiLp 2 (fun _ : Fin 2 => h (j, x).2)))
    (hVl : ∀ x, MemLp (V x) 2 (volume.restrict (Set.Icc a b)))
    (hV : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V x t) =ᵐ[volume]
      wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p t) (j, x) t)
    (hV' : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V x t) =ᵐ[volume]
      wordChainPreviousFlux letters X₀ δ κ (fun p => Uw' p t) (j, x) t) :
    WordChainLevelEq κ a b (fun j x => U (j, x)) (fun j x => U' (j, x))
      (fun j x => Uw (j, x)) (fun j x => Uw' (j, x)) j := by
  have hu : ∀ x, ∀ t ∈ Set.Icc a b, U (j, x) t = U' (j, x) t := fun x =>
    wordChain_component_unique hD G hG letters X₀ δ κ a b hab vd hv f U U' Uw Uw' hsol hsol'
      (j, x)
      (V x) (hVl x) (hV x) (hV' x)
  exact ⟨hu, fun x => planeTruncEq a b (Uw (j, x)) (Uw' (j, x)) (U (j, x)) (U' (j, x))
    (hsol.2.2.1 (j, x)) (hsol'.2.2.1 (j, x)) (hu x)⟩

omit [Fintype ι] in
/-- The zero source is square integrable in time. -/
theorem wordChain_zero_memLp (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (x : ι) :
    MemLp (fun _ : ℝ => (0 : PlaneHk Set.univ (κ (0, x).1 (0, x).2)
      (PiLp 2 (fun _ : Fin 2 => h (0, x).2)))) 2 (volume.restrict (Set.Icc a b)) :=
  planeHk_zero_time_memLp _ _

/-- The zero source is the previous-letter flux of level `0`. -/
theorem wordChain_zero_flux (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (Uw : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2)) (x : ι) (t : ℝ) :
    planeValue (0 : PlaneHk Set.univ (κ (0, x).1 (0, x).2)
      (PiLp 2 (fun _ : Fin 2 => h (0, x).2))) =ᵐ[volume]
      wordChainPreviousFlux letters X₀ δ κ Uw (0, x) t := by
  rw [wordChainPreviousFlux_zero]
  exact planeValue_zero_ae _

/-- Level `0` has the zero source in both chains. -/
theorem wordChain_level_zero (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2)
    (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b) (vd : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift vd)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U U' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw Uw' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (hsol' : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U' (j, x)) (fun j x => Uw' (j, x))) :
    WordChainLevelEq κ a b (fun j x => U (j, x)) (fun j x => U' (j, x))
      (fun j x => Uw (j, x)) (fun j x => Uw' (j, x)) 0 :=
  by
  refine wordChain_level_of_source hD G hG letters X₀ δ κ a b hab vd hv f U U' Uw Uw' hsol hsol' 0
    (fun x _ => (0 : PlaneHk Set.univ (κ (0, x).1 (0, x).2)
      (PiLp 2 (fun _ : Fin 2 => h (0, x).2)))) ?_ ?_ ?_
  · intro x
    exact wordChain_zero_memLp κ a b x
  · intro x
    exact Filter.Eventually.of_forall fun t =>
      wordChain_zero_flux letters X₀ δ κ (fun p => Uw p t) x t
  · intro x
    exact Filter.Eventually.of_forall fun t =>
      wordChain_zero_flux letters X₀ δ κ (fun p => Uw' p t) x t

/-- Equal fields at level `j` give equal values and fields at level `j + 1`. -/
theorem wordChain_level_succ (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H)
    (hm : ∀ j x y o, ∀ γ ∈ (letters j).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z)
    (X₀ : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (hκJ : ∀ j x, κ j x ≤ J)
    (vd : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift vd) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U U' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw Uw' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (hsol' : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U' (j, x)) (fun j x => Uw' (j, x)))
    (he : ∀ j x n,
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ (κ j x) (Uw (j, x) t)) ≠ ⊤)
    (j : Fin N)
    (ih : WordChainLevelEq κ a b (fun j x => U (j, x)) (fun j x => U' (j, x))
      (fun j x => Uw (j, x)) (fun j x => Uw' (j, x)) j.castSucc) :
    WordChainLevelEq κ a b (fun j x => U (j, x)) (fun j x => U' (j, x))
      (fun j x => Uw (j, x)) (fun j x => Uw' (j, x)) j.succ := by
  have hsrc := fun x => wordChain_source π hπ a b J H letters hL hm X₀ δ κ hκJ ϖ ρ hϖ hρ
    Uw (fun p => hsol.2.1 p) he j x
  choose V hVl hV using hsrc
  refine wordChain_level_of_source hD G hG letters X₀ δ κ a b hab vd hv f U U' Uw Uw' hsol hsol'
    j.succ V hVl hV (fun x => ?_)
  have hall : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ y, Uw (j.castSucc, y) t = Uw' (j.castSucc, y) t :=
    ae_all_iff.mpr fun y => ih.2 y
  filter_upwards [hV x, hall] with t ht hy
  have hf := wordChainFluxCongr letters X₀ δ κ (fun p => Uw p t) (fun p => Uw' p t) j x
    (fun y => hy y) t
  exact ht.trans (Filter.Eventually.of_forall fun z => congrFun hf z)

end Levels

theorem wordChainUnique : WordChainUniqueStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D N hD π hπ G hG _g _hg _hGn vd hv _hvs a b hab J H letters hL hm
    X₀ δ κ hκJ f u u' w w' hc hc' ϖ ρ hϖ hρ he _he'
  have hsol : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => (fun p : Fin (N + 1) × ι => chainDatum κ f p.1 p.2) (j, x)) (fun _ _ _ => 0)
      (fun j x => (fun p : Fin (N + 1) × ι => u p.1 p.2) (j, x))
      (fun j x => (fun p : Fin (N + 1) × ι => w p.1 p.2) (j, x)) := hc
  have hsol' : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b vd
      (fun j x => (fun p : Fin (N + 1) × ι => chainDatum κ f p.1 p.2) (j, x)) (fun _ _ _ => 0)
      (fun j x => (fun p : Fin (N + 1) × ι => u' p.1 p.2) (j, x))
      (fun j x => (fun p : Fin (N + 1) × ι => w' p.1 p.2) (j, x)) := hc'
  have hlev : ∀ j, WordChainLevelEq κ a b u u' w w' j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      exact wordChain_level_zero hD G hG letters X₀ δ κ a b hab vd hv
        (fun p => chainDatum κ f p.1 p.2) (fun p => u p.1 p.2) (fun p => u' p.1 p.2)
        (fun p => w p.1 p.2) (fun p => w' p.1 p.2) hsol hsol'
    | succ j ih =>
      exact wordChain_level_succ hD G hG π hπ letters J H a b hab hL hm X₀ δ κ hκJ vd hv ϖ ρ hϖ hρ
        (fun p => chainDatum κ f p.1 p.2) (fun p => u p.1 p.2) (fun p => u' p.1 p.2)
        (fun p => w p.1 p.2) (fun p => w' p.1 p.2) hsol hsol' (fun j x n => he j x n) j ih
  intro j x t ht
  exact (hlev j).1 x t ht

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs.Assembly

/-! Time dilation and the positive partition preserve the original identity prices. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {W : Set ℝ}
  {Ca : ℝ} {Ks Ls : ℕ} {B : ι → ι → ℝ}

/-- All reserved original jets of one piece are bounded simultaneously at almost every time. -/
theorem blockAnalytic_flux_all_jets_ae_bound {E : ℝ}
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) :
    ∀ᵐ t ∂volume, ∀ d : Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∀ I : DerivativeWord2 (d.val - 1), ∀ r : Fin (Ks + 1), ∀ q : Fin (Ls + 1),
      t ∈ (F.piece p).output ∩ W → ∀ X z,
        ‖(F.identity v u γ).map‖ *
          ‖iteratedFDeriv ℝ r.val (fun Y => iteratedFDeriv ℝ q.val (F.flux p c v u γ d.val I t Y) z) X‖ ≤
        blockIdentityAnalyticPrice F (ChartedFamily.Domain.onWindow F W) E Ks Ls v u γ := by
  apply ae_all_iff.mpr
  intro d
  apply ae_all_iff.mpr
  intro I
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro q
  exact blockAnalytic_flux_jet_ae_bound data v u γ hγ p c d.val d.property I r.val q.val
    (Nat.le_of_lt_succ r.isLt) (Nat.le_of_lt_succ q.isLt)

/-- A block readout has an almost-everywhere mixed jet price weighted by its original map. -/
theorem blockLetterCoefficient_analytic_ae_bound
    {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (data : BlockLetterAnalyticInputs F π W (ocEpsilon q Λ (m - 1)) Ca Ks Ls B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart (F.piece p).anchor σ)
    (e : ℝ) (he : 0 < e) (heE : e ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (timeScale : ℝ) (hclock : timeScale ≠ 0) (hchart : Ks + D ≤ Jchart)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder) (I : DerivativeWord2 (d - 1))
    (r qfast : ℕ) (hr : r ≤ Ks) (hq : qfast ≤ Ls) :
    ∀ᵐ t ∂volume, timeScale * t ∈ (F.piece p).output ∩ W → ∀ X z,
      ‖(F.identity v u γ).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast
          (blockLetterCoefficient F hφ p c v u γ l σ yc e (ocEpsilon q Λ (m - 1)) timeScale d I t Y) z) X‖ ≤
      blockSourceAnalyticJetPrice Ks D Jchart Cchart *
        blockIdentityAnalyticPrice F (ChartedFamily.Domain.onWindow F W) (ocEpsilon q Λ (m - 1)) Ks Ls v u γ := by
  let Pγ := blockIdentityAnalyticPrice F (ChartedFamily.Domain.onWindow F W)
    (ocEpsilon q Λ (m - 1)) Ks Ls v u γ
  have hP : 0 ≤ Pγ := ENNReal.toReal_nonneg
  have hC : 0 ≤ blockSourceAnalyticJetPrice Ks D Jchart Cchart :=
    zero_le_one.trans (blockSourceAnalyticJetPrice_one_le Ks D Jchart Cchart)
  by_cases hγ : (F.identity v u γ).map = 0
  · exact Filter.Eventually.of_forall (fun t ht X z => by
      rw [hγ, norm_zero, zero_mul]
      exact mul_nonneg hC hP)
  have hm : 0 < ‖(F.identity v u γ).map‖ := norm_pos_iff.mpr hγ
  have hall := ae_real_time_dilation timeScale hclock _
    (blockAnalytic_flux_all_jets_ae_bound data p c v u γ hγ)
  filter_upwards [hall] with t ht
  intro htime X z
  have hf : ∀ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∀ A j k,
      j ≤ Ks → k ≤ Ls → ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => iteratedFDeriv ℝ k (F.flux p c v u γ d A (timeScale * t) Y) z) X‖ ≤
        Pγ / ‖(F.identity v u γ).map‖ := by
    intro d hd A j k hj hk X z
    exact (le_div_iff₀ hm).mpr (by
      simpa only [mul_comm] using
        ht ⟨d, hd⟩ A ⟨j, Nat.lt_succ_of_le hj⟩ ⟨k, Nat.lt_succ_of_le hk⟩ htime X z)
  have hb := blockLetterCoefficient_analytic_mixed_bound data p c v u γ l σ chart e he heE yc
    timeScale t htime (Pγ / ‖(F.identity v u γ).map‖) (div_nonneg hP hm.le) hf hchart d hd I r qfast hr hq X z
  calc
    _ ≤ ‖(F.identity v u γ).map‖ * (blockSourceAnalyticJetPrice Ks D Jchart Cchart *
        (Pγ / ‖(F.identity v u γ).map‖)) := mul_le_mul_of_nonneg_left hb hm.le
    _ = blockSourceAnalyticJetPrice Ks D Jchart Cchart * Pγ := by
      calc
        _ = blockSourceAnalyticJetPrice Ks D Jchart Cchart *
            (‖(F.identity v u γ).map‖ * (Pγ / ‖(F.identity v u γ).map‖)) := by ring
        _ = _ := by rw [mul_div_cancel₀ Pγ hm.ne']

/-- A nonzero cutoff weight is supported at a time with the original regularity. -/
theorem blockWeight_nonzero_mem (p : P) (t : ℝ)
    (hw : W.indicator (F.weight p) t ≠ 0) : t ∈ (F.piece p).output ∩ W := by
  classical
  by_cases ht : t ∈ W
  · refine ⟨?_, ht⟩
    by_contra hp
    exact hw (by rw [Set.indicator_of_mem ht, F.weight_zero p t hp])
  · exact False.elim (hw (Set.indicator_of_notMem ht _))

/-- Multiplying by the cutoff preserves joint smoothness, including inactive times. -/
theorem weightedBlockLetterCoefficient_joint_contDiff {E : ℝ}
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e timeScale : ℝ)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (n : ℕ) (hn : n ≤ Ks + Ls) :
    ContDiff ℝ (n : ℕ) (fun w : Vec 2 × Vec 2 =>
      W.indicator (F.weight p) (timeScale * t) •
        blockLetterCoefficient F hφ p c v u γ l σ yc e E timeScale d I t w.1 w.2) := by
  classical
  by_cases hw : W.indicator (F.weight p) (timeScale * t) = 0
  · simpa only [hw, zero_smul] using (contDiff_const (c := (0 : Vec 2)))
  · exact (blockLetterCoefficient_joint_contDiff data hφ p c v u γ l σ yc e timeScale d I t
      (blockWeight_nonzero_mem p _ hw) n hn).const_smul _

/-- The finite weighted source coefficient is jointly smooth at every cell time. -/
theorem sourceConstituent_joint_contDiff {E : ℝ}
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (pieces : Finset P) (actual : ∀ p, Ctx p)
    (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e timeScale : ℝ)
    (d : ℕ) (hd : d ≤ (F.identity v u γ).maxOrder) (I : DerivativeWord2 (d - 1))
    (t : ℝ) (n : ℕ) (hn : n ≤ Ks + Ls) :
    ContDiff ℝ (n : ℕ) (fun w : Vec 2 × Vec 2 =>
      (sourceConstituent F pieces actual hφ v u γ d hd W l σ yc e E timeScale).coeff I t w.1 w.2) := by
  apply ContDiff.sum
  intro p _
  exact weightedBlockLetterCoefficient_joint_contDiff data hφ p (actual p) v u γ l σ yc e
    timeScale d I t n hn

/-- Convex time weights bound the source constituent by one original identity price. -/
theorem sourceConstituent_analytic_ae_bound
    {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (data : BlockLetterAnalyticInputs F π W (ocEpsilon q Λ (m - 1)) Ca Ks Ls B)
    (pieces : Finset P) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ)
    (charts : ∀ p ∈ pieces, BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart
      (F.piece p).anchor σ)
    (e : ℝ) (he : 0 < e) (heE : e ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (timeScale : ℝ) (hclock : timeScale ≠ 0) (hchart : Ks + D ≤ Jchart)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder) (I : DerivativeWord2 (d - 1))
    (r qfast : ℕ) (hr : r ≤ Ks) (hq : qfast ≤ Ls) :
    ∀ᵐ t ∂volume, ∀ X z,
      ‖(F.identity v u γ).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast
          ((sourceConstituent F pieces actual hφ v u γ d (Finset.mem_Icc.mp hd).2 W l σ yc e
            (ocEpsilon q Λ (m - 1)) timeScale).coeff I t Y) z) X‖ ≤
      blockSourceAnalyticJetPrice Ks D Jchart Cchart *
        blockIdentityAnalyticPrice F (ChartedFamily.Domain.onWindow F W) (ocEpsilon q Λ (m - 1)) Ks Ls v u γ := by
  classical
  let C := blockSourceAnalyticJetPrice Ks D Jchart Cchart *
    blockIdentityAnalyticPrice F (ChartedFamily.Domain.onWindow F W) (ocEpsilon q Λ (m - 1)) Ks Ls v u γ
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans (blockSourceAnalyticJetPrice_one_le _ _ _ _))
    ENNReal.toReal_nonneg
  have hall : ∀ᵐ t ∂volume, ∀ p : pieces,
      timeScale * t ∈ (F.piece p.val).output ∩ W → ∀ X z,
      ‖(F.identity v u γ).map‖ * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast
        (blockLetterCoefficient F hφ p.val (actual p.val) v u γ l σ yc e
          (ocEpsilon q Λ (m - 1)) timeScale d I t Y) z) X‖ ≤ C := by
    apply ae_all_iff.mpr
    intro p
    exact blockLetterCoefficient_analytic_ae_bound data p.val (actual p.val) v u γ l σ
      (charts p.val p.property) e he heE yc timeScale hclock hchart d hd I r qfast hr hq
  filter_upwards [hall] with t ht
  intro X z
  let w : P → ℝ := fun p => W.indicator (F.weight p) (timeScale * t)
  have hw (p : P) : 0 ≤ w p := by
    by_cases hW : timeScale * t ∈ W
    · simpa only [w, Set.indicator_of_mem hW] using F.weight_nonneg p (timeScale * t)
    · simp only [w, Set.indicator_of_notMem hW, le_refl]
  let f : P → Vec 2 → Vec 2 → Vec 2 := fun p X z => w p •
    blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e (ocEpsilon q Λ (m - 1)) timeScale d I t X z
  have hf (p : P) : IsBoxSmooth r qfast (f p) :=
    Weighted.isBoxSmooth_of_joint_contDiff r qfast (f p)
      (weightedBlockLetterCoefficient_joint_contDiff data hφ p (actual p) v u γ l σ yc e
        timeScale d I t (r + qfast) (Nat.add_le_add hr hq))
  have hp (p : P) (hp : p ∈ pieces) :
      ‖(F.identity v u γ).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast (f p Y) z) X‖ ≤ w p * C := by
    by_cases hz : w p = 0
    · simp only [f, hz, zero_smul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero, zero_mul, le_refl]
    have hactive := blockWeight_nonzero_mem p (timeScale * t) hz
    have hb : IsBoxSmooth r qfast
        (blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e
          (ocEpsilon q Λ (m - 1)) timeScale d I t) :=
      Weighted.isBoxSmooth_of_joint_contDiff r qfast _
        (blockLetterCoefficient_joint_contDiff data hφ p (actual p) v u γ l σ yc e
          timeScale d I t hactive (r + qfast) (Nat.add_le_add hr hq))
    have heq := mixedJet_dimensional_norm_eq hb (w p) 1 X z
    simp only [abs_one, one_pow, mul_one, one_smul, abs_of_nonneg (hw p)] at heq
    change ‖(F.identity v u γ).map‖ * _ ≤ _
    rw [show ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast (f p Y) z) X‖ = _ from heq]
    rw [← mul_assoc, mul_comm ‖(F.identity v u γ).map‖, mul_assoc]
    exact mul_le_mul_of_nonneg_left (ht ⟨p, hp⟩ hactive X z) (hw p)
  have hsum : (∑ p ∈ pieces, w p) ≤ 1 := by
    by_cases hW : timeScale * t ∈ W
    · simpa only [w, Set.indicator_of_mem hW] using
        family_weight_finset_sum_le_one F pieces (timeScale * t)
    · simp only [w, Set.indicator_of_notMem hW, Finset.sum_const_zero, zero_le_one]
  calc
    _ ≤ ‖(F.identity v u γ).map‖ *
        ∑ p ∈ pieces, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast (f p Y) z) X‖ :=
      mul_le_mul_of_nonneg_left (block_mixed_sum_norm_le pieces f r qfast (fun p _ => hf p) X z)
        (norm_nonneg _)
    _ = ∑ p ∈ pieces, ‖(F.identity v u γ).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ qfast (f p Y) z) X‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ pieces, w p * C := Finset.sum_le_sum hp
    _ = (∑ p ∈ pieces, w p) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ C := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsum hC

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! The finite source budget is charged to original identities, independently of piece counts. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {W : Set ℝ}
  {Ca : ℝ} {Ks Ls : ℕ} {B : ι → ι → ℝ}

/-- Express the indexed list budget using an ordinary list map and sum. -/
theorem blockListAnalyticBudget_eq_map_sum {Hu Hv : Type*}
    [NormedAddCommGroup Hu] [NormedSpace ℝ Hu] [NormedAddCommGroup Hv] [NormedSpace ℝ Hv]
    {d : ℕ} (cs : List (Constituent d Hu Hv)) (dom : Set (ℝ × Vec 2)) (Ks J : ℕ) :
    blockListAnalyticBudget cs dom Ks J =
      (cs.map fun c => ENNReal.ofReal ‖c.map‖ * ∑ I : DerivativeWord2 (d - 1),
        ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1), jetSupOn dom r q (c.coeff I)).sum := by
  let f := fun c : Constituent d Hu Hv => ENNReal.ofReal ‖c.map‖ * ∑ I : DerivativeWord2 (d - 1),
    ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1), jetSupOn dom r q (c.coeff I)
  have he : List.ofFn (fun k => f (cs.get k)) = cs.map f := by
    change List.ofFn (f ∘ cs.get) = cs.map f
    rw [← List.map_ofFn, List.ofFn_get]
  change (∑ k : Fin cs.length, f (cs.get k)) = _
  rw [← List.sum_ofFn, he]

/-- The number of reserved source jets, summed over all permitted orders. -/
def blockSourceJetCount (D Ks J : ℕ) : ℕ :=
  ∑ o : Finset.Icc 2 D, Fintype.card (DerivativeWord2 (o.val - 1)) * (Ks + 1) * (J + 1)

/-- The source envelope price is independent of the graph and the number of pieces. -/
def blockSourceLetterPrice (D Ks J Jchart : ℕ) (Cchart : ℕ → ℝ) (Ca : ℝ) : ℝ :=
  blockSourceJetCount D Ks J * blockSourceAnalyticJetPrice Ks D Jchart Cchart * |Ca|

theorem blockSourceLetterPrice_nonneg (D Ks J Jchart : ℕ) (Cchart : ℕ → ℝ) (Ca : ℝ) :
    0 ≤ blockSourceLetterPrice D Ks J Jchart Cchart Ca :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (zero_le_one.trans (blockSourceAnalyticJetPrice_one_le _ _ _ _))) (abs_nonneg _)

/-- A source edge's full budget is bounded by a finite reserve count times its original prices. -/
theorem blockSourceEdges_analyticBudget_le
    {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (data : BlockLetterAnalyticInputs F π W (ocEpsilon q Λ (m - 1)) Ca Ks Ls B)
    (pieces : Finset P) (actual : ∀ p, Ctx p) (l : ℤ) (σ : ℝ)
    (charts : ∀ p ∈ pieces, BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart
      (F.piece p).anchor σ)
    (e : ℝ) (he : 0 < e) (heE : e ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (timeScale : ℝ) (hclock : timeScale ≠ 0) (hchart : Ks + D ≤ Jchart)
    (J : ℕ) (hJ : J ≤ Ls) (dom : Set (ℝ × Vec 2)) (v u : ι) :
    blockFiberAnalyticBudget
      (blockSourceEdges F pieces actual hφ W l σ yc e (ocEpsilon q Λ (m - 1)) timeScale)
      dom Ks J v u ≤ ENNReal.ofReal ((blockSourceJetCount D Ks J : ℝ) *
        blockSourceAnalyticJetPrice Ks D Jchart Cchart * ∑ γ, blockIdentityAnalyticPrice F
          (ChartedFamily.Domain.onWindow F W) (ocEpsilon q Λ (m - 1)) Ks Ls v u γ) := by
  classical
  let C := blockSourceAnalyticJetPrice Ks D Jchart Cchart
  let Price := fun γ : F.Γ v u => blockIdentityAnalyticPrice F
    (ChartedFamily.Domain.onWindow F W) (ocEpsilon q Λ (m - 1)) Ks Ls v u γ
  let count := fun o : Finset.Icc 2 D =>
    Fintype.card (DerivativeWord2 (o.val - 1)) * (Ks + 1) * (J + 1)
  have hC : 0 ≤ C := zero_le_one.trans (blockSourceAnalyticJetPrice_one_le _ _ _ _)
  have hP (γ : F.Γ v u) : 0 ≤ Price γ := ENNReal.toReal_nonneg
  have ho (o : Finset.Icc 2 D) :
      blockListAnalyticBudget
        (blockSourceEdges F pieces actual hφ W l σ yc e (ocEpsilon q Λ (m - 1)) timeScale v u o)
        dom Ks J ≤ ∑ γ : F.Γ v u, ENNReal.ofReal ((count o : ℝ) * (C * Price γ)) := by
    rw [blockListAnalyticBudget_eq_map_sum]
    unfold blockSourceEdges
    rw [CycleComparison.LiftSetting.list_sum_map_filterMap, Finset.sum_map_toList]
    apply Finset.sum_le_sum
    intro γ _
    by_cases hd : o.val ≤ (F.identity v u γ).maxOrder
    · simp only [hd, dite_true, Option.elim_some]
      have hb := block_constituent_analyticBudget_le
        (sourceConstituent F pieces actual hφ v u γ o.val hd W l σ yc e (ocEpsilon q Λ (m - 1)) timeScale)
        dom Ks J (C * Price γ) (by
          intro I r k hr hk
          apply block_jetSupOn_weighted_le dom r k _ _ _ (norm_nonneg _)
          filter_upwards [sourceConstituent_analytic_ae_bound data pieces actual v u γ l σ charts
            e he heE yc timeScale hclock hchart o.val (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp o.property).1, hd⟩)
            I r k hr (hk.trans hJ)] with t ht
          intro X _ z
          exact ht X z)
      exact hb.trans_eq (by rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)])
    · simp only [hd, dite_false, Option.elim_none, zero_le]
  calc
    _ ≤ ∑ o : Finset.Icc 2 D, ∑ γ : F.Γ v u,
        ENNReal.ofReal ((count o : ℝ) * (C * Price γ)) := Finset.sum_le_sum (fun o _ => ho o)
    _ = ENNReal.ofReal (∑ o : Finset.Icc 2 D, ∑ γ : F.Γ v u,
        (count o : ℝ) * (C * Price γ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => Finset.sum_nonneg (fun γ _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC (hP γ))))]
      apply Finset.sum_congr rfl
      intro o _
      exact (ENNReal.ofReal_sum_of_nonneg (fun γ _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC (hP γ)))).symm
    _ = _ := by
      congr 1
      simp only [← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
      rw [← Nat.cast_sum]
      rfl

/-- The source letter inherits the analytic reserve with the stated graph majorant. -/
theorem blockSourceLetter_analytic
    {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (data : BlockLetterAnalyticInputs F π W (ocEpsilon q Λ (m - 1)) Ca Ks Ls B)
    (pieces : Finset P) (actual : ∀ p, Ctx p) (l : ℤ) (σ : ℝ)
    (charts : ∀ p ∈ pieces, BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart
      (F.piece p).anchor σ)
    (e : ℝ) (he : 0 < e) (heE : e ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (timeScale : ℝ) (hclock : timeScale ≠ 0) (hchart : Ks + D ≤ Jchart)
    (J : ℕ) (hJ : J ≤ Ls) (dom : Set (ℝ × Vec 2)) (C : ℝ)
    (hC : blockSourceLetterPrice D Ks J Jchart Cchart Ca ≤ C) :
    IsAnalyticEnvelope (ChartedFamily.ofFiber
      (blockSourceEdges F pieces actual hφ W l σ yc e (ocEpsilon q Λ (m - 1)) timeScale)) π
      (fun _ _ => dom) 1 1 Ks J (fun v u => C * B v u) := by
  apply block_ofFiber_analyticEnvelope
  · intro v u o c hc I tX _ z
    obtain ⟨γ, hd, rfl⟩ := mem_blockSourceEdges F pieces actual hφ W l σ yc e
      (ocEpsilon q Λ (m - 1)) timeScale v u o c hc
    exact (sourceConstituent_joint_contDiff data hφ pieces actual v u γ l σ yc e timeScale
      o.val hd I tX.1 (Ks + J) (Nat.add_le_add_left hJ Ks)).contDiffAt
  · intro v u
    have hb := blockSourceEdges_analyticBudget_le data pieces actual l σ charts e he heE yc
      timeScale hclock hchart J hJ dom v u
    apply (mul_le_mul' le_rfl hb).trans
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ((blockSourceJetCount D Ks J : ℝ) * blockSourceAnalyticJetPrice Ks D Jchart Cchart) *
          (Real.sqrt (π u / π v) * ∑ γ, blockIdentityAnalyticPrice F
            (ChartedFamily.Domain.onWindow F W) (ocEpsilon q Λ (m - 1)) Ks Ls v u γ) := by ring
      _ ≤ ((blockSourceJetCount D Ks J : ℝ) * blockSourceAnalyticJetPrice Ks D Jchart Cchart) *
          (|Ca| * B v u) := mul_le_mul_of_nonneg_left (blockIdentityAnalyticPrice_sum_le data v u)
            (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (blockSourceAnalyticJetPrice_one_le _ _ _ _)))
      _ = blockSourceLetterPrice D Ks J Jchart Cchart Ca * B v u := by
        unfold blockSourceLetterPrice
        ring
      _ ≤ C * B v u := mul_le_mul_of_nonneg_right hC (data.nonneg v u)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Both renewal block letters satisfy the level-C statement `BlockLettersStatement`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- One uniform constant controls both analytic envelopes on the native chart window. -/
theorem blockLettersAnalytic : BlockLettersAnalyticStatement.{u, v, w, x} := by
  classical
  intro D Kmax Ks Ls Jm Jchart qJ Jstar hJs hqJ hJchart Ca Cm Cchart CG
  let Cs := blockSourceLetterPrice D Ks Jstar Jchart Cchart Ca
  let Cg := blockMetricLetterPrice Ks Jstar CG
  let CL := Cs + Cg
  have hCs : 0 ≤ Cs := blockSourceLetterPrice_nonneg _ _ _ _ _ _
  have hCg : 0 ≤ Cg := blockMetricLetterPrice_nonneg _ _ _
  refine ⟨CL, add_nonneg hCs hCg, ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb y₀
    cov hΛ heE haOld hg0 hD
    ι instFintype instDecidable h instNorm instInner instFinite instMeas instBorel instComplete
    P' Ctx F hmeas hwmeas π hπ K hK actual A Θ Cth H hθ hc hcoverage henv hdepth htransverse
    S hquiet ic a b hab hwindow l σ hσ hσmem hblock
  dsimp only
  let e := ocEpsilon q Λ m
  let E := ocEpsilon q Λ (m - 1)
  let pieces := (F.locally_finite tS tZ).toFinset
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
  have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos hΛ
  have hclock : ν⁻¹ * e ^ 2 ≠ 0 :=
    (mul_pos (inv_pos.mpr cov.pos.1) (sq_pos_of_pos he)).ne'
  let data : BlockLetterAnalyticInputs F π (Set.Icc tS tZ) E Ca Ks Ls
      (fun v u => Real.sqrt (π u / π v) * A v u) :=
    ⟨hE, hπ, henv.nonneg, henv.analytic⟩
  have hcharts (p : P') (hp : p ∈ pieces) : BlockSourceChartInputs α q Λ m (Φ (m - 1)) hφ
      tS tZ Cpad Cage Jchart Cchart (F.piece p).anchor σ := by
    have hp' := (F.locally_finite tS tZ).mem_toFinset.mp hp
    have hg := preparation_piece_anchor_mem_geometry hc p hp'
    rcases hσmem with hl₀ | hσwin
    · have hσ₀ : σ = (l₀ : ℝ) * ocTauPP α q Λ m := by simpa only [hl₀] using hσ
      rw [hσ₀]
      have hh := preparation_reference_anchor_endpoints hc p hp' (Construction.Stream.ocTauPP_pos hΛ).le
      exact ⟨hc.flow, haOld, hh.1, hh.2.1, hh.2.2⟩
    · exact ⟨hc.flow, haOld, hc.schedule.geometry_padded p hp' hg,
        preparation_reference_time_padded hc hcoverage σ hσwin,
        preparation_piece_to_window_reference_age hc hcoverage p hp' _ hg σ hσwin⟩
  constructor
  · exact blockSourceLetter_analytic data pieces actual l σ hcharts e he heE yc
      (ν⁻¹ * e ^ 2) hclock (by omega) Jstar hJs (Set.Icc a b ×ˢ Set.univ) CL
      (le_add_of_nonneg_right hCg)
  · apply blockMetricLetter_analytic π hπ G (E⁻¹ • yc) (e / E) g a b Ks Jstar CG hD
      (div_pos he hE) cov.g_range.1
    · intro t ht i j
      exact (cov.metric_smooth ic t (hwindow ht) i j).of_le (by exact_mod_cast hqJ)
    · intro t ht X
      exact ⟨ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + ic) ν yc t X,
        cov.metric_near ic t (hwindow ht) X⟩
    · intro t ht X j hj hjK i k
      exact cov.metric_jets ic t (hwindow ht) X j hj (hjK.trans (by omega)) i k
    · exact le_add_of_nonneg_left hCs

/-- The metric and source letters of a renewal block satisfy the level-C statement. -/
theorem blockLetters : BlockLettersStatement.{u, v, w, x} :=
  blockLetters_of_analytic blockLettersAnalytic

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The bodies of the block letters and the block transition after their constants**.

`BlockLettersBody` is `BlockLettersStatement` after `∃ CL, 0 ≤ CL ∧`, and `BlockTransitionBody`
is `BlockTransitionStatement` after `∃ CU, 0 < CU ∧`, with the orders and supplied bounds as
parameters; `blockLetters_body` and `blockTransition_body` restate the two statements with them
(by definitional unfolding). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x y

namespace AVRegularity.CycleJointProofs.Assembly

/-- The body of `BlockLettersStatement` after its constant `CL`. -/
def BlockLettersBody (D Kmax Ks Ls Jm Jchart qJ Jstar : ℕ) (Ca : ℝ) (Cm Cchart CG : ℕ → ℝ)
    (CL : ℝ) : Prop :=
  ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
    (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (y₀ : Vec 2)
    (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
      l₀ P y₀)
    (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
    (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
    (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
    (actual : ∀ p, Ctx p) (A : Matrix ι ι ℝ) (Θ Cth : ℝ) (H : ℕ),
    0 ≤ Cth * Θ →
    IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
    (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
    IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ
      (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm →
    F.HasDepthAtMost H →
    F.IsTransverseOnPulses
      (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
        (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS tZ)
      (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1) →
    ∀ S : Set ℝ, F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
    ∀ (ic : Fin (P + 2)) (a b : ℝ), a ≤ b →
    Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
    ∀ (l : ℤ) (σ : ℝ), σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
    (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
  let vd := ocCellDrift α q Λ ζfast m ν yc
  let X₀ := (ocEpsilon q Λ (m - 1))⁻¹ • yc
  let δ := ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)
  let Sl := blockSourceLetter F (F.locally_finite tS tZ).toFinset actual hφ (Set.Icc tS tZ) l σ yc
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * ocEpsilon q Λ m ^ 2) Ks (CL * (Cth * Θ))
    (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
  let Ml := blockMetricLetter (D := D) (h := h) G X₀ δ Ks (CL * g)
    (fun v u => if v = u then CL * g else 0)
  IsCycleLetter π Sl (Set.Icc a b ×ˢ Set.univ) Jstar H ∧
  IsCycleLetter π Ml (Set.Icc a b ×ˢ Set.univ) Jstar H ∧
  (∀ {κ : Type} (pulse : κ → Set ℝ) (orient : κ → Fin 2),
    (∀ p, ∃ k : ℤ, Odd k ∧
      (∀ t ∈ pulse p, |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
      orient p = (if k % 4 = 3 then 0 else 1)) →
    IsTransverseOnPulses Sl.edge pulse orient ∧ IsTransverseOnPulses Ml.edge pulse orient) ∧
  (∀ Q : Set ℝ, (∀ t ∈ Q, ν⁻¹ * ocEpsilon q Λ m ^ 2 * t ∈ S) → (∀ t ∈ Q, ∀ z, vd t z = 0) →
    IsQuietOn Sl.edge vd Q ∧ IsQuietOn Ml.edge vd Q) ∧
  (∀ x y o, ∀ γ ∈ Sl.edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z) ∧
  (∀ x y o, ∀ γ ∈ Ml.edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z)

/-- `BlockLettersStatement` with its body named. -/
theorem blockLetters_body (hL : BlockLettersStatement.{u, v, w, x})
    (D Kmax Ks Ls Jm Jchart qJ Jstar : ℕ) (hJs : Jstar ≤ Ls) (hqJ : Ks + Jstar ≤ qJ)
    (hJchart : Ks + Jstar + D ≤ Jchart) (Ca : ℝ) (Cm Cchart CG : ℕ → ℝ) :
    ∃ CL : ℝ, 0 ≤ CL ∧
      BlockLettersBody.{u, v, w, x} D Kmax Ks Ls Jm Jchart qJ Jstar Ca Cm Cchart CG CL :=
  hL D Kmax Ks Ls Jm Jchart qJ Jstar hJs hqJ hJchart Ca Cm Cchart CG

/-- The body of `BlockTransitionStatement` after its constant `CU`. -/
def BlockTransitionBody (Kmax Jchart : ℕ) (Cchart CG : ℕ → ℝ) (Cpad Cage CU : ℝ) : Prop :=
  ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (tS tZ : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
    (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
    (cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
      l₀ P y₀)
    (hΛ : 1 ≤ Λ) (ha : 0 ≤ ocA α q Λ (m - 1)) (_hg0 : g0 ≤ 1 / 4),
  ∀ {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart
      Cchart l₀ P F)
    (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS tZ)
    (t : ℝ) (ht : t ∈ Set.Icc tS tZ)
    (_htblock : ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m ≤ t ∧
      t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m),
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
    (windowCoverReferenceChartIndex P)
  let ycpost := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
    (windowCoverFollowingChartIndex P cov.P_pos)
  ∃ Υ Υinv : Vec 2 → Vec 2,
    (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (J : ℕ) (hJ : J ≤ Jchart + 1)
      (U : PlaneHk Set.univ J E),
      planeValue (preparationReferenceCellTransitionOperator hprep hcover
        (Construction.Stream.ocTauPP_pos hΛ).le ha J hJ
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc ycpost t ht U) =ᵐ[volume]
        fun z => planeValue U (Υ z)) ∧
    IsCenteredTransition Υ Υinv (g + ocA α q Λ (m - 1) * ocTauPP α q Λ m)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) CU (Jchart + 1) ∧
    ContDiff ℝ (⊤ : ℕ∞) Υinv

/-- `BlockTransitionStatement` with its body named. -/
theorem blockTransition_body (hT : BlockTransitionStatement.{u, v, w, x, y}) (Kmax Jchart : ℕ)
    (Cchart CG : ℕ → ℝ) (Cpad Cage : ℝ) :
    ∃ CU : ℝ, 0 < CU ∧ BlockTransitionBody.{u, v, w, x, y} Kmax Jchart Cchart CG Cpad Cage CU :=
  hT Kmax Jchart Cchart CG Cpad Cage

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Non-quiet outputs retain the renewal-block label of their active pulse. -/

@[expose] public section

open Homogenization AVenhance

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- A nonzero slow envelope lies strictly inside both renewal quiet margins. -/
theorem slowEnvelope_mem_core_of_ne_zero {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (j : ℤ) {t : ℝ} (ht : slowEnvelope α q Λ m j t ≠ 0) :
    t ∈ Set.Ioo (((j : ℝ) - 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m)
      (((j : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) := by
  have hP := EntryScales.ocTauP_pos' (α := α) (q := q) (m := m) hΛ
  have hleft : 0 <
      (t - ((j : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
        ocTauP α q Λ m := by
    by_contra hn
    apply ht
    rw [slowEnvelope, Real.smoothTransition.zero_of_nonpos (not_lt.mp hn), zero_mul]
  have hright : 0 <
      (((j : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
        ocTauP α q Λ m := by
    by_contra hn
    apply ht
    rw [slowEnvelope, Real.smoothTransition.zero_of_nonpos (not_lt.mp hn), mul_zero]
  have hl := (div_pos_iff_of_pos_right hP).mp hleft
  have hr := (div_pos_iff_of_pos_right hP).mp hright
  exact ⟨by linarith only [hl], by linarith only [hr]⟩

/-- Every output outside the trimmed quiet times lies in the open core (margin `τ' - τ/24`) of its
piece's own label: a non-quiet time `s` within `τ/24` carries an active pulse, whose slow envelope
puts `s` in the `τ'`-core of the pulse's block, so `t` is in its `(τ' - τ/24)`-core and
`core_label` gives the piece that label. -/
theorem nonQuietCore : NonQuietCoreStatement.{u, v, w, x} := by
  intro ι h _ _ D P' Ctx α q Λ m hΛ ζ φ hφ tS tZ Cpad Cage Npad l₀ P F hsched
    p t ht htrim
  classical
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  obtain ⟨s, hs, hsq⟩ : ∃ s ∈ Set.Icc (t - ocTau α q Λ m / 24) (t + ocTau α q Λ m / 24),
      s ∉ ocQuietTimes α q Λ ζ m := by
    by_contra hn
    push Not at hn
    exact htrim (Providers.QuietAtlas.mem_ocTrimmedQuietTimes.mpr hn)
  have hpulse : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k s ≠ 0 := by
    by_contra hn
    apply hsq
    intro y
    apply CycleReference.pulseStreamVel_eq_zero_of_quiet
    intro k hk
    by_contra hp
    exact hn ⟨k, hk, hp⟩
  obtain ⟨k, _, hk⟩ := hpulse
  have hslow : slowEnvelope α q Λ m (ocLabel α q Λ m k) s ≠ 0 := by
    intro hz
    exact hk (by rw [ocPulse, hz, zero_mul])
  have hcore := slowEnvelope_mem_core_of_ne_zero hΛ (ocLabel α q Λ m k) hslow
  have hcore' : t ∈ Set.Ioo (((ocLabel α q Λ m k : ℤ) - 1 / 2 : ℝ) * ocTauPP α q Λ m +
      (ocTauP α q Λ m - ocTau α q Λ m / 24))
      (((ocLabel α q Λ m k : ℤ) + 1 / 2 : ℝ) * ocTauPP α q Λ m -
        (ocTauP α q Λ m - ocTau α q Λ m / 24)) := by
    obtain ⟨h1, h2⟩ := hcore
    obtain ⟨h3, h4⟩ := hs
    constructor <;> linarith
  have hlabel := hsched.core_label p t ht (ocLabel α q Λ m k) hcore'
  simpa only [hlabel] using hcore'

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Exact plane/torus preparation ingredient, including the edge-free slot-zero clause. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.PlaneTorus
universe u v w x
namespace AVRegularity.CycleJointProofs.Assembly

/-- Every preparation patch has a physical solution with radial moments; their periodizations
reconstruct every torus solution, also at slot zero when the family has no edges. -/
theorem planeTorus : PlaneTorusStatement.{u, v, w, x} := by
  intro α q Λ ζ hζ hΛ g₀ H D Kmax Ks Ls Jm qJ Jchart _hD hchart hmol
    Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar _hcMol
    ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual
    A Θ T ρold hprem N hN
  constructor
  · intro f
    obtain ⟨U, W, hplane, hmU, _, hall⟩ := preparation_plane_torus_datum hprem hΛ hζ hchart hmol N hN f
    exact ⟨U, W, hplane, hmU, hall⟩
  · intro he f
    have hprem0 := jointPremises_zeroSlots_of_edgeFree hprem he
    obtain ⟨U, W, hplane, hmU, htorus, hall⟩ :=
      preparation_plane_torus_datum hprem0 hΛ hζ hchart hmol N hN f
    exact ⟨htorus, U, W, hplane, hmU, hall⟩

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The following block with an explicit physical endpoint**.

`following_explicit_original_energy_error`: the energy error of the following block, with the
physical endpoint given explicitly as the return to physical variables
(`preparationWindowReferenceCellReturnOperator`) of the given retained endpoint `Tret`. The proof
reads three layers: `preparation_following_mixed_seam_retained_error` for the native bound,
`preparationWindowReferenceRetainedEndpointLinearMap_native_curve_error_le` for the return, and
`twoBlock_original_energy_budget` for the price. The cell time `t` of the endpoint is a binder
with its defining equation, so that callers can pass the time they already have. -/

universe u v w x y

/-- **The following block, explicit physical endpoint.** -/
theorem following_explicit_original_energy_error
    (D Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
      (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hB : ∀ i j, 0 ≤ B i j),
    ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
      (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output),
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS tZ)
      (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H → F.IsDescending K →
    ∀ (ζ : ℝ → ℝ) (Bcover g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ)
      (CG : ℕ → ℝ) (y₀ : Vec 2)
      (cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
      (hΛ : 128 ≤ Λ), IsFastProfile ζ → a ≤ b →
    let ic := windowCoverFollowingChartIndex P cov.P_pos
    Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      max Kmax 1 ≤ qJ → g ≤ 1 / 4 → 2 ≤ D →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let σ := ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    e = ocEpsilon q Λ m →
    IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)) →
    ∀ Nperiod : ℕ, (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ) →
    ∀ (s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      IsAdmissibleQ α s q → IsOCStreamSeq α q Λ ζ Φ → 1 ≤ m →
    ∀ (ha : 0 ≤ ocA α q Λ (m - 1)) (tp : ℝ) (htp : tp ∈ Set.Icc tS tZ),
    a = (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tp) →
    (∀ t ∈ Set.Icc a b,
      (((l₀ + 1 : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ (((l₀ + 1 : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
    let hΛ1 : 1 ≤ Λ := (by omega)
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc0 := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let S := preparationReferenceCellTransitionFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha K (fun i => by have hh := _hK i; omega)
      σ hnext (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 yc tp htp
    ∀ (n : ℕ) (Cw : ℕ → ℝ) (ϖ : ℝ) (_W : ChartWeights G v a (b - a) ϖ 0 n Cw),
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X]
      (Upre Tpre Tret : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hUinit : ∀ ξ i, weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i) ≠ ⊤)
      (_hTinit : ∀ ξ i, weightedFactorialNormSq n ϖ 0 r (K i) (Tpre ξ i) ≠ ⊤)
      (Uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uwphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (V : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Vw : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ ξ, ∃ f : ∀ i, PlaneHk Set.univ (K i) (h i),
      IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
        (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K)
        f (fun _ _ => 0) (fun _ _ => 0) (Uphys ξ) (Uwphys ξ)) →
    (∀ ξ i, Upre ξ i = preparationReferenceCellNativeCurve hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (by have hh := _hK i; omega)
      ν (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 (Uphys ξ i) a) →
    (∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      (S (Tpre ξ)) (fun _ _ => 0) (fun _ _ => 0) (V ξ) (Vw ξ)) →
    ∀ (tphys : ℝ) (_htphys : tphys ∈ Set.Icc tS tZ),
      (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tphys) ∈ Set.Icc a b →
    ∀ (t : ℝ), t = (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tphys) →
    let EinPre := fun ξ => ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i - Tpre ξ i)
    let Cjet := fun j => max (CG j) 0
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    ∀ (Aerr : X → ℝ≥0∞),
    (∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (V ξ i t - Tret ξ i)) ≤ Aerr ξ) →
    ∀ (N : ℕ) (Ein : X → ℝ≥0∞) (Cfirst εlow εhigh εpost : ℝ≥0∞),
    (∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq N ϖ 0 r (K i) (Upre ξ i)) ≤ Cfirst * Ein ξ) →
    (∀ ξ, EinPre ξ ≤ εlow * Ein ξ) →
    (∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq N ϖ 0 r (K i) (Upre ξ i - Tpre ξ i)) ≤ εhigh * Ein ξ) →
    (∀ ξ, Aerr ξ ≤ εpost * (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq N ϖ 0 r (K i) (Tpre ξ i))) →
    ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (Uphys ξ i tphys - preparationWindowReferenceCellReturnOperator hprep hcover σ hnext ha
        (K i) (by have hh := _hK i; omega) (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc tphys _htphys (Tret ξ i)).val) ≤
      twoBlockOriginalEnergyPrice
        (ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) * |ocEpsilon q Λ m|) ^ 2)) Cactual
        (ENNReal.ofReal (cellTransitionMomentBudget Kmax n)) Cfirst εlow εhigh εpost * Ein ξ
 := by
  obtain ⟨Cprep, hCprep, hbase⟩ := preparation_following_mixed_seam_retained_error
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
    hnext a b θ hsub hrow hcol H hdepth hdesc ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov hΛ
    hζ hab ic hwindow hqJ hg4 hD yc G v r σ A he htorus Nperiod hperiod
    s hα0 hα1 hs0 hs1 hq hseq hm ha tp htp htime hblock hΛ1 seed yc0 S
    n Cw ϖ W X _ _ Upre Tpre Tret hUinit hTinit Uphys Uwphys V Vw hphysical htrace hV
    tphys htphys ht t htdef EinPre Cjet Cactual Aerr herr N Ein Cfirst εlow εhigh εpost
    hfirst hlow hhigh hpost
  rw [htdef] at herr
  let U := fun ξ i => preparationWindowReferenceCellNativeCurve hprep hcover σ hnext ha
    (K i) (by have hh := hK i; omega) ν (ocEpsilon q Λ m)
    (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc (Uphys ξ i)
  let Uw := fun ξ i => preparationWindowReferenceCellNativeCurve hprep hcover σ hnext ha
    (K i + 1) (by have hh := hK i; omega) ν (ocEpsilon q Λ m)
    (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc (Uwphys ξ i)
  have hρe' : ρ ≤ ocEpsilon q Λ m := he ▸ hρe
  have heE' : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := he ▸ heE
  have henv' := henv
  rw [he] at henv'
  have hsub' := hsub
  rw [he] at hsub'
  have hU (ξ : X) : IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (S (Upre ξ))
      (fun _ _ => 0) (fun _ _ => 0) (U ξ) (Uw ξ) := by
    obtain ⟨f, hs⟩ := hphysical ξ
    rw [he] at hs
    have hb := preparation_window_reference_cell_coupled_solution_on_actual_mixed_seam
      F (htp.1.trans htp.2) (fun _ ht => ht) ρ hρ K hdesc hD hprep hcover
      (l₀ + 1) hnext ha Kmax Jm hK hchart hmol Cm π hπ B hB hmeas hwmeas
      hΛ1 hm hseq ν (ocEpsilon q Λ m) hν rfl hρe' heE' henv' actual htorus hperiod
      yc f (Uphys ξ) (Uwphys ξ) a b (hsub' ⟨le_rfl, hab⟩).1 hab
      (hsub' ⟨hab, le_rfl⟩).2 hblock hs
      (Construction.Stream.ocTauPP_pos hΛ1).le yc0 tp htp htime
    dsimp only at hb
    have hid : (fun i => preparationReferenceCellNativeCurve hprep hcover
        (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (by have hh := hK i; omega)
        ν (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 (Uphys ξ i) a) =
        Upre ξ :=
      funext (fun i => (htrace ξ i).symm)
    rw [hid] at hb
    dsimp only [G, windowCoverCellMetric]
    rw [windowCoverFollowingChartIndex_label]
    simpa only [A, he, σ, S, U, Uw, v] using hb
  have hnative (ξ : X) :
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
        (U ξ i ((ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tphys)) - Tret ξ i)) ≤
        2 * (Cactual * (ENNReal.ofReal (cellTransitionMomentBudget Kmax n) * EinPre ξ) + Aerr ξ) :=
    hbase α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv hnext
      a b θ hsub hrow hcol H hdepth ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov hΛ
      hζ hab hwindow hqJ hg4 hD he s hα0 hα1 hs0 hs1 hq hseq hm ha tp htp
      n Cw ϖ W (Upre ξ) (Tpre ξ) (hUinit ξ) (hTinit ξ) (U ξ) (V ξ) (Uw ξ) (Vw ξ)
      (hU ξ) (hV ξ) _ ht (Tret ξ) (Aerr ξ) (herr ξ)
  intro ξ
  exact twoBlock_original_energy_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hfirst ξ) (hlow ξ) (hhigh ξ)
    (planeFamily_polynomial_energy_of_approximation_le K π N ϖ 0 r (Upre ξ) (Tpre ξ))
    (hpost ξ)
    ((preparationWindowReferenceRetainedEndpointLinearMap_native_curve_error_le
      hprep hcover σ hnext ha K (fun i => by have hh := hK i; omega)
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc tphys htphys
      ν hν.ne' π hπ (Construction.Stream.ocEpsilon_pos hΛ1) hρ.le (hρe.trans heE)
      n ϖ Tret ξ (Uphys ξ)).trans (mul_le_mul_right (hnative ξ) _))

end AVRegularity.CycleJointProofs.Assembly
end
end
