-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePairing
import AVRegularity.Construction.InitialValue.Cascade
public import AVRegularity.CycleComparison.Coarse.Fact.GradWord
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleWords.CellTransitionLipschitz
public import AVRegularity.Definitions.Entry.TerminalResidualClauses
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public noncomputable section

section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Time step of `ReadoutStrongEquationStatement`: an integrable function whose integrals over
all `(tp, t]` vanish is almost everywhere zero (Lebesgue differentiation). -/

theorem roStr_ae_zero_of_primitive_zero {tp tf : ℝ} (hle : tp ≤ tf) {G : ℝ → ℝ}
    (hG : IntegrableOn G (Ioc tp tf))
    (h0 : ∀ t ∈ Icc tp tf, ∫ s in Ioc tp t, G s = 0) :
    ∀ᵐ s ∂(volume.restrict (Icc tp tf)), G s = 0 := by
  have hI : IntervalIntegrable G volume tp tf :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr hG
  have hd := hI.ae_hasDerivAt_integral
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ tf := by simp [ae_iff, measure_singleton]
  have hne' : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ tp := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hd, hne, hne'] with x hx h1 h2 hxm
  have hx' : x ∈ Ioo tp tf := ⟨lt_of_le_of_ne hxm.1 (Ne.symm h2), lt_of_le_of_ne hxm.2 h1⟩
  have hmem : x ∈ uIcc tp tf := by rw [uIcc_of_le hle]; exact hxm
  have hder := hx hmem tp (by rw [uIcc_of_le hle]; exact ⟨le_rfl, hle⟩)
  have hev : (fun y => ∫ t in tp..y, G t) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
    rw [intervalIntegral.integral_of_le hy.1.le]
    exact h0 y ⟨hy.1.le, hy.2.le⟩
  have hz : HasDerivAt (fun y => ∫ t in tp..y, G t) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  exact hder.unique hz

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Continuous linear maps commute with the covariance operator, its iterates and the
polynomials `P_p`, `Q_p`, at the finite regularity that each of them consumes. This is used to
read a vector-valued flux componentwise. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map commutes with the covariance operator on `C²` fields. -/
theorem covProj_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) (L : E →L[ℝ] F) {h : Vec 2 → E}
    (hh : ContDiff ℝ 2 h) (x : Vec 2) :
    L (covOperator Hc h x) = covOperator Hc (fun y => L (h y)) x := by
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hj : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => fderiv ℝ h y (basisVec j)) := fun j =>
    (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have e1 : ∀ j : Fin 2, (fun y => fderiv ℝ (fun z => L (h z)) y (basisVec j)) =
      fun y => L (fderiv ℝ h y (basisVec j)) := fun j => by
    funext y
    have h' : HasFDerivAt (fun z => L (h z)) (L.comp (fderiv ℝ h y)) y :=
      L.hasFDerivAt.comp y (hd y).hasFDerivAt
    rw [h'.fderiv]
    rfl
  have e2 : ∀ i j : Fin 2, fderiv ℝ (fun y => L (fderiv ℝ h y (basisVec j))) x (basisVec i) =
      L (fderiv ℝ (fun y => fderiv ℝ h y (basisVec j)) x (basisVec i)) := fun i j => by
    have h' : HasFDerivAt (fun y => L (fderiv ℝ h y (basisVec j)))
        (L.comp (fderiv ℝ (fun y => fderiv ℝ h y (basisVec j)) x)) x :=
      L.hasFDerivAt.comp x (((hj j).differentiable one_ne_zero) x).hasFDerivAt
    rw [h'.fderiv]
    rfl
  simp only [covOperator, map_sum, map_smul, e1, e2]

/-- Iterates: `L (𝒞^l f) = 𝒞^l (L f)` for `f ∈ C^{2l}`. -/
theorem covProj_covIter (Hc : Matrix (Fin 2) (Fin 2) ℝ) (L : E →L[ℝ] F) :
    ∀ (l : ℕ) {f : Vec 2 → E}, ContDiff ℝ ((2 * l : ℕ) : ℕ∞) f → ∀ x,
      L ((covOperator Hc)^[l] f x) = (covOperator Hc)^[l] (fun y => L (f y)) x
  | 0, _, _, _ => rfl
  | l + 1, f, hf, x => by
    have hl : ContDiff ℝ ((2 * l : ℕ) : ℕ∞) f :=
      hf.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * (l + 1)))
    have h2 : ContDiff ℝ 2 ((covOperator Hc)^[l] f) :=
      FullLift.covOperator_iterate_contDiff Hc l 2 f (by
        have : (2 + 2 * l : ℕ) = 2 * (l + 1) := by omega
        rw [this]; exact hf)
    have e : (fun y => L ((covOperator Hc)^[l] f y)) =
        (covOperator Hc)^[l] (fun y => L (f y)) := funext (covProj_covIter Hc L l hl)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      covProj_covOperator Hc L h2, e]

theorem covProj_covPolyP (Hc : Matrix (Fin 2) (Fin 2) ℝ) (L : E →L[ℝ] F) (p : ℕ)
    {f : Vec 2 → E} (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) (x : Vec 2) :
    L (covPolyP Hc p f x) = covPolyP Hc p (fun y => L (f y)) x := by
  simp only [covPolyP, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [covProj_covIter Hc L l ((hf.of_le (by
    exact_mod_cast (by have := Finset.mem_range.mp hl; omega : 2 * l ≤ 2 * p)))) x]

theorem covProj_covPolyQ (Hc : Matrix (Fin 2) (Fin 2) ℝ) (L : E →L[ℝ] F) (p : ℕ)
    {f : Vec 2 → E} (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) (x : Vec 2) :
    L (covPolyQ Hc p f x) = covPolyQ Hc p (fun y => L (f y)) x := by
  simp only [covPolyQ, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [covProj_covIter Hc L l ((hf.of_le (by
    exact_mod_cast (by have := Finset.mem_range.mp hl; omega : 2 * l ≤ 2 * p)))) x]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Time step of `MacroWeakFromStrongStatement`: the time primitive of a derivative field with
an integrable uniform bound, paired with a continuous test and integrated over the cell,
equals the iterated integral of the pairings (Fubini). -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A jointly measurable field on the window has a globally measurable extension. -/
theorem macroWeakTime_extension (tp tf : ℝ) (da : ℝ → Vec 2 → E)
    (hmeas : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} => da z.1.1 z.1.2)) :
    ∃ dq : ℝ × Vec 2 → E, Measurable dq ∧ ∀ z : ℝ × Vec 2, z.1 ∈ Set.Icc tp tf →
      dq z = da z.1 z.2 := by
  have hS : MeasurableSet {z : ℝ × Vec 2 | z.1 ∈ Set.Icc tp tf} :=
    measurable_fst measurableSet_Icc
  have he : MeasurableEmbedding
      (Subtype.val : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} → ℝ × Vec 2) :=
    MeasurableEmbedding.subtype_coe hS
  refine ⟨Function.extend Subtype.val (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} =>
    da z.1.1 z.1.2) (fun _ => 0), he.measurable_extend hmeas measurable_const, fun z hz => ?_⟩
  exact he.injective.extend_apply (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} =>
    da z.1.1 z.1.2) (fun _ => 0) ⟨z, hz⟩

theorem macroWeakTime_cube_measurable : MeasurableSet AVenhance.unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- Fubini for the time primitive. -/
theorem macroWeakTime (tp tf t : ℝ) (ht : t ∈ Set.Icc tp tf) (a da : ℝ → Vec 2 → E)
    (φ : Vec 2 → E) (hφ : Continuous φ)
    (hprim : ∀ x, ∀ s ∈ Set.Icc tp tf, a s x - a tp x = ∫ r in Set.Ioc tp s, da r x)
    (hmeas : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} => da z.1.1 z.1.2))
    (hB : ∃ B : ℝ → ℝ, IntegrableOn B (Set.Icc tp tf) ∧
      ∀ s ∈ Set.Icc tp tf, ∀ x ∈ AVenhance.unitCube, ‖da s x‖ ≤ B s)
    (hat : Integrable (fun x => inner ℝ (a t x) (φ x)) (volume.restrict AVenhance.unitCube))
    (hatp : Integrable (fun x => inner ℝ (a tp x) (φ x)) (volume.restrict AVenhance.unitCube)) :
    Integrable (fun p : Vec 2 × ℝ => inner ℝ (da p.2 p.1) (φ p.1))
        ((volume.restrict AVenhance.unitCube).prod (volume.restrict (Set.Ioc tp t))) ∧
      ((∫ x in AVenhance.unitCube, inner ℝ (a t x) (φ x)) -
        ∫ x in AVenhance.unitCube, inner ℝ (a tp x) (φ x) =
        ∫ s in Set.Ioc tp t, ∫ x in AVenhance.unitCube, inner ℝ (da s x) (φ x)) ∧
      IntegrableOn (fun s => ∫ x in AVenhance.unitCube, inner ℝ (da s x) (φ x))
        (Set.Ioc tp t) := by
  obtain ⟨dq, hdq, hdqe⟩ := macroWeakTime_extension tp tf da hmeas
  obtain ⟨B, hBint, hBb⟩ := hB
  obtain ⟨C, hC0, hC⟩ := AVRegularity.CoupledEnergy.Galerkin.continuous_unitCube_bound φ hφ
  have hsub : Set.Ioc tp t ⊆ Set.Icc tp tf := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hBI : IntegrableOn B (Set.Ioc tp t) := hBint.mono_set hsub
  have hcube := macroWeakTime_cube_measurable
  -- the product integrability
  have hmajor : Integrable (fun p : Vec 2 × ℝ => C * B p.2)
      ((volume.restrict AVenhance.unitCube).prod (volume.restrict (Set.Ioc tp t))) :=
    (AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable (fun _ => C)
      continuous_const).mul_prod hBI
  have hmeasP : AEStronglyMeasurable (fun p : Vec 2 × ℝ => inner ℝ (dq (p.2, p.1)) (φ p.1))
      ((volume.restrict AVenhance.unitCube).prod (volume.restrict (Set.Ioc tp t))) :=
    ((hdq.comp measurable_swap).aestronglyMeasurable.inner
      (hφ.comp continuous_fst).aestronglyMeasurable)
  have hbound : ∀ᵐ p ∂((volume.restrict AVenhance.unitCube).prod
      (volume.restrict (Set.Ioc tp t))), ‖inner ℝ (dq (p.2, p.1)) (φ p.1)‖ ≤ C * B p.2 := by
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (hcube.prod measurableSet_Ioc) fun p hp => ?_
    have h1 := hBb p.2 (hsub hp.2) p.1 hp.1
    have h2 := hC p.1 hp.1
    rw [hdqe (p.2, p.1) (hsub hp.2)]
    calc ‖inner ℝ (da p.2 p.1) (φ p.1)‖ ≤ ‖da p.2 p.1‖ * ‖φ p.1‖ := norm_inner_le_norm _ _
      _ ≤ B p.2 * C := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = C * B p.2 := mul_comm _ _
  have hPdq := hmajor.mono' hmeasP hbound
  have hP : Integrable (fun p : Vec 2 × ℝ => inner ℝ (da p.2 p.1) (φ p.1))
      ((volume.restrict AVenhance.unitCube).prod (volume.restrict (Set.Ioc tp t))) := by
    refine hPdq.congr ?_
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (hcube.prod measurableSet_Ioc) fun p hp => ?_
    simp only [hdqe (p.2, p.1) (hsub hp.2)]
  -- per-point integrability in time
  have hint : ∀ x ∈ AVenhance.unitCube, Integrable (fun s => da s x) (volume.restrict (Set.Ioc tp t)) := by
    intro x hx
    have hm : AEStronglyMeasurable (fun s => dq (s, x)) (volume.restrict (Set.Ioc tp t)) :=
      (hdq.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hb : ∀ᵐ s ∂(volume.restrict (Set.Ioc tp t)), ‖dq (s, x)‖ ≤ B s := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      rw [hdqe (s, x) (hsub hs)]
      exact hBb s (hsub hs) x hx
    refine (hBI.mono' hm hb).congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
    exact hdqe (s, x) (hsub hs)
  refine ⟨hP, ?_, hP.integral_prod_right⟩
  have hpt : ∀ x ∈ AVenhance.unitCube, inner ℝ (a t x) (φ x) - inner ℝ (a tp x) (φ x) =
      ∫ s in Set.Ioc tp t, inner ℝ (da s x) (φ x) := by
    intro x hx
    rw [← inner_sub_left, hprim x t ht, real_inner_comm]
    rw [← integral_inner (hint x hx) (φ x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => real_inner_comm _ _)
  rw [← integral_sub hat hatp]
  rw [setIntegral_congr_fun hcube hpt]
  exact integral_integral_swap (f := fun x s => inner ℝ (da s x) (φ x)) hP

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! A countable family of smooth periodic real tests that separates continuous periodic
functions (step of `ReadoutStrongEquationStatement`): a continuous periodic function with
vanishing cell pairings against every member of the family vanishes everywhere. -/

/-- The smooth periodic real test functions. -/
def roStrTestSet : Set (Vec 2 → ℝ) :=
  {g | ContDiff ℝ (⊤ : ℕ∞) g ∧ IsZ2Periodic g}

/-- The closed unit cell. -/
def roStrClosedCell : Set (Vec 2) := Set.Icc (0 : Vec 2) 1

theorem roStr_closedCell_compact : IsCompact roStrClosedCell := isCompact_Icc

/-- Restriction of a continuous function to the closed cell. -/
def roStrRestrict (g : Vec 2 → ℝ) (hg : Continuous g) : C(roStrClosedCell, ℝ) :=
  ⟨fun p => g p, hg.comp continuous_subtype_val⟩

theorem roStr_exists_countable_tests :
    ∃ T : ℕ → Vec 2 → ℝ, (∀ n, T n ∈ roStrTestSet) ∧ ∀ g ∈ roStrTestSet, ∀ ε > 0, ∃ n,
      ∀ x ∈ roStrClosedCell, |g x - T n x| < ε := by
  have : CompactSpace roStrClosedCell := isCompact_iff_compactSpace.mp roStr_closedCell_compact
  let r : roStrTestSet → C(roStrClosedCell, ℝ) := fun g =>
    roStrRestrict g.1 (g.2.1.continuous)
  have hsep : TopologicalSpace.IsSeparable (Set.range r) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨t, htsub, htc, htd⟩ := hsep.exists_countable_dense_subset
  have hne : (0 : Vec 2 → ℝ) ∈ roStrTestSet :=
    ⟨contDiff_const, fun n x => rfl⟩
  have htne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    subst h
    simp only [closure_empty, Set.subset_empty_iff] at htd
    exact Set.range_nonempty_iff_nonempty.mpr ⟨⟨0, hne⟩⟩ |>.ne_empty htd
  obtain ⟨f, hf⟩ := htc.exists_eq_range htne
  have hfr : ∀ n, ∃ g : roStrTestSet, r g = f n := fun n => by
    have : f n ∈ t := by rw [hf]; exact Set.mem_range_self n
    exact htsub this
  choose G hG using hfr
  refine ⟨fun n => (G n).1, fun n => (G n).2, fun g hg ε hε => ?_⟩
  have hmem : r ⟨g, hg⟩ ∈ closure t := htd ⟨_, rfl⟩
  rw [hf, Metric.mem_closure_iff] at hmem
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hmem ε hε
  refine ⟨n, fun x hx => ?_⟩
  rw [← hG n] at hn
  have := ContinuousMap.dist_apply_le_dist (f := r ⟨g, hg⟩) (g := r (G n)) ⟨x, hx⟩
  rw [Real.dist_eq] at this
  exact lt_of_le_of_lt this hn

theorem roStr_cell_integrable {F g : Vec 2 → ℝ} (hF : Continuous F) (hg : Continuous g) :
    IntegrableOn (fun x => F x * g x) AVenhance.unitCube :=
  AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ (hF.mul hg)

theorem roStr_unitCube_subset : AVenhance.unitCube ⊆ roStrClosedCell := fun _ hx =>
  ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩

/-- A continuous periodic function orthogonal to all tests of the family vanishes on the cell. -/
theorem roStr_pairing_zero_of_tests {F : Vec 2 → ℝ} (hF : Continuous F)
    (T : ℕ → Vec 2 → ℝ) (hT : ∀ n, T n ∈ roStrTestSet)
    (hd : ∀ g ∈ roStrTestSet, ∀ ε > 0, ∃ n, ∀ x ∈ roStrClosedCell, |g x - T n x| < ε)
    (h0 : ∀ n, ∫ x in AVenhance.unitCube, F x * T n x = 0) :
    ∀ g ∈ roStrTestSet, ∫ x in AVenhance.unitCube, F x * g x = 0 := by
  intro g hg
  obtain ⟨C, hC⟩ := roStr_closedCell_compact.exists_bound_of_continuousOn hF.continuousOn
  set V : ℝ := (volume AVenhance.unitCube).toReal with hV
  have hVfin : volume AVenhance.unitCube < ⊤ :=
    (measure_mono roStr_unitCube_subset).trans_lt (roStr_closedCell_compact.measure_lt_top)
  have hbd : ∀ ε > 0, |∫ x in AVenhance.unitCube, F x * g x| ≤ (|C| * V + 1) * ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := hd g hg ε hε
    have hdiff : ∫ x in AVenhance.unitCube, F x * g x =
        ∫ x in AVenhance.unitCube, F x * (g x - T n x) := by
      have := h0 n
      rw [← sub_zero (∫ x in AVenhance.unitCube, F x * g x), ← this, ← integral_sub
        (roStr_cell_integrable hF hg.1.continuous)
        (roStr_cell_integrable hF (hT n).1.continuous)]
      congr 1; funext x; ring
    rw [hdiff]
    have hle : ‖∫ x in AVenhance.unitCube, F x * (g x - T n x)‖ ≤ (|C| * ε) * V := by
      change _ ≤ (|C| * ε) * volume.real AVenhance.unitCube
      refine norm_setIntegral_le_of_norm_le_const (C := |C| * ε) hVfin (fun x hx => ?_)
      have hx' := roStr_unitCube_subset hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul ((hC x hx').trans (le_abs_self C)) (hn x hx').le (abs_nonneg _)
        (abs_nonneg _)
    rw [← Real.norm_eq_abs]
    refine hle.trans ?_
    have : 0 ≤ V := ENNReal.toReal_nonneg
    nlinarith [abs_nonneg C]
  by_contra hne
  have hpos : 0 < |∫ x in AVenhance.unitCube, F x * g x| := abs_pos.mpr hne
  have hden : 0 < |C| * V + 1 := by
    have : 0 ≤ V := ENNReal.toReal_nonneg
    positivity
  have := hbd (|∫ x in AVenhance.unitCube, F x * g x| / (2 * (|C| * V + 1)))
    (by positivity)
  have h2 : (|C| * V + 1) * (|∫ x in AVenhance.unitCube, F x * g x| / (2 * (|C| * V + 1))) =
      |∫ x in AVenhance.unitCube, F x * g x| / 2 := by field_simp
  linarith

theorem roStr_zero_of_tests {F : Vec 2 → ℝ} (hF : Continuous F) (hFp : IsZ2Periodic F)
    (h : ∀ g ∈ roStrTestSet, ∫ x in AVenhance.unitCube, F x * g x = 0) : ∀ x, F x = 0 := by
  have hae : F =ᵐ[volume.restrict AVenhance.unitCube] (fun _ => (0 : ℝ)) := by
    refine AVRegularity.InitialValue.ae_eq_of_cellInner_eq
      (AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable F hF)
      (integrableOn_const (C := (0 : ℝ)) (ne_of_lt ((measure_mono roStr_unitCube_subset).trans_lt
        (roStr_closedCell_compact.measure_lt_top)))) ?_
    intro φ hφ hφp
    have := h φ ⟨hφ, hφp⟩
    simp only [cellInner, RCLike.inner_apply, conj_trivial]
    simpa [mul_comm] using this
  have hcube : ∀ x ∈ AVenhance.unitCube, F x = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x0, hx0, hne⟩ := hcon
    have hopen : IsOpen ({y | F y ≠ 0} ∩ AVenhance.unitCube) :=
      (isOpen_ne_fun hF continuous_const).inter AVRegularity.InitialValue.isOpen_unitCube
    have hmeas0 : volume ({y | F y ≠ 0} ∩ AVenhance.unitCube) = 0 := by
      have := (ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)).mp hae
      rw [ae_iff] at this
      refine measure_mono_null ?_ this
      intro y hy hc
      exact hy.1 (hc hy.2)
    rw [hopen.measure_eq_zero_iff volume] at hmeas0
    exact (Set.eq_empty_iff_forall_notMem.mp hmeas0) x0 ⟨hne, hx0⟩
  have hclosed : IsClosed {y | F y = 0} := isClosed_eq hF continuous_const
  have hcl : roStrClosedCell ⊆ {y | F y = 0} := by
    have hsub : roStrClosedCell ⊆ closure AVenhance.unitCube := by
      unfold AVenhance.unitCube roStrClosedCell
      rw [closure_pi_set]
      intro x hx i _
      rw [closure_Ioo (by norm_num)]
      exact ⟨hx.1 i, hx.2 i⟩
    exact hsub.trans (closure_minimal hcube hclosed)
  intro x
  have hx : (fun i => Int.fract (x i)) ∈ roStrClosedCell :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have := hFp (fun i => ⌊x i⌋) (fun i => Int.fract (x i))
  have hsum : (fun i => Int.fract (x i)) + latticeShift (fun i => ⌊x i⌋) = x := by
    funext i; exact Int.fract_add_floor (x i)
  rw [hsum] at this
  rw [this]
  exact hcl hx

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! The scalar-component core of the covariance mean reduction: `P_p` moves inside a divergence,
and the divergence of a finite combination is the combination of the divergences. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem meanCore_op_add {N : ℕ} {T : (Vec 2 → E) → (Vec 2 → E)} (hT : ConstCoefOp N T)
    {f g : Vec 2 → E} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (hg : ContDiff ℝ (N : WithTop ℕ∞) g) :
    T (fun x => f x + g x) = fun x => T f x + T g x := by
  have := hT.sum Finset.univ ![f, g] (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using this

theorem meanCore_op_neg_add {N : ℕ} {T : (Vec 2 → E) → (Vec 2 → E)} (hT : ConstCoefOp N T)
    {f g : Vec 2 → E} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (hg : ContDiff ℝ (N : WithTop ℕ∞) g) :
    T (fun x => -(f x + g x)) = fun x => -(T f x + T g x) := by
  have h1 := hT.smul (-1) (fun x => f x + g x) (hf.add hg)
  rw [meanCore_op_add hT hf hg] at h1
  have e : (fun x => -(f x + g x)) = fun x => (-1 : ℝ) • (f x + g x) := by
    funext x; exact (neg_one_smul ℝ _).symm
  rw [e, h1]
  funext x
  simp only [neg_smul, one_smul]

theorem meanCore_partial_combo {a b c d : Vec 2 → E} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hc : ContDiff ℝ 1 c) (hd : ContDiff ℝ 1 d) (j : Fin 2) (x : Vec 2) :
    partialOp j (fun y => a y - b y - c y - d y) x =
      partialOp j a x - partialOp j b x - partialOp j c x - partialOp j d x := by
  have h : HasFDerivAt (fun y => a y - b y - c y - d y) _ x := ((((ha.differentiable one_ne_zero x).hasFDerivAt.sub
    (hb.differentiable one_ne_zero x).hasFDerivAt).sub
    (hc.differentiable one_ne_zero x).hasFDerivAt).sub
    (hd.differentiable one_ne_zero x).hasFDerivAt)
  change fderiv ℝ (fun y => a y - b y - c y - d y) x (basisVec j) = _
  rw [h.fderiv]
  rfl

theorem meanCore_partial_neg_add {b c : Vec 2 → E} (hb : ContDiff ℝ 1 b)
    (hc : ContDiff ℝ 1 c) (j : Fin 2) (x : Vec 2) :
    partialOp j (fun y => -(b y + c y)) x = -(partialOp j b x + partialOp j c x) := by
  have h : HasFDerivAt (fun y => -(b y + c y)) _ x := ((hb.differentiable one_ne_zero x).hasFDerivAt.add
    (hc.differentiable one_ne_zero x).hasFDerivAt).neg
  change fderiv ℝ (fun y => -(b y + c y)) x (basisVec j) = _
  rw [h.fderiv]
  rfl

/-- The core identity, with `g_j` the components of the readout flux, `u_j` of `Υ` and `l_j`
of the last flux. -/
theorem meanCore_identity (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (g u l : Fin 2 → Vec 2 → E)
    (hg : ∀ j, ContDiff ℝ ((4 * p + 2 : ℕ) : WithTop ℕ∞) (g j))
    (hu : ∀ j, ContDiff ℝ ((2 * p + 2 : ℕ) : WithTop ℕ∞) (u j))
    (hl : ∀ j, ContDiff ℝ 1 (l j)) (x : Vec 2) :
    covPolyP Hc p (fun y => ∑ j : Fin 2, partialOp j
        (fun z => -(covPolyQ Hc p (g j) z + u j z)) y) x +
      ∑ j : Fin 2, partialOp j (g j) x - ∑ j : Fin 2, partialOp j (l j) x =
    ∑ j : Fin 2, partialOp j (fun y => g j y - covPolyP Hc p (covPolyQ Hc p (g j)) y
        - covPolyP Hc p (u j) y - l j y) x := by
  have hP := ConstCoefOp.covPolyP (E := E) Hc p
  have hQ := ConstCoefOp.covPolyQ (E := E) Hc p
  have hQg : ∀ j, ContDiff ℝ ((2 * p + 2 : ℕ) : WithTop ℕ∞) (covPolyQ Hc p (g j)) := fun j =>
    hQ.reg (2 * p + 2) (g j) (by
      have : 2 * p + 2 + 2 * p = 4 * p + 2 := by omega
      rw [this]; exact hg j)
  have hmono : ∀ {f : Vec 2 → E}, ContDiff ℝ ((2 * p + 2 : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) f := fun hf => hf.of_le (Nat.cast_le.mpr (by omega : 2 * p ≤ 2 * p + 2))
  have hr : ∀ j, ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞)
      (fun z => -(covPolyQ Hc p (g j) z + u j z)) := fun j =>
    (((hQg j).of_le (Nat.cast_le.mpr (by omega))).add
      ((hu j).of_le (Nat.cast_le.mpr (by omega)))).neg
  have hdiv := hP.div (g := fun j z => -(covPolyQ Hc p (g j) z + u j z)) hr
    (f := fun y => ∑ j : Fin 2, partialOp j (fun z => -(covPolyQ Hc p (g j) z + u j z)) y) rfl
  rw [hdiv]
  have hPr : ∀ j, covPolyP Hc p (fun z => -(covPolyQ Hc p (g j) z + u j z)) =
      fun y => -(covPolyP Hc p (covPolyQ Hc p (g j)) y + covPolyP Hc p (u j) y) := fun j =>
    meanCore_op_neg_add hP (hmono (hQg j)) (hmono (hu j))
  have hPQ : ∀ j, ContDiff ℝ 1 (covPolyP Hc p (covPolyQ Hc p (g j))) := fun j =>
    hP.reg 1 _ ((hQg j).of_le (Nat.cast_le.mpr (by omega)))
  have hPu : ∀ j, ContDiff ℝ 1 (covPolyP Hc p (u j)) := fun j =>
    hP.reg 1 _ ((hu j).of_le (Nat.cast_le.mpr (by omega)))
  have hg1 : ∀ j, ContDiff ℝ 1 (g j) := fun j => (hg j).of_le (Nat.cast_le.mpr (by omega : 1 ≤ 4 * p + 2))
  simp only [hPr, meanCore_partial_neg_add (hPQ _) (hPu _),
    meanCore_partial_combo (hg1 _) (hPQ _) (hPu _) (hl _)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  abel

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open Homogenization AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Finite-regularity commutation of the covariance operators with each other, and additivity of
constant-coefficient operators on binary sums. They are the finite-regularity versions of smooth
statements such as `partialOp_partialOp_covOperator`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cco_add {N : ℕ} {T : (Vec 2 → E) → (Vec 2 → E)} (hT : ConstCoefOp N T)
    {f g : Vec 2 → E} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (hg : ContDiff ℝ (N : WithTop ℕ∞) g) :
    T (fun x => f x + g x) = fun x => T f x + T g x := by
  have h := hT.sum (Finset.univ : Finset (Fin 2)) ![f, g] (by
    intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

theorem cco_smul {N : ℕ} {T : (Vec 2 → E) → (Vec 2 → E)} (hT : ConstCoefOp N T)
    (c : ℝ) {f : Vec 2 → E} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) :
    T (fun x => c • f x) = fun x => c • T f x := hT.smul c f hf

theorem cco_sub {N : ℕ} {T : (Vec 2 → E) → (Vec 2 → E)} (hT : ConstCoefOp N T)
    {f g : Vec 2 → E} (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (hg : ContDiff ℝ (N : WithTop ℕ∞) g) :
    T (fun x => f x - g x) = fun x => T f x - T g x := by
  have e : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) • g x := by
    funext x; simp [sub_eq_add_neg]
  rw [e, cco_add hT hf (hg.const_smul _), cco_smul hT _ hg]
  funext x; simp [sub_eq_add_neg]

theorem partialOp_partialOp_covOperator' (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ ((3 + 1 : ℕ) : WithTop ℕ∞) f) (i j : Fin 2) :
    partialOp i (partialOp j (AVRegularity.covOperator Hc f)) =
      AVRegularity.covOperator Hc (partialOp i (partialOp j f)) := by
  have h3 : ContDiff ℝ 3 f := hf.of_le (by norm_num)
  have h3' : ContDiff ℝ 3 (partialOp j f) := contDiff_partialOp (k := 3) hf j
  rw [partialOp_covOperator Hc j h3, partialOp_covOperator Hc i h3']

theorem covOperator_comm' (H H' : Matrix (Fin 2) (Fin 2) ℝ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ ((3 + 1 : ℕ) : WithTop ℕ∞) ψ) :
    AVRegularity.covOperator H (AVRegularity.covOperator H' ψ) =
      AVRegularity.covOperator H' (AVRegularity.covOperator H ψ) := by
  have h2 : ∀ i j, ContDiff ℝ 2 (partialOp i (partialOp j ψ)) := fun i j =>
    contDiff_partialOp (k := 2) (contDiff_partialOp (k := 3) hψ j) i
  have hs : AVRegularity.covOperator H ψ = fun y => ∑ i : Fin 2, ∑ j : Fin 2,
      H i j • partialOp i (partialOp j ψ) y := covOperator_eq H ψ
  funext x
  conv_lhs => rw [covOperator_eq H]
  simp only [partialOp_partialOp_covOperator' H' hψ]
  rw [hs, covOperator_sum H' Finset.univ
    (fun i y => ∑ j : Fin 2, H i j • partialOp i (partialOp j ψ) y)
    (fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ (h2 i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covOperator_sum H' Finset.univ (fun j y => H i j • partialOp i (partialOp j ψ) y)
    (fun j _ => ContDiff.const_smul _ (h2 i j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [covOperator_smul H' _ (h2 i j)]

theorem covIter_covOperator_comm' (H H' : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (l : ℕ) {ψ : Vec 2 → E}, ContDiff ℝ ((l * 2 + 2 : ℕ) : WithTop ℕ∞) ψ →
      (AVRegularity.covOperator H)^[l] (AVRegularity.covOperator H' ψ) =
        AVRegularity.covOperator H' ((AVRegularity.covOperator H)^[l] ψ)
  | 0, _, _ => rfl
  | l + 1, ψ, hψ => by
    have hψ' : ContDiff ℝ ((l * 2 + 2 : ℕ) : WithTop ℕ∞) ψ :=
      hψ.of_le (by exact_mod_cast (by omega : l * 2 + 2 ≤ (l + 1) * 2 + 2))
    have h4 : ContDiff ℝ ((3 + 1 : ℕ) : WithTop ℕ∞) ((AVRegularity.covOperator H)^[l] ψ) :=
      (ConstCoefOp.covIter (E := E) H l).reg 4 ψ
        (hψ.of_le (by exact_mod_cast (by omega : 4 + l * 2 ≤ (l + 1) * 2 + 2)))
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      covIter_covOperator_comm' H H' l hψ', covOperator_comm' H H' h4]

theorem covPolyP_covOperator_comm' (H H' : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ ((p * 2 + 2 : ℕ) : WithTop ℕ∞) ψ) :
    AVRegularity.covPolyP H p (AVRegularity.covOperator H' ψ) =
      AVRegularity.covOperator H' (AVRegularity.covPolyP H p ψ) := by
  have hl : ∀ l ∈ Finset.range (p + 1), ContDiff ℝ ((l * 2 + 2 : ℕ) : WithTop ℕ∞) ψ := fun l hm =>
    hψ.of_le (by
      have := Finset.mem_range.mp hm
      exact_mod_cast (by nlinarith : l * 2 + 2 ≤ p * 2 + 2))
  have h2 : ∀ l ∈ Finset.range (p + 1), ContDiff ℝ 2 ((AVRegularity.covOperator H)^[l] ψ) :=
    fun l hm => by
      have hc : ContDiff ℝ ((2 + l * 2 : ℕ) : WithTop ℕ∞) ψ :=
        (hl l hm).of_le (by exact_mod_cast (by omega : 2 + l * 2 ≤ l * 2 + 2))
      exact_mod_cast (ConstCoefOp.covIter (E := E) H l).reg 2 ψ hc
  have hs : AVRegularity.covPolyP H p ψ = fun y => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] ψ y := by
    funext y; simp [AVRegularity.covPolyP, Finset.sum_apply]
  funext x
  rw [hs, covOperator_sum H' _ _ (fun l hl' => ContDiff.const_smul _ (h2 l hl'))]
  simp only [AVRegularity.covPolyP, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun l hl' => ?_
  rw [covIter_covOperator_comm' H H' l (hl l hl'), covOperator_smul H' _ (h2 l hl')]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse Set Filter
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Pointwise-in-time product rule for the covariance iterates: if every spatial word of the
jet of `f` has the time derivative of the jet of `df` at a time `t` and the covariance matrix has
derivative `Am` at `t`, the same holds for `covOperator (Hm s) (f s)` with the displayed derivative,
with two spatial derivatives lost. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem od_sum_smul {n : ℕ} (w : DerivativeWord2 n) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (G : ι → Vec 2 → E) (hG : ∀ i ∈ s, ContDiff ℝ (n : WithTop ℕ∞) (G i)) :
    orderedDerivative w (fun x => ∑ i ∈ s, c i • G i x) =
      fun x => ∑ i ∈ s, c i • orderedDerivative w (G i) x := by
  have hc : ∀ i ∈ s, ContDiff ℝ (n : WithTop ℕ∞) (fun x => c i • G i x) :=
    fun i hi => (hG i hi).const_smul _
  have hsum : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun x => ∑ i ∈ s, c i • G i x) :=
    ContDiff.sum fun i hi => by exact_mod_cast hc i hi
  rw [AVRegularity.orderedDerivative_eq_iteratedFDeriv w hsum]
  funext x
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hc i hi).contDiffAt)]
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hGi : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (G i) := by exact_mod_cast hG i hi
  rw [iteratedFDeriv_const_smul_apply' (hG i hi).contDiffAt, _root_.smul_apply,
    AVRegularity.orderedDerivative_eq_iteratedFDeriv w hGi]

theorem od_partialOp2 {n : ℕ} (w : DerivativeWord2 n) (i j : Fin 2) (g : Vec 2 → E) :
    orderedDerivative w (partialOp i (partialOp j g)) =
      orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) w) g := by
  rw [AVRegularity.CycleWords.orderedDerivative_append]
  congr 1

theorem od_covOperator {n : ℕ} (w : DerivativeWord2 n) (M : Matrix (Fin 2) (Fin 2) ℝ)
    {g : Vec 2 → E} (hg : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) g) :
    orderedDerivative w (AVRegularity.covOperator M g) = fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      M i j • orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) w) g x := by
  have hP : ∀ p : Fin 2 × Fin 2, ContDiff ℝ (n : WithTop ℕ∞)
      (partialOp p.1 (partialOp p.2 g)) := fun p =>
    contDiff_partialOp (k := n) (contDiff_partialOp (k := n + 1) hg p.2) p.1
  have e : AVRegularity.covOperator M g = fun x => ∑ p : Fin 2 × Fin 2,
      M p.1 p.2 • partialOp p.1 (partialOp p.2 g) x := by
    rw [covOperator_eq]; funext x; rw [Fintype.sum_prod_type]
  rw [e, od_sum_smul w Finset.univ (fun p => M p.1 p.2)
    (fun p => partialOp p.1 (partialOp p.2 g)) (fun p _ => hP p)]
  funext x
  rw [Fintype.sum_prod_type]
  simp only [od_partialOp2]
end

/-! Time derivative of the covariance iterates and of the covariance polynomial at one time. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All spatial words up to length `k` of `f` have, at time `t`, the derivative given by the
same words of `df t`. -/
def HasWordTimeDerivAt (k : ℕ) (f df : ℝ → Vec 2 → E) (t : ℝ) : Prop :=
  ContDiff ℝ (k : WithTop ℕ∞) (df t) ∧ ∀ (n : ℕ) (w : DerivativeWord2 n), n ≤ k → ∀ x,
    HasDerivAt (fun s => orderedDerivative w (f s) x) (orderedDerivative w (df t) x) t

theorem HasWordTimeDerivAt.mono {k k' : ℕ} {f df : ℝ → Vec 2 → E} {t : ℝ} (h : HasWordTimeDerivAt k f df t)
    (hk : k' ≤ k) : HasWordTimeDerivAt k' f df t :=
  ⟨h.1.of_le (by exact_mod_cast hk), fun n w hn x => h.2 n w (hn.trans hk) x⟩

theorem good_step {a b t : ℝ} (ht : t ∈ Ioo a b) {k : ℕ} {f df : ℝ → Vec 2 → E}
    (hf : ∀ s ∈ Icc a b, ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (f s))
    (hg : HasWordTimeDerivAt (k + 2) f df t) (Hm Am : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => Hm s i j) (Am t i j) t) :
    HasWordTimeDerivAt k (fun s => AVRegularity.covOperator (Hm s) (f s))
      (fun s x => AVRegularity.covOperator (Am s) (f s) x +
        AVRegularity.covOperator (Hm s) (df s) x) t := by
  have hft : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (f t) := hf t (Ioo_subset_Icc_self ht)
  have hc1 : ContDiff ℝ (k : WithTop ℕ∞) (AVRegularity.covOperator (Am t) (f t)) :=
    contDiff_covOperator _ hft
  have hc2 : ContDiff ℝ (k : WithTop ℕ∞) (AVRegularity.covOperator (Hm t) (df t)) :=
    contDiff_covOperator _ hg.1
  refine ⟨hc1.add hc2, fun n w hn x => ?_⟩
  have hnb : ∀ᶠ s in nhds t, s ∈ Icc a b := Icc_mem_nhds ht.1 ht.2
  have hk2 : ∀ g : Vec 2 → E, ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) g →
      ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) g := fun g hg =>
    hg.of_le (by exact_mod_cast (by omega : n + 2 ≤ k + 2))
  have hd : ∀ i j : Fin 2, HasDerivAt
      (fun s => orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) w) (f s) x)
      (orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) w) (df t) x) t :=
    fun i j => hg.2 (2 + n) _ (by omega) x
  have hp := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 2))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin 2))) (fun j _ => (hH i j).smul (hd i j)))
  have hev : (fun s => ∑ i : Fin 2, ∑ j : Fin 2, Hm s i j •
      orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) w) (f s) x) =ᶠ[nhds t]
      fun s => orderedDerivative w (AVRegularity.covOperator (Hm s) (f s)) x := by
    filter_upwards [hnb] with s hs
    rw [od_covOperator w (Hm s) (hk2 _ (hf s hs))]
  refine (hp.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  show _ = orderedDerivative w (fun y => AVRegularity.covOperator (Am t) (f t) y +
    AVRegularity.covOperator (Hm t) (df t) y) x
  have hc1n : ContDiff ℝ (n : ℕ∞) (AVRegularity.covOperator (Am t) (f t)) :=
    hc1.of_le (by exact_mod_cast hn)
  have hc2n : ContDiff ℝ (n : ℕ∞) (AVRegularity.covOperator (Hm t) (df t)) :=
    hc2.of_le (by exact_mod_cast hn)
  rw [AVRegularity.orderedDerivative_add w hc1n hc2n,
    od_covOperator w (Am t) (hk2 _ hft), od_covOperator w (Hm t) (hk2 _ hg.1)]
  simp only [Finset.sum_add_distrib]
  rw [add_comm]

/-- Time derivative of `(covOperator H)^[l] φ` when `H` has derivative `A` and `φ` has derivative
`ψ0`. -/
def s130dIter (H A : Matrix (Fin 2) (Fin 2) ℝ) (φ ψ0 : Vec 2 → E) : ℕ → Vec 2 → E
  | 0 => ψ0
  | l + 1 => fun x => AVRegularity.covOperator A ((AVRegularity.covOperator H)^[l] φ) x +
      AVRegularity.covOperator H (s130dIter H A φ ψ0 l) x

/-- The lower covariance polynomial `∑_{l<p} (1/l!) 𝒞^l φ`. -/
def PolyLow (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E) : Vec 2 → E :=
  fun y => ∑ l ∈ Finset.range p, ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] φ y

theorem good_iter {a b t : ℝ} (ht : t ∈ Ioo a b)
    (Hm Am : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => Hm s i j) (Am t i j) t) {f df : ℝ → Vec 2 → E} :
    ∀ (l k : ℕ), (∀ s ∈ Icc a b, ContDiff ℝ ((k + l * 2 : ℕ) : WithTop ℕ∞) (f s)) →
      HasWordTimeDerivAt (k + l * 2) f df t →
      HasWordTimeDerivAt k (fun s => (AVRegularity.covOperator (Hm s))^[l] (f s))
        (fun s => s130dIter (Hm s) (Am s) (f s) (df s) l) t
  | 0, k, _, hg => by simpa [s130dIter] using hg
  | l + 1, k, hf, hg => by
    have e : k + (l + 1) * 2 = (k + 2) + l * 2 := by omega
    rw [e] at hf hg
    have ih := good_iter ht Hm Am hH l (k + 2) hf hg
    have hf' : ∀ s ∈ Icc a b, ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
        ((AVRegularity.covOperator (Hm s))^[l] (f s)) := fun s hs =>
      (ConstCoefOp.covIter (E := E) (Hm s) l).reg (k + 2) (f s) (by simpa [add_comm] using hf s hs)
    have := good_step ht hf' ih Hm Am hH
    simpa only [Function.iterate_succ_apply', s130dIter] using this

theorem hasDerivAt_iter {a b t : ℝ} (ht : t ∈ Ioo a b)
    (Hm Am : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => Hm s i j) (Am t i j) t) {f df : ℝ → Vec 2 → E} (l : ℕ)
    (hf : ∀ s ∈ Icc a b, ContDiff ℝ ((l * 2 : ℕ) : WithTop ℕ∞) (f s))
    (hg : HasWordTimeDerivAt (l * 2) f df t) (x : Vec 2) :
    HasDerivAt (fun s => (AVRegularity.covOperator (Hm s))^[l] (f s) x)
      (s130dIter (Hm t) (Am t) (f t) (df t) l x) t := by
  have h := (good_iter ht Hm Am hH l 0 (by simpa using hf) (by simpa using hg)).2 0
    Fin.elim0 le_rfl x
  simpa [orderedDerivative] using h

theorem hasDerivAt_covPolyP {a b t : ℝ} (ht : t ∈ Ioo a b)
    (Hm Am : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => Hm s i j) (Am t i j) t) {f df : ℝ → Vec 2 → E} (p : ℕ)
    (hf : ∀ s ∈ Icc a b, ContDiff ℝ ((p * 2 : ℕ) : WithTop ℕ∞) (f s))
    (hg : HasWordTimeDerivAt (p * 2) f df t) (x : Vec 2) :
    HasDerivAt (fun s => AVRegularity.covPolyP (Hm s) p (f s) x)
      (∑ l ∈ Finset.range (p + 1), ((l.factorial : ℝ)⁻¹) •
        s130dIter (Hm t) (Am t) (f t) (df t) l x) t := by
  have e : ∀ s, AVRegularity.covPolyP (Hm s) p (f s) x = ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator (Hm s))^[l] (f s) x := fun s => by
    simp [AVRegularity.covPolyP, Finset.sum_apply]
  simp only [e]
  refine HasDerivAt.fun_sum fun l hl => ?_
  have hl' : l * 2 ≤ p * 2 := by have := Finset.mem_range.mp hl; omega
  exact (hasDerivAt_iter ht Hm Am hH l
    (fun s hs => (hf s hs).of_le (by exact_mod_cast hl')) (hg.mono hl') x).const_smul _

theorem dIter_eq (H A : Matrix (Fin 2) (Fin 2) ℝ) (φ ψ0 : Vec 2 → E) :
    ∀ l : ℕ, ContDiff ℝ ((l * 2 + 2 : ℕ) : WithTop ℕ∞) φ →
      ContDiff ℝ ((l * 2 : ℕ) : WithTop ℕ∞) ψ0 →
      s130dIter H A φ ψ0 l = fun x => (AVRegularity.covOperator H)^[l] ψ0 x +
        (l : ℝ) • AVRegularity.covOperator A ((AVRegularity.covOperator H)^[l - 1] φ) x
  | 0, _, _ => by funext x; simp [s130dIter]
  | l + 1, hφ, hψ => by
    have hφ' : ContDiff ℝ ((l * 2 + 2 : ℕ) : WithTop ℕ∞) φ :=
      hφ.of_le (by exact_mod_cast (by omega : l * 2 + 2 ≤ (l + 1) * 2 + 2))
    have hψ' : ContDiff ℝ ((l * 2 : ℕ) : WithTop ℕ∞) ψ0 :=
      hψ.of_le (by exact_mod_cast (by omega : l * 2 ≤ (l + 1) * 2))
    have ih := dIter_eq H A φ ψ0 l hφ' hψ'
    have hg1 : ContDiff ℝ 2 ((AVRegularity.covOperator H)^[l] ψ0) := by
      have := (ConstCoefOp.covIter (E := E) H l).reg 2 ψ0 (by
        refine hψ.of_le ?_
        exact_mod_cast (by omega : 2 + l * 2 ≤ (l + 1) * 2))
      exact_mod_cast this
    show (fun x => AVRegularity.covOperator A ((AVRegularity.covOperator H)^[l] φ) x +
      AVRegularity.covOperator H (s130dIter H A φ ψ0 l) x) = _
    rw [ih]
    rcases Nat.eq_zero_or_pos l with rfl | hpos
    · funext x
      simp [add_comm]
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      have h4 : ContDiff ℝ ((3 + 1 : ℕ) : WithTop ℕ∞) ((AVRegularity.covOperator H)^[m] φ) := by
        have := (ConstCoefOp.covIter (E := E) H m).reg 4 φ (by
          refine hφ'.of_le ?_
          exact_mod_cast (by omega : 4 + m * 2 ≤ (m + 1) * 2 + 2))
        exact_mod_cast this
      have hg2 : ContDiff ℝ 2 (AVRegularity.covOperator A ((AVRegularity.covOperator H)^[m] φ)) := by
        have := (ConstCoefOp.covOperator (E := E) A).reg 2 _ (by exact_mod_cast h4)
        exact_mod_cast this
      have hcc := ConstCoefOp.covOperator (E := E) H
      have hadd := cco_add hcc (f := (AVRegularity.covOperator H)^[m + 1] ψ0)
        (g := fun x => ((m + 1 : ℕ) : ℝ) •
          AVRegularity.covOperator A ((AVRegularity.covOperator H)^[m + 1 - 1] φ) x)
        (by exact_mod_cast hg1) (by simpa using hg2.const_smul ((m + 1 : ℕ) : ℝ))
      rw [hadd]
      funext x
      have h1 := congrFun (covOperator_smul H ((m + 1 : ℕ) : ℝ) hg2) x
      have h2 := congrFun (covOperator_comm' H A h4) x
      simp only [show m + 1 - 1 = m from rfl, show m + 1 + 1 - 1 = m + 1 from rfl]
      rw [h1, h2, ← Function.iterate_succ_apply' (AVRegularity.covOperator H) m φ,
        Function.iterate_succ_apply' (AVRegularity.covOperator H) (m + 1) ψ0]
      push_cast
      module

theorem dPoly_eq (H A : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {φ ψ0 : Vec 2 → E}
    (hφ : ContDiff ℝ ((p * 2 + 2 : ℕ) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((p * 2 : ℕ) : WithTop ℕ∞) ψ0) (x : Vec 2) :
    ∑ l ∈ Finset.range (p + 1), ((l.factorial : ℝ)⁻¹) • s130dIter H A φ ψ0 l x =
      AVRegularity.covPolyP H p ψ0 x + AVRegularity.covOperator A (PolyLow H p φ) x := by
  have hl : ∀ l ∈ Finset.range (p + 1), s130dIter H A φ ψ0 l = fun x =>
      (AVRegularity.covOperator H)^[l] ψ0 x +
        (l : ℝ) • AVRegularity.covOperator A ((AVRegularity.covOperator H)^[l - 1] φ) x :=
    fun l hl => by
      have hlp : l * 2 + 2 ≤ p * 2 + 2 := by have := Finset.mem_range.mp hl; omega
      exact dIter_eq H A φ ψ0 l (hφ.of_le (by exact_mod_cast hlp))
        (hψ.of_le (by exact_mod_cast (by omega : l * 2 ≤ p * 2)))
  have h2' : ∀ m ∈ Finset.range p, ContDiff ℝ 2 ((AVRegularity.covOperator H)^[m] φ) :=
    fun m hm => by
      have hmp : 2 + m * 2 ≤ p * 2 + 2 := by have := Finset.mem_range.mp hm; omega
      have := (ConstCoefOp.covIter (E := E) H m).reg 2 φ
        (by simpa [add_comm] using hφ.of_le (by exact_mod_cast hmp))
      exact_mod_cast this
  have h2 : ∀ m ∈ Finset.range p, ContDiff ℝ 2
      (fun y => ((m.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[m] φ y) :=
    fun m hm => (h2' m hm).const_smul _
  have hrhs : AVRegularity.covOperator A (PolyLow H p φ) x = ∑ m ∈ Finset.range p,
      ((m.factorial : ℝ)⁻¹) • AVRegularity.covOperator A ((AVRegularity.covOperator H)^[m] φ) x := by
    unfold PolyLow
    rw [covOperator_sum A _ _ h2]
    refine Finset.sum_congr rfl fun m hm => ?_
    exact congrFun (covOperator_smul A _ (h2' m hm)) x
  rw [hrhs, Finset.sum_congr rfl (fun l hm => by rw [hl l hm])]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  · simp [AVRegularity.covPolyP, Finset.sum_apply]
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_smul, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    rw [smul_smul]
    congr 1
    field_simp
end

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Residual operators for one menu: the covariance anchor and slow length are explicit.
Anchor zero and length factor one recover the cascade operators; anchor `tp` and factor
`cr` recover the terminal covariance and complete lift. Kernels stay inside coefficients. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The covariance primitive of a menu, retaining its actual anchor. -/
def menuCovPrimitive (D : OCData) (Mn : SuccMenu) (m : ℕ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) Mn.anchor t

def menuLiftedRep (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root :=
  fun t x => gluedLift (ocObsPulses D.α D.q D.Λ m t t) (fun k => ocCutoff D.α D.q D.Λ m k)
    (D.cellScaleSq m) (Mn.lenFactor * liftLength D m) (D.eps m)
    (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / (Mn.lenFactor * liftLength D m)) N depth CcT
    (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
    (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') g t x

def menuCovPRep (Mn : SuccMenu) (D : OCData) (m p : ℕ) {S : Finset Comp} (g : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root :=
  fun t y v => covPolyP (menuCovPrimitive D Mn m t) p (fun y' => g t y' v) y

def menuGluedMeanFlux (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m : ℕ) (rs ns : Finset ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) : Fin 2 → hr v.1.root :=
  ∑ k ∈ ocObsPulses D.α D.q D.Λ m t t, ∑ r ∈ rs, ∑ n ∈ ns,
    if hk : Odd k then
      ocCutoff D.α D.q D.Λ m k t • pulseMeanFluxEuler (D.cellScaleSq m) (Mn.lenFactor * liftLength D m)
        (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / (Mn.lenFactor * liftLength D m)) n r
        (familyLiftData D m k (nativeChain m k) (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
        (fun s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
        (fun s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') a t x v
    else 0

def menuMeanFluxE (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) : Fin 2 → hr v.1.root :=
  menuGluedMeanFlux Mn G m (Finset.Icc 1 depth) (Finset.Icc 2 (N + Dm)) CcT a t x v

def menuDiagFluxPhys (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) : Fin 2 → hr v.1.root :=
  menuGluedMeanFlux Mn G m {0} (Finset.Icc 2 (N + 1)) CcT a t x v -
    fun j => ∑ l : Fin 2, ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t j l •
      gradE (fun y => a t y v) x l

def menuTemporalFlux (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (v : CompIn G.comps) :
    Vec 2 → Fin 2 → hr v.1.root :=
  fun x => (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
      (covOperator (menuCovPrimitive D Mn m t))^[a'] (commFluxE (streamVel (D.Φ (m - 1)) t)
        (menuCovPrimitive D Mn m t) ((covOperator (menuCovPrimitive D Mn m t))^[l - 1 - a'] (fun y => a t y v))) x) -
    menuDiagFluxPhys Mn G m N CcT (fun s y w => covPolyP (menuCovPrimitive D Mn m s) p (fun y' => a s y' w) y) t x v

open scoped Classical in

def menuGFlux (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  menuTemporalFlux Mn G m N p CcT aZ t v x - menuMeanFluxE Mn G m N depth CcT (menuCovPRep Mn D m p aZ) t x v

def menuMeanFluxF (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Υ : ∀ v : CompIn G.comps, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root))
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) : Fin 2 → hr v.1.root :=
  (menuGFlux Mn G m N p depth CcT aZ v t x -
      covPolyP (menuCovPrimitive D Mn m t) p
        (covPolyQ (menuCovPrimitive D Mn m t) p (fun y => menuGFlux Mn G m N p depth CcT aZ v t y)) x) -
    covPolyP (menuCovPrimitive D Mn m t) p (fun y => WithLp.ofLp (Υ v t y)) x -
    fun j => ∑ l : Fin 2, (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) j l •
      gradE (fun y => ((p.factorial : ℝ)⁻¹) •
        (covOperator (menuCovPrimitive D Mn m t))^[p] (fun y' => aZ t y' v) y) x l

def menuMacroFlux (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  (fun j => ∑ l : Fin 2, (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) j l •
      gradE (fun y => g t y v) x l) +
    menuDiagFluxPhys Mn G m N CcT g t x v + menuMeanFluxE Mn G m N depth CcT g t x v

def menuMacroRes (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g dg : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2) :
    ∀ v : CompIn G.comps, hr v.1.root :=
  fun v => dg t x v +
    ∑ j : Fin 2, streamVel (D.Φ (m - 1)) t x j • gradE (fun y => g t y v) x j -
    divE (fun y => D.κ (m - 1) • gradE (fun y' => g t y' v) y +
      menuMacroFlux Mn G m N depth CcT g v t y) x

def menuPhysRes (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep dRep dUh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : hr v.1.root :=
  let uh := menuLiftedRep Mn G m N depth CcT aRep
  (dUh t x v +
      ∑ j : Fin 2, streamVel (D.Φ m) t x j • gradE (fun y => uh t y v) x j -
      divE (fun y => D.κ m • gradE (fun y' => uh t y' v) y +
        fun j => WithLp.ofLp (coeffFluxOn P seedK freshK φ₀ G .plain
          uh v t y) j) x) -
    menuLiftedRep Mn G m N depth CcT (menuMacroRes Mn G m N depth CcT aRep dRep) t x v

/-- The native pulse lift and covariance image for any menu and any output order. -/
def IsMenuLiftedField (Mn : SuccMenu) (G Gr : GenStage D hr Dm b j₀) (m p Naux N depth sX sZ : ℕ) (η₀ tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) {K : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk K (hr v.1.root)) : Prop :=
  (∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D m k (nativeChain m k) (Mn.lenFactor * liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N depth (CcT k)) ∧
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    IsCovImage (covPolyP (menuCovPrimitive D Mn m t) p)
      (succReadout m (D.eps (m - 1)) η₀ Naux (fun v' => Y v' t) v) (PZ v t) ∧
    IsClassicalRep (PZ v t) (fun x => aRep t x v) (Naux - 2 * p)) ∧
  ∀ v, ∀ t ∈ Set.Icc tp tf,
    (û v t).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => gluedLift (ocObsPulses D.α D.q D.Λ m t t) (fun k => ocCutoff D.α D.q D.Λ m k)
        (D.cellScaleSq m) (Mn.lenFactor * liftLength D m) (D.eps m)
        (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / (Mn.lenFactor * liftLength D m)) N depth CcT
        (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
        (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') aRep t x v

section
omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

/-- Cascade and terminal specializations of the same covariance and complete lift. -/
theorem menuCovPrimitive_cascade (Mn : SuccMenu) (hanchor : Mn.anchor = 0) (m : ℕ) (t : ℝ) :
    menuCovPrimitive D Mn m t = covPrimitive D m t := by
  simp only [menuCovPrimitive, covPrimitive, hanchor]

theorem menuLiftedRep_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuLiftedRep Mn G m N depth CcT g = liftedRep G m N depth CcT g := by
  unfold menuLiftedRep liftedRep
  simp only [hlength, one_mul]

theorem menuCovPRep_cascade (Mn : SuccMenu)
    (hanchor : Mn.anchor = 0) (D : OCData) (m p : ℕ) {S : Finset Comp} (g : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root) :
    menuCovPRep Mn D m p g = covPRep D m p g := by
  unfold menuCovPRep covPRep
  simp only [menuCovPrimitive_cascade _ hanchor]

theorem menuGluedMeanFlux_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m : ℕ) (rs ns : Finset ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuGluedMeanFlux Mn G m rs ns CcT a = gluedMeanFlux G m rs ns CcT a := by
  unfold menuGluedMeanFlux gluedMeanFlux
  simp only [hlength, one_mul]

theorem menuMeanFluxE_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuMeanFluxE Mn G m N depth CcT a = meanFluxE G m N depth CcT a := by
  unfold menuMeanFluxE meanFluxE
  simp only [menuGluedMeanFlux_cascade _ hlength]

theorem menuDiagFluxPhys_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuDiagFluxPhys Mn G m N CcT a = diagFluxPhys G m N CcT a := by
  unfold menuDiagFluxPhys diagFluxPhys
  simp only [menuGluedMeanFlux_cascade _ hlength]

theorem menuTemporalFlux_cascade (Mn : SuccMenu)
    (hanchor : Mn.anchor = 0) (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N p : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuTemporalFlux Mn G m N p CcT a = temporalFlux G m N p CcT a := by
  unfold menuTemporalFlux temporalFlux
  simp only [menuCovPrimitive_cascade _ hanchor, menuDiagFluxPhys_cascade _ hlength]

theorem menuGFlux_cascade (Mn : SuccMenu)
    (hanchor : Mn.anchor = 0) (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuGFlux Mn G m N p depth CcT aZ = gFlux G m N p depth CcT aZ := by
  unfold menuGFlux gFlux
  simp only [menuTemporalFlux_cascade _ hanchor hlength, menuMeanFluxE_cascade _ hlength, menuCovPRep_cascade _ hanchor]

theorem menuMeanFluxF_cascade (Mn : SuccMenu)
    (hanchor : Mn.anchor = 0) (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Υ : ∀ v : CompIn G.comps, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :
    menuMeanFluxF Mn G m N p depth CcT aZ Υ = meanFluxF G m N p depth CcT aZ Υ := by
  unfold menuMeanFluxF meanFluxF
  simp only [menuGFlux_cascade _ hanchor hlength, menuCovPrimitive_cascade _ hanchor]

theorem menuMacroFlux_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuMacroFlux Mn G m N depth CcT g = macroFlux G m N depth CcT g := by
  unfold menuMacroFlux macroFlux
  simp only [menuDiagFluxPhys_cascade _ hlength, menuMeanFluxE_cascade _ hlength]

theorem menuMacroRes_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g dg : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuMacroRes Mn G m N depth CcT g dg = macroRes G m N depth CcT g dg := by
  unfold menuMacroRes macroRes
  simp only [menuMacroFlux_cascade _ hlength]

theorem menuPhysRes_cascade (Mn : SuccMenu)
    (hlength : Mn.lenFactor = 1) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep dRep dUh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    menuPhysRes Mn P seedK freshK φ₀ G m N depth CcT aRep dRep dUh = physRes P seedK freshK φ₀ G m N depth CcT aRep dRep dUh := by
  unfold menuPhysRes physRes
  simp only [menuLiftedRep_cascade _ hlength, menuMacroRes_cascade _ hlength]

end

theorem isMenuLiftedField_cascade (Mn : SuccMenu)
    (hanchor : Mn.anchor = 0) (hlength : Mn.lenFactor = 1) (G Gr : GenStage D hr Dm b j₀) (m p Naux N depth sX sZ : ℕ) (η₀ tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) {K : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk K (hr v.1.root)) :
    IsMenuLiftedField Mn G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û ↔ IsLiftedField G Gr m p Naux N depth sX sZ η₀ tp tf Y CcT PZ aRep û := by
  simp only [IsMenuLiftedField, IsLiftedField, menuCovPrimitive, covPrimitive, hanchor, hlength, one_mul]

theorem menuLiftedRep_terminal {Gw : GenStage D ScalarH Dm b j₀} (Mn : SuccMenu)
    (cr : ℝ) (hlength : Mn.lenFactor = cr) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root) :
    menuLiftedRep Mn Gw m N depth CcT a = termLiftedRep Gw m N depth cr CcT a := by
  rcases Mn with ⟨M, A, H, J, N, p, sX, sZ, η, anchor, factor⟩
  change factor = cr at hlength
  subst factor
  rfl
end

/-! The glued mean and diagonal fluxes at a time `t` depend on the field only through its time
slice, provided the cell scale is nonzero. -/

section
section Generic
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem liftApply_local (n : ℕ) (c : LiftCoeff ι h) (a b : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hab : a τ = b τ) : liftApply n c a τ = liftApply n c b τ := by
  funext X z v
  simp only [liftApply, hab]

theorem liftFluxX_local (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (τ : ℝ) (hab : a τ = b τ) :
    liftFluxX Q Cc a hh n τ = liftFluxX Q Cc b hh n τ := by
  have hl : ∀ (k : ℕ) (cc : LiftCoeff ι h), liftApply k cc a τ = liftApply k cc b τ :=
    fun k cc => liftApply_local k cc a b τ hab
  funext X z k
  simp only [liftFluxX, hl]

theorem pulseMeanFluxEuler_local (c ρ εc : ℝ) (n r : ℕ) (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2)
    (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) (v : ι) (hc : c ≠ 0) (hab : a t = b t) :
    pulseMeanFluxEuler c ρ εc n r Q Cc chart label a t x v =
      pulseMeanFluxEuler c ρ εc n r Q Cc chart label b t x v := by
  have h1 : (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) (c⁻¹ * t) =
      (fun s' X' => b (c * s') (chart (c * s') (ρ • X'))) (c⁻¹ * t) := by
    funext X'
    simp only [mul_inv_cancel_left₀ hc, hab]
  unfold pulseMeanFluxEuler
  rw [liftFluxX_local Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X')))
    (fun s' X' => b (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t) h1]

end Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem menuGluedMeanFlux_local (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m : ℕ)
    (rs ns : Finset ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a a' : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) (hc : D.cellScaleSq m ≠ 0) (hab : a t = a' t) :
    menuGluedMeanFlux Mn G m rs ns CcT a t x v = menuGluedMeanFlux Mn G m rs ns CcT a' t x v := by
  unfold menuGluedMeanFlux
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun n _ => ?_
  split_ifs with hk
  · rw [pulseMeanFluxEuler_local _ _ _ _ _ _ _ _ _ a a' t x v hc hab]
  · rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem menuMeanFluxE_local (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a a' : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) (hc : D.cellScaleSq m ≠ 0) (hab : a t = a' t) :
    menuMeanFluxE Mn G m N depth CcT a t x v = menuMeanFluxE Mn G m N depth CcT a' t x v :=
  menuGluedMeanFlux_local Mn G m _ _ CcT a a' t x v hc hab

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem menuDiagFluxPhys_local (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a a' : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) (hc : D.cellScaleSq m ≠ 0) (hab : a t = a' t) :
    menuDiagFluxPhys Mn G m N CcT a t x v = menuDiagFluxPhys Mn G m N CcT a' t x v := by
  unfold menuDiagFluxPhys
  rw [menuGluedMeanFlux_local Mn G m _ _ CcT a a' t x v hc hab, hab]
end

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
