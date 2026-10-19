-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.TransitionTaylorBounds
public import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.MeanEnhancementScale
import AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable

section
section
@[expose] public section
namespace AVRegularity.CycleReference

/-! The uniform reciprocal bootstrap for every finite permitted-band chain. -/

theorem bandChain_normalized_uniform_bound {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ R : ℝ, 0 < R ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 2 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 1 ≤ m → m < M →
          reciprocalSize (normalizedDiffusivity α q Λ m (κ m)) ≤ R := by
  obtain ⟨B, hB, Lstart, hLstart, hstart⟩ := terminal_normalized_start hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cr, Ce, hCr, hCe, Lstep, hLstep, hstep⟩ := normalized_step_of_small_errors hα0 hα1 hs0 hs1 hq hζ
  let R := 2 * B
  have hR : 0 < R := by dsimp [R]; positivity
  let D := Ce * (R + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hparams := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  obtain ⟨Lbudget, hLbudget, hbudget⟩ := exists_recurrence_error_budget hq.1 hparams.1 hparams.2.1 hCr hD
  refine ⟨R, hR, max Lstart (max Lstep Lbudget), hLstart.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ
  have hΛstart : Lstart ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛstep : Lstep ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛbudget : Lbudget ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 : 128 ≤ Λ := hLstart.trans hΛstart
  have hΛ1 : 1 ≤ Λ := by omega
  let y := fun j => reciprocalSize (normalizedDiffusivity α q Λ (j + 1) (κ (j + 1)))
  let e := fun j => 16 * (Cr * ocEpsilon q Λ (j + 1) +
    ocEpsilon q Λ (j + 2) ^ (2 * ocGamma α q) + D * ocEpsilon q Λ (j + 1) ^ ocDelta α q)
  have hyStart : y (M - 2) ≤ B := by
    have hm : M - 2 + 1 = M - 1 := by omega
    dsimp [y]
    rw [hm, hκ.2 M (by omega) (le_refl M)]
    exact hstart Λ M hΛstart hM (κ M) hκ.1
  have he : ∀ j, 0 ≤ e j := by
    intro j
    have he1 := (AVRegularity.Scales.epsilon_basic (m := j + 1) hq.1 h128).1
    have he2 := (AVRegularity.Scales.epsilon_basic (m := j + 2) hq.1 h128).1
    dsimp [e]
    positivity
  have heBudget : ∑ j ∈ Finset.range (M - 2), e j ≤ 1 / 2 := (hbudget Λ hΛbudget).1 _
  have hyStep : ∀ j, 1 ≤ j → j ≤ M - 2 → y j ≤ R →
      y (j - 1) ≤ y j * (1 + e (j - 1)) := by
    intro j hj hjM hsize
    have hν := bandChain_pos hΛ1 hζ hκ (show j + 1 ≤ M by omega)
    have hsmall := (hbudget Λ hΛbudget).2 (j + 1) (by omega)
    have hs := hstep Λ (j + 1) hΛstep (by omega) (κ (j + 1)) R hν hsize
      (by simpa only [Nat.add_sub_cancel] using hsmall.1)
      (by simpa only [Nat.add_sub_cancel, D] using hsmall.2)
    have hκstep : κ j = ocMeanFlux α q Λ ζ (j + 1) (κ (j + 1)) := by
      simpa only [Nat.add_sub_cancel] using hκ.2 (j + 1) (by omega) (by omega)
    have hj1 : j - 1 + 1 = j := by omega
    have hj2 : j - 1 + 2 = j + 1 := by omega
    change reciprocalSize (normalizedDiffusivity α q Λ (j - 1 + 1) (κ (j - 1 + 1))) ≤ _
    rw [hj1, hκstep]
    simpa only [y, e, hj1, hj2, Nat.add_sub_cancel, D] using hs
  have hfinal := backward_small_error_bootstrap hR.le (show B ≤ R / 2 by dsimp [R]; linarith)
    hyStart he heBudget hyStep
  intro m hm hmM
  have h := hfinal (m - 1) (by omega)
  simpa only [y, Nat.sub_add_cancel hm] using h

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! H¹ membership and the metric energy identity in a renewal chart. -/

theorem streamFlow_gradient_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) {Du : Vec 2 → Vec 2}
    (hDu : GradMemL2On Set.univ Du) :
    GradMemL2On Set.univ
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (Du (AVRegularity.streamFlow φ hφ t y s))) := by
  obtain ⟨C, hC, hb⟩ := streamFlow_jacMatrix_bounded hφ t s
  let F := fun y => AVRegularity.streamFlow φ hφ t y s
  have hmp := streamFlow_measurePreserving hφ t s
  have hJ (i j : Fin 2) : Continuous (fun y => jacMatrix F y i j) :=
    (jacMatrix_entry_smooth (streamFlow_spatial_smooth hφ t s) i j).continuous
  have htop (i j : Fin 2) : MemLp (fun y => jacMatrix F y i j) ⊤ volume :=
    memLp_top_of_bound (hJ i j).aestronglyMeasurable C (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using hb y i j))
  have hcomp (i : Fin 2) : MemLp (fun y => Du (F y) i) 2 volume := by
    have hi : MemLp (fun y => Du y i) 2 volume := by
      simpa only [MemL2On, Measure.restrict_univ] using hDu i
    exact hi.comp_measurePreserving hmp
  intro j
  simp only [MemL2On, Measure.restrict_univ]
  have hmul (i : Fin 2) : MemLp (fun y => jacMatrix F y i j * Du (F y) i) 2 volume :=
    (htop i j).mul (hcomp i)
  have he : (fun y => ((jacMatrix F y)ᵀ.mulVec (Du (F y))) j) =
      (fun y => ∑ i : Fin 2, jacMatrix F y i j * Du (F y) i) := by
    funext y
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [he]
  exact memLp_finsetSum _ (fun i _ => hmul i)

theorem chart_h1_energy (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ) {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : MemL2On Set.univ u) (hDu : GradMemL2On Set.univ Du)
    (hw : HasWeakGradientOn Set.univ u Du) :
    ∃ Du' : Vec 2 → Vec 2, GradMemL2On Set.univ Du' ∧
      HasWeakGradientOn Set.univ (fun y => u (ocChart α q Λ m φ hφ l t y)) Du' ∧
      ∫ y, vecDot (Du' y) ((ocMaterialMetric α q Λ m φ hφ l t y).mulVec (Du' y)) =
        ∫ x, vecDot (Du x) (Du x) := by
  refine ⟨fun y => (jacMatrix (ocChart α q Λ m φ hφ l t) y)ᵀ.mulVec
    (Du (ocChart α q Λ m φ hφ l t y)), ?_, ?_, ?_⟩
  · exact streamFlow_gradient_memL2 hφ t _ hDu
  · exact streamFlow_weakGradient hφ t _ hu hDu hw
  · exact chart_gradient_energy α q Λ m hφ l t Du

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Uniform interior diffusivity comparisons along every permitted-band chain. -/

theorem normalized_bound_implies_diffusivity_asymp {α q : ℝ} {Λ m : ℕ} {ν R : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hR : 0 < R)
    (hsize : reciprocalSize (normalizedDiffusivity α q Λ m ν) ≤ R) :
    ocAsymp (1 + R * cycleAmplitude + R / cycleAmplitude) ν
      (ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q)) := by
  let C := 1 + R * cycleAmplitude + R / cycleAmplitude
  let z := normalizedDiffusivity α q Λ m ν
  let P := ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q)
  have ha := cycleAmplitude_pos
  have hP : 0 < P := Real.rpow_pos_of_pos (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) _
  have hz : 0 < z := normalizedDiffusivity_pos hΛ hν
  have hRA : 0 < R / cycleAmplitude := div_pos hR ha
  have hRA' : 0 < R * cycleAmplitude := mul_pos hR ha
  have hC : 0 < C := by dsimp [C]; linarith
  have hzu : z ≤ R := (le_max_left _ _).trans hsize
  have hzi : z⁻¹ ≤ R := (le_max_right _ _).trans hsize
  have hzl : R⁻¹ ≤ z := by
    have h := (inv_le_inv₀ hR (inv_pos.mpr hz)).2 hzi
    simpa only [inv_inv] using h
  have hidentity : ν = z * cycleAmplitude * P := by
    change ν = (ν / (cycleAmplitude * P)) * cycleAmplitude * P
    field_simp
  have hCu : R * cycleAmplitude ≤ C := by dsimp [C]; linarith
  have hCl : R / cycleAmplitude ≤ C := by dsimp [C]; linarith
  have hCi : C⁻¹ ≤ R⁻¹ * cycleAmplitude := by
    have h := (inv_le_inv₀ hC (div_pos hR ha)).2 hCl
    simpa only [div_eq_mul_inv, mul_inv, inv_inv, mul_comm] using h
  change C⁻¹ * P ≤ ν ∧ ν ≤ C * P
  rw [hidentity]
  constructor
  · exact (mul_le_mul_of_nonneg_right hCi hP.le).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzl ha.le) hP.le)
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzu ha.le) hP.le).trans
      (mul_le_mul_of_nonneg_right hCu hP.le)

theorem bandChain_interior_diffusivities {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 1 ≤ m → m < M →
          ocAsymp C (κ m) (ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q)) := by
  obtain ⟨R, hR, Λ₀, hΛ₀, hb⟩ := bandChain_normalized_uniform_bound hα0 hα1 hs0 hs1 hq hζ
  have ha := cycleAmplitude_pos
  have hRA : 0 < R / cycleAmplitude := div_pos hR ha
  have hRA' : 0 < R * cycleAmplitude := mul_pos hR ha
  refine ⟨1 + R * cycleAmplitude + R / cycleAmplitude, by linarith, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M _ κ hκ m hm hmM
  have hΛ1 : 1 ≤ Λ := by omega
  exact normalized_bound_implies_diffusivity_asymp hΛ1 (bandChain_pos hΛ1 hζ hκ (by omega)) hR
    (hb Λ hΛ M (by omega) κ hκ m hm hmM)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory Filter Topology Homogenization
open scoped ENNReal
namespace AVRegularity.CycleReference

/-! Continuous L² traces survive a continuous family of volume-preserving charts. -/

theorem continuous_L2_trace_comp {Z : Type*} [TopologicalSpace Z]
    (θ : Z → Vec 2 → ℝ) (hθ : ∀ z, MemLp (θ z) 2 volume)
    (ht : ∀ z, Tendsto (fun w => eLpNorm (fun x => θ w x - θ z x) 2 volume) (𝓝 z) (𝓝 0))
    (X : Z → C(Vec 2, Vec 2)) (hX : Continuous X)
    (hmp : ∀ z, MeasurePreserving (X z) volume volume) :
    ∀ z, Tendsto (fun w => eLpNorm (fun x => θ w (X w x) - θ z (X z x)) 2 volume)
      (𝓝 z) (𝓝 0) := by
  let F : Z → Lp ℝ 2 volume := fun z => (hθ z).toLp (θ z)
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.2
    intro z
    rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
    simpa only [F, Lp.edist_toLp_toLp, Pi.sub_def, Function.comp_def] using ht z
  have hc := hF.compMeasurePreservingLp hX hmp (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro z
  have ht' := hc.continuousAt (x := z)
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0] at ht'
  simpa only [F, Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp, Pi.sub_def, Function.comp_def] using ht'


noncomputable def streamFlowContinuousMap {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (s t : ℝ) : C(Vec 2, Vec 2) :=
  ⟨fun y => AVRegularity.streamFlow φ hφ t y s, (streamFlow_spatial_smooth hφ t s).continuous⟩

theorem streamFlowContinuousMap_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (s : ℝ) :
    Continuous (streamFlowContinuousMap hφ s) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (streamFlow_joint_smooth hφ).continuous.comp
    (continuous_fst.prodMk (continuous_snd.prodMk (continuous_const (y := s))))

theorem streamFlow_L2_trace_on {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (s : ℝ) (S : Set ℝ)
    (θ : ℝ → Vec 2 → ℝ) (hθ : ∀ t ∈ S, MemL2On Set.univ (θ t))
    (ht : ∀ t ∈ S, Tendsto (fun r => eLpNorm (fun x => θ r x - θ t x) 2 volume)
      (𝓝[S] t) (𝓝 0)) :
    ∀ t ∈ S, Tendsto (fun r => eLpNorm
      (fun x => θ r (AVRegularity.streamFlow φ hφ r x s) -
        θ t (AVRegularity.streamFlow φ hφ t x s)) 2 volume) (𝓝[S] t) (𝓝 0) := by
  have hm (t : S) : MemLp (θ t) 2 volume := by
    simpa only [MemL2On, Measure.restrict_univ] using hθ t t.property
  have hc (t : S) : Tendsto (fun r : S => eLpNorm (fun x => θ r x - θ t x) 2 volume)
      (𝓝 t) (𝓝 0) :=
    (tendsto_nhdsWithin_iff_subtype t.property _ _).1 (ht t t.property)
  have hcomp := continuous_L2_trace_comp (fun t : S => θ t) hm hc
    (fun t : S => streamFlowContinuousMap hφ s t)
    ((streamFlowContinuousMap_continuous hφ s).comp continuous_subtype_val)
    (fun t => streamFlow_measurePreserving hφ t s)
  intro t htin
  exact (tendsto_nhdsWithin_iff_subtype htin _ _).2 (hcomp ⟨t, htin⟩)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! One-sided diffusivity bounds valid also at the terminal band. -/

theorem bandChain_all_level_bounds {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 1 ≤ m → m ≤ M →
          C⁻¹ * ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) ≤ κ m ∧
          κ m ≤ C * ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  have hCp : 0 < C := by linarith
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  refine ⟨C + 2, by linarith, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have h128 := hΛ₀.trans hΛ
  have he := AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128
  have hpow : ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) ≤
      ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) :=
    Real.rpow_le_rpow_of_exponent_ge he.1 he.2.1 (by linarith)
  by_cases hlt : m < M
  · have hi := asymp_mono_constant hCp (show C ≤ C + 2 by linarith)
      (Real.rpow_pos_of_pos he.1 _).le (hb Λ hΛ M hM κ hκ m hm hlt)
    exact ⟨hi.1, hi.2.trans (mul_le_mul_of_nonneg_left hpow (by linarith))⟩
  · have hmM' : m = M := by omega
    have hband : κ m ∈ ocBand α q Λ m := by simpa only [hmM'] using hκ.1
    have hDi : (C + 2)⁻¹ ≤ 1 / 2 := by
      have h := (inv_le_inv₀ (show 0 < C + 2 by linarith) (by norm_num : (0 : ℝ) < 2)).2
        (show 2 ≤ C + 2 by linarith)
      norm_num at h
      exact h
    have hlow := (mul_le_mul_of_nonneg_right hDi (Real.rpow_pos_of_pos he.1 _).le).trans
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 2))
    refine ⟨hlow.trans ?_, hband.2.trans ?_⟩
    · convert hband.1 using 1; ring
    · exact mul_le_mul_of_nonneg_right (show 2 ≤ C + 2 by linarith) (Real.rpow_pos_of_pos he.1 _).le

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Space-time L² control of the gradient in a fixed-start flow chart. -/

theorem streamFlowTime_restrict_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) :
    MeasurePreserving (streamFlowTimeHomeomorph hφ s)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ))
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
  have hm := (streamFlowTime_measurePreserving hφ s).restrict_preimage
    (s := Set.Ioo a b ×ˢ (Set.univ : Set (Vec 2)))
    (measurableSet_Ioo.prod MeasurableSet.univ)
  have he : (streamFlowTimeHomeomorph hφ s) ⁻¹' (Set.Ioo a b ×ˢ Set.univ) =
      Set.Ioo a b ×ˢ Set.univ := by
    ext p
    rfl
  rw [he] at hm
  exact hm

theorem streamFlow_joint_gradient_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) {Du : ℝ → Vec 2 → Vec 2}
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) :
    ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ p.1 x s) p.2)ᵀ.mulVec
        (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
  let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a b ×ˢ Set.univ)
  let J := fun p : ℝ × Vec 2 => jacMatrix (fun x => AVRegularity.streamFlow φ hφ p.1 x s) p.2
  obtain ⟨C, hC, hb⟩ := streamFlow_jacMatrix_bounded_on_compact_time hφ s
    (Set.Icc a b) isCompact_Icc
  have htop (i j : Fin 2) : MemLp (fun p => J p i j) ⊤ μ := by
    have hc := (continuous_apply j).comp ((continuous_apply i).comp
      (streamFlow_jacMatrix_joint_continuous hφ s))
    refine memLp_top_of_bound hc.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
    rw [Real.norm_eq_abs]
    exact hb p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 i j
  have hcomp (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) i) 2 μ :=
    (hDu i).comp_measurePreserving (streamFlowTime_restrict_measurePreserving hφ s a b)
  intro j
  have hmul (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => J p i j * Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) i) 2 μ :=
    (htop i j).mul (hcomp i)
  have he : (fun p : ℝ × Vec 2 => ((J p)ᵀ.mulVec
      (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) =
      (fun p => ∑ i : Fin 2, J p i j * Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) i) := by
    funext p
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  change MemLp (fun p => ((J p)ᵀ.mulVec
    (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) 2 μ
  rw [he]
  exact memLp_finsetSum _ (fun i _ => hmul i)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleReference

/-! Continuous L² traces under the inverse fixed-start chart. -/

noncomputable def inverseStreamFlowContinuousMap {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (s t : ℝ) : C(Vec 2, Vec 2) :=
  ⟨fun y => AVRegularity.streamFlow φ hφ s y t, (streamFlow_spatial_smooth hφ s t).continuous⟩

theorem inverseStreamFlowContinuousMap_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (s : ℝ) :
    Continuous (inverseStreamFlowContinuousMap hφ s) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (streamFlow_joint_smooth hφ).continuous.comp
    (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))

theorem inverseStreamFlow_L2_trace_on {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (s : ℝ) (S : Set ℝ)
    (θ : ℝ → Vec 2 → ℝ) (hθ : ∀ t ∈ S, MemL2On Set.univ (θ t))
    (ht : ∀ t ∈ S, Tendsto (fun r => eLpNorm (fun x => θ r x - θ t x) 2 volume)
      (𝓝[S] t) (𝓝 0)) :
    ∀ t ∈ S, Tendsto (fun r => eLpNorm
      (fun x => θ r (AVRegularity.streamFlow φ hφ s x r) -
        θ t (AVRegularity.streamFlow φ hφ s x t)) 2 volume) (𝓝[S] t) (𝓝 0) := by
  have hm (t : S) : MemLp (θ t) 2 volume := by
    simpa only [MemL2On, Measure.restrict_univ] using hθ t t.property
  have hc (t : S) : Tendsto (fun r : S => eLpNorm (fun x => θ r x - θ t x) 2 volume)
      (𝓝 t) (𝓝 0) :=
    (tendsto_nhdsWithin_iff_subtype t.property _ _).1 (ht t t.property)
  have hcomp := continuous_L2_trace_comp (fun t : S => θ t) hm hc
    (fun t : S => inverseStreamFlowContinuousMap hφ s t)
    ((inverseStreamFlowContinuousMap_continuous hφ s).comp continuous_subtype_val)
    (fun t => streamFlow_measurePreserving hφ s t)
  intro t htin
  exact (tendsto_nhdsWithin_iff_subtype htin _ _).2 (hcomp ⟨t, htin⟩)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Almost-everywhere spatial weak gradients of a chart pullback. -/

/-- Adapted from the upstream product-space L² section argument. -/
theorem memL2_spatial_sections {u : ℝ × Vec 2 → ℝ} (a b : ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), MemLp (fun x => u (t, x)) 2 volume := by
  have hm : (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec 2)))) =
      (volume.restrict (Set.Ioo a b)).prod (volume : Measure (Vec 2)) := by
    rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm] at hu
  have hmeas := hu.aestronglyMeasurable.prodMk_left
  have hi := hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hs := hi.prod_right_ae
  filter_upwards [hmeas, hs] with t ht hi
  exact (memLp_two_iff_integrable_sq ht).2 (by simpa [Real.norm_eq_abs, sq_abs] using hi)

theorem streamFlow_ae_weakGradient {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ)
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : ∀ t ∈ Set.Icc a b, MemL2On Set.univ (u t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      HasWeakGradientOn Set.univ (u t) (Du t)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      HasWeakGradientOn Set.univ (fun y => u t (AVRegularity.streamFlow φ hφ t y s))
        (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
          (Du t (AVRegularity.streamFlow φ hφ t y s))) := by
  have hs : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      ∀ i : Fin 2, MemLp (fun x => Du t x i) 2 volume := by
    rw [Filter.eventually_all]
    intro i
    exact memL2_spatial_sections a b (hDu i)
  filter_upwards [hs, hw, ae_restrict_mem measurableSet_Ioo] with t ht hw htmem
  apply streamFlow_weakGradient hφ t s (hu t ⟨htmem.1.le, htmem.2.le⟩) _ hw
  intro i
  simpa only [MemL2On, Measure.restrict_univ] using ht i

/-! Space-time L² control for the inverse fixed-start chart. -/

theorem inverseStreamFlowTime_restrict_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) :
    MeasurePreserving (streamFlowTimeHomeomorph hφ s).symm
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ))
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
  have hmp := MeasurePreserving.symm (streamFlowTimeHomeomorph hφ s).toMeasurableEquiv
    (streamFlowTime_measurePreserving hφ s)
  have hm := hmp.restrict_preimage
    (s := Set.Ioo a b ×ˢ (Set.univ : Set (Vec 2)))
    (measurableSet_Ioo.prod MeasurableSet.univ)
  have he : (streamFlowTimeHomeomorph hφ s).toMeasurableEquiv.symm ⁻¹' (Set.Ioo a b ×ˢ Set.univ) =
      Set.Ioo a b ×ˢ Set.univ := by
    ext p
    rfl
  rw [he] at hm
  exact hm

theorem inverseStreamFlow_joint_gradient_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) {Du : ℝ → Vec 2 → Vec 2}
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) :
    ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x p.1) p.2)ᵀ.mulVec
        (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
  let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a b ×ˢ Set.univ)
  let J := fun p : ℝ × Vec 2 => jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x p.1) p.2
  obtain ⟨C, hC, hb⟩ := inverseStreamFlow_jacMatrix_bounded_on_compact_time hφ s
    (Set.Icc a b) isCompact_Icc
  have htop (i j : Fin 2) : MemLp (fun p => J p i j) ⊤ μ := by
    have hc := (continuous_apply j).comp ((continuous_apply i).comp
      (inverseStreamFlow_jacMatrix_joint_continuous hφ s))
    refine memLp_top_of_bound hc.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
    rw [Real.norm_eq_abs]
    exact hb p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 i j
  have hcomp (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1) i) 2 μ :=
    (hDu i).comp_measurePreserving (inverseStreamFlowTime_restrict_measurePreserving hφ s a b)
  intro j
  have hmul (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => J p i j * Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1) i) 2 μ :=
    (htop i j).mul (hcomp i)
  have he : (fun p : ℝ × Vec 2 => ((J p)ᵀ.mulVec
      (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) =
      (fun p => ∑ i : Fin 2, J p i j * Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1) i) := by
    funext p
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  change MemLp (fun p => ((J p)ᵀ.mulVec
    (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) 2 μ
  rw [he]
  exact memLp_finsetSum _ (fun i _ => hmul i)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Parent diffusivity expressed in either the parent or the fine wavelength. -/

theorem bandChain_parent_comparisons {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          ocAsymp C (κ (m - 1)) (ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q)) ∧
          ocAsymp C (κ (m - 1)) (ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q)) := by
  obtain ⟨C, hC, Lc, hLc, hc⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, Lk, hLk, hk⟩ := epsilon_power_scale_asymp hq.1 ((1 + α) - ocGamma α q)
  have hCp : 0 < C := by linarith
  have hKp : 0 < K := by linarith
  have hCK : 1 ≤ C * K := by nlinarith
  refine ⟨C * K, hCK, max Lc Lk, hLc.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛc : Lc ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛk : Lk ≤ Λ := (le_max_right _ _).trans hΛ
  have hi := hc Λ hΛc M hM κ hκ (m - 1) (by omega) (by omega)
  have hpowers : ocAsymp K (ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q))
      (ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q)) := by
    simpa only [enhancement_exponent_identity hq.1] using hk Λ m hΛk hm
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 (hLc.trans hΛc)).1
  exact ⟨asymp_mono_constant hCp (by nlinarith) (Real.rpow_pos_of_pos hE _).le hi,
    asymp_trans hCp hKp hi (asymp_symm hKp hpowers)⟩

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Filter Topology
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Section5
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Weak H¹ transport on the periodic cell. -/

theorem periodic_cell_L2_locallyIntegrable {u : Vec 2 → ℝ}
    (hu : MemL2On unitCube u) (hp : IsZ2Periodic u) : LocallyIntegrable u volume := by
  intro x
  let b : ContDiffBump x := ⟨1, 2, by norm_num, by norm_num⟩
  have hi := periodic_compact_pairing_integrable hu hp (b.contDiff (n := (⊤ : ℕ∞))).continuous b.hasCompactSupport
  obtain ⟨S, hS, he⟩ := Filter.eventually_iff_exists_mem.mp b.eventuallyEq_one
  obtain ⟨U, hUS, hU, hxU⟩ := mem_nhds_iff.mp hS
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  apply hi.integrableOn.congr_fun _ hU.measurableSet
  intro y hy
  simp only [he y (hUS hy), Pi.one_apply, mul_one]

 theorem streamFlow_cell_gradient_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) {Du : Vec 2 → Vec 2}
    (hp : IsZ2Periodic Du) (hDu : GradMemL2On unitCube Du) :
    GradMemL2On unitCube
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (Du (AVRegularity.streamFlow φ hφ t y s))) := by
  obtain ⟨C, _, hb⟩ := streamFlow_jacMatrix_bounded hφ t s
  let F := fun y => AVRegularity.streamFlow φ hφ t y s
  have htop (i j : Fin 2) : MemLp (fun y => jacMatrix F y i j) ⊤
      (volume.restrict unitCube) :=
    memLp_top_of_bound
      ((jacMatrix_entry_smooth (streamFlow_spatial_smooth hφ t s) i j).continuous.aestronglyMeasurable)
      C (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using hb y i j))
  have hcomp (i : Fin 2) : MemLp (fun y => Du (F y) i) 2 (volume.restrict unitCube) :=
    streamFlow_cell_memL2 hφ t s (fun k x => congrFun (hp k x) i) (hDu i)
  intro j
  change MemLp _ 2 (volume.restrict unitCube)
  have he : (fun y => ((jacMatrix F y)ᵀ.mulVec (Du (F y))) j) =
      (fun y => ∑ i : Fin 2, jacMatrix F y i j * Du (F y) i) := by
    funext y
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [he]
  exact memLp_finsetSum _ (fun i _ => (htop i j).mul (hcomp i))

 theorem streamFlow_periodicH1 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) :
    IsPeriodicH1With (fun y => u (AVRegularity.streamFlow φ hφ t y s))
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (Du (AVRegularity.streamFlow φ hφ t y s))) := by
  refine ⟨?_, ?_, streamFlow_cell_memL2 hφ t s hu.1 hu.2.2.1,
    streamFlow_cell_gradient_memL2 hφ t s hu.2.1 hu.2.2.2.1, ?_⟩
  · intro k x
    dsimp only
    rw [streamFlow_lattice_equivariant, hu.1]
  · intro k x
    dsimp only
    rw [streamFlow_jacMatrix_spatial_periodic, streamFlow_lattice_equivariant, hu.2.1]
  · let X := streamFlowHomeomorph hφ t s
    have hY : ContDiff ℝ (⊤ : ℕ∞) (X.symm : Vec 2 → Vec 2) :=
      streamFlow_spatial_smooth hφ s t
    have ht := weakGradient_homeomorph_piola X (streamFlow_measurePreserving hφ t s)
      hY (fun x => streamFlow_jacMatrix_det_one hφ s t x)
      (periodic_cell_L2_locallyIntegrable hu.2.2.1 hu.1)
      (fun i => periodic_cell_L2_locallyIntegrable (hu.2.2.2.1 i)
        (fun k x => congrFun (hu.2.1 k x) i)) hu.2.2.2.2
    have hc (y : Vec 2) : rowCofactor (gradMatrix (X.symm : Vec 2 → Vec 2) (X y)) =
        jacMatrix (X : Vec 2 → Vec 2) y := by
      rw [rowCofactor_eq_jacMatrix_inverse (hY.differentiable (by simp)) _
        (show (jacMatrix (X.symm : Vec 2 → Vec 2) (X y)).det = 1 from
          streamFlow_jacMatrix_det_one hφ s t _)]
      exact homeomorph_inverse_jacMatrix X
        ((streamFlow_spatial_smooth hφ t s).differentiable (by simp))
        (hY.differentiable (by simp)) y
    simp_rw [hc] at ht
    exact ht

 theorem chart_cell_h1_energy (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ) {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) :
    ∃ Du' : Vec 2 → Vec 2,
      IsPeriodicH1With (fun y => u (ocChart α q Λ m φ hφ l t y)) Du' ∧
      (∫ y in unitCube, Homogenization.vecDot (Du' y)
        ((ocMaterialMetric α q Λ m φ hφ l t y).mulVec (Du' y))) =
      ∫ x in unitCube, Homogenization.vecDot (Du x) (Du x) := by
  refine ⟨fun y => (jacMatrix (ocChart α q Λ m φ hφ l t) y)ᵀ.mulVec
    (Du (ocChart α q Λ m φ hφ l t y)), streamFlow_periodicH1 hφ t _ hu, ?_⟩
  have he (y : Vec 2) := metric_pullback_energy
    (jacMatrix (ocChart α q Λ m φ hφ l t) y)
    (by change IsUnit (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x _) y).det
        rw [streamFlow_jacMatrix_det_one hφ]; exact isUnit_one)
    (Du (ocChart α q Λ m φ hφ l t y))
  simp_rw [ocMaterialMetric, he]
  exact streamFlow_cell_integral hφ t _ (fun x => Homogenization.vecDot (Du x) (Du x))
    (fun k x => by dsimp only; rw [hu.2.1 k x])

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Two-sided interior contrast at the parent wavelength. -/

theorem bandChain_interior_contrast {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m < M →
          ocAsymp C (Real.sqrt (κ (m - 1) / κ m))
            (ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))) := by
  obtain ⟨Cp, hCp, Lp, hLp, hp⟩ := bandChain_parent_comparisons hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cf, hCf, Lf, hLf, hf⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, Lk, hLk, hk⟩ := epsilon_power_scale_asymp hq.1 (-ocGamma α q)
  have hCpp : 0 < Cp := by linarith
  have hCfp : 0 < Cf := by linarith
  have hKp : 0 < K := by linarith
  have hprod : 1 ≤ Cp * Cf := by nlinarith
  have hs : 1 ≤ Real.sqrt (Cp * Cf) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hprod
  have hsp : 0 < Real.sqrt (Cp * Cf) := by linarith
  have hC : 1 ≤ Real.sqrt (Cp * Cf) * K := by nlinarith
  refine ⟨Real.sqrt (Cp * Cf) * K, hC, max Lp (max Lf Lk), hLp.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛp : Lp ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛf : Lf ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛk : Lk ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 := hLp.trans hΛp
  have hΛ1 : 1 ≤ Λ := by omega
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hi := hf Λ hΛf M hM κ hκ m (by omega) hmM
  have hb := (hp Λ hΛp M hM κ hκ m hm (by omega)).2
  have hratio := asymp_div hCpp hCfp (Real.rpow_pos_of_pos he _).le
    (Real.rpow_pos_of_pos he _) (bandChain_pos hΛ1 hζ hκ (by omega)) hb hi
  have hpower : ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) /
      ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) = ocEpsilon q Λ m ^ (-2 * ocGamma α q) := by
    rw [← Real.rpow_sub he]
    congr 1
    ring
  rw [hpower] at hratio
  have hsratio := asymp_sqrt (mul_pos hCpp hCfp) (Real.rpow_pos_of_pos he _).le hratio
  have hsPower : Real.sqrt (ocEpsilon q Λ m ^ (-2 * ocGamma α q)) =
      ocEpsilon q Λ m ^ (-ocGamma α q) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.le]
    congr 1
    ring
  rw [hsPower] at hsratio
  have hscale := hk Λ m hΛk hm
  have h := asymp_trans hsp hKp hsratio hscale
  simpa only [mul_neg] using h

/-! Bounded contrast at the permitted terminal band. -/

theorem bandChain_terminal_contrast {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 2 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        κ (M - 1) / κ M ≤ C := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := bandChain_parent_comparisons hα0 hα1 hs0 hs1 hq hζ
  have hCp : 0 < C := by linarith
  refine ⟨2 * C, by linarith, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ
  have hΛ1 : 1 ≤ Λ := by omega
  have hν := bandChain_pos hΛ1 hζ hκ (le_refl M)
  have hl : ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2 ≤ κ M := hκ.1.1
  have hu := (hb Λ hΛ M (by omega) κ hκ M hM (le_refl M)).2.2
  apply (div_le_iff₀ hν).2
  have hs := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * C by positivity)
  have heq : (2 * C) * (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2) =
      C * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) := by ring
  rw [heq] at hs
  exact hu.trans hs

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory Filter Topology
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Transport of the energy-space conditions, including the initial L² trace. -/

theorem streamFlow_energy_space {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ)
    {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : ∀ t ∈ Set.Icc a b, MemL2On Set.univ (u t))
    (ht : ∀ t ∈ Set.Icc a b, Tendsto
      (fun r => eLpNorm (fun x => u r x - u t x) 2 volume) (𝓝[Set.Icc a b] t) (𝓝 0))
    (hinit : u a =ᵐ[volume] u₀)
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), HasWeakGradientOn Set.univ (u t) (Du t)) :
    (∀ t ∈ Set.Icc a b, MemL2On Set.univ
      (fun x => u t (AVRegularity.streamFlow φ hφ t x s))) ∧
    (∀ t ∈ Set.Icc a b, Tendsto (fun r => eLpNorm
      (fun x => u r (AVRegularity.streamFlow φ hφ r x s) -
        u t (AVRegularity.streamFlow φ hφ t x s)) 2 volume) (𝓝[Set.Icc a b] t) (𝓝 0)) ∧
    ((fun x => u a (AVRegularity.streamFlow φ hφ a x s)) =ᵐ[volume]
      (fun x => u₀ (AVRegularity.streamFlow φ hφ a x s))) ∧
    (∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ p.1 x s) p.2)ᵀ.mulVec
        (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), HasWeakGradientOn Set.univ
      (fun y => u t (AVRegularity.streamFlow φ hφ t y s))
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (Du t (AVRegularity.streamFlow φ hφ t y s)))) := by
  refine ⟨?_, streamFlow_L2_trace_on hφ s (Set.Icc a b) u hu ht,
    (streamFlow_measurePreserving hφ a s).quasiMeasurePreserving.ae_eq_comp hinit,
    streamFlow_joint_gradient_memL2 hφ s a b hDu,
    streamFlow_ae_weakGradient hφ s a b hu hDu hw⟩
  intro t ht
  have hu' : MemLp (u t) 2 volume := by
    simpa only [MemL2On, Measure.restrict_univ] using hu t ht
  simpa only [MemL2On, Measure.restrict_univ, Function.comp_def] using
    hu'.comp_measurePreserving (streamFlow_measurePreserving hφ t s)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! The enhancement numerator is controlled by the parent diffusivity uniformly in contrast. -/

theorem reciprocal_enhancement_bound {Cp Cf ν B P Q : ℝ}
    (hCp : 0 < Cp) (hCf : 0 < Cf) (hν : 0 < ν) (_hB : 0 < B)
    (_hP : 0 ≤ P) (hQ : 0 ≤ Q) (hνB : ν ≤ B)
    (hνl : Cf⁻¹ * P ≤ ν) (hBl : Cp⁻¹ * Q ≤ B) :
    ν + P * Q / ν ≤ (1 + Cp * Cf) * B := by
  have hprod := mul_le_mul hνl hBl (mul_nonneg (inv_pos.mpr hCp).le hQ) hν.le
  have hscaled := mul_le_mul_of_nonneg_left hprod (mul_pos hCp hCf).le
  have hcancel : (Cp * Cf) * ((Cf⁻¹ * P) * (Cp⁻¹ * Q)) = P * Q := by
    field_simp
  rw [hcancel] at hscaled
  have hdiv : P * Q / ν ≤ Cp * Cf * B := by
    apply (div_le_iff₀ hν).2
    convert hscaled using 1; ring
  have h := add_le_add hνB hdiv
  convert h using 1; ring

theorem bandChain_enhancement_bound {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          κ m + ocEpsilon q Λ m ^ (2 * (1 + α)) / κ m ≤ C * κ (m - 1) := by
  obtain ⟨Cp, hCp, Lp, hLp, hp⟩ := bandChain_parent_comparisons hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cf, hCf, Lf, hLf, hf⟩ := bandChain_all_level_bounds hα0 hα1 hs0 hs1 hq hζ
  have hCpp : 0 < Cp := by linarith
  have hCfp : 0 < Cf := by linarith
  refine ⟨1 + Cp * Cf, by nlinarith, max Lp Lf, hLp.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛp : Lp ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛf : Lf ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLp.trans hΛp
  have hΛ1 : 1 ≤ Λ := by omega
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hν := bandChain_pos hΛ1 hζ hκ hmM
  have hB := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
  have h := reciprocal_enhancement_bound hCpp hCfp hν hB
    (Real.rpow_pos_of_pos he ((1 + α) + ocGamma α q)).le
    (Real.rpow_pos_of_pos he ((1 + α) - ocGamma α q)).le
    (bandChain_step_ge hΛ1 hζ hκ (by omega) hmM)
    (hf Λ hΛf M hM κ hκ m (by omega) hmM).1
    (hp Λ hΛp M hM κ hκ m hm hmM).2.1
  have hpower : ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) *
      ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) = ocEpsilon q Λ m ^ (2 * (1 + α)) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  simpa only [hpower] using h

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Filter Topology
open AVenhance.Infra.Torus
open scoped ENNReal
namespace AVRegularity.CycleReference

/-! Continuous periodic L² traces under the renewal chart. -/

local instance inverseTorusChartTraceMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance inverseTorusChartTraceHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance inverseTorusChartTraceProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def inverseTorusChartContinuousMap {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) : C(ChartTorus, ChartTorus) :=
  ⟨torusChart hφ t s,
    (torusChart_inverse_joint_continuous hφ s).comp (continuous_const.prodMk continuous_id)⟩

 theorem inverseTorusChartContinuousMap_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) : Continuous (inverseTorusChartContinuousMap hφ s) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact torusChart_inverse_joint_continuous hφ s

 theorem inverseStreamFlow_cell_L2_trace_on {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (S : Set ℝ)
    (θ : ℝ → Vec 2 → ℝ)
    (hp : ∀ t ∈ S, IsZ2Periodic (θ t))
    (hθ : ∀ t ∈ S, MemL2On unitCube (θ t))
    (ht : ∀ t ∈ S, Tendsto (fun r => eLpNorm (fun x => θ r x - θ t x) 2
      (volume.restrict unitCube)) (𝓝[S] t) (𝓝 0)) :
    ∀ t ∈ S, Tendsto (fun r => eLpNorm
      (fun x => θ r (AVRegularity.streamFlow φ hφ s x r) -
        θ t (AVRegularity.streamFlow φ hφ s x t)) 2 (volume.restrict unitCube))
      (𝓝[S] t) (𝓝 0) := by
  let u : S → ChartTorus → ℝ := fun t => periodicToTorus (θ t)
  have hu (t : S) : MemLp (u t) 2 volume := cell_memLp_toTorus (hθ t t.property)
  let F : S → Lp ℝ 2 (volume : Measure ChartTorus) := fun t => (hu t).toLp (u t)
  have hc (t : S) : Tendsto (fun r : S => eLpNorm (fun z => u r z - u t z) 2 volume)
      (𝓝 t) (𝓝 0) := by
    have h := (tendsto_nhdsWithin_iff_subtype t.property _ _).mp (ht t t.property)
    have he (r : S) := cell_eLpNorm_toTorus
      ((hθ r r.property).aestronglyMeasurable.sub (hθ t t.property).aestronglyMeasurable)
      (p := 2)
    convert h using 1
    funext r
    exact he r
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
    simpa only [F, Lp.edist_toLp_toLp, Pi.sub_def] using hc t
  have hcomp := hF.compMeasurePreservingLp
    ((inverseTorusChartContinuousMap_continuous hφ s).comp continuous_subtype_val)
    (fun t : S => torusChart_measurePreserving hφ t s)
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro t htS
  apply (tendsto_nhdsWithin_iff_subtype htS _ _).mpr
  have h := hcomp.continuousAt (x := (⟨t, htS⟩ : S))
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0] at h
  simp only [F, Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp, Pi.sub_def,
    Function.comp_def] at h
  have he (r : S) := cell_eLpNorm_toTorus
    ((streamFlow_cell_memL2 hφ s r (hp r r.property) (hθ r r.property)).aestronglyMeasurable.sub
      (streamFlow_cell_memL2 hφ s t (hp t htS) (hθ t htS)).aestronglyMeasurable) (p := 2)
  have heq (r : S) :
      eLpNorm (fun z => u r (torusChart hφ r s z) - u ⟨t, htS⟩ (torusChart hφ t s z)) 2 volume =
      eLpNorm (fun x => θ r (AVRegularity.streamFlow φ hφ s x r) -
        θ t (AVRegularity.streamFlow φ hφ s x t)) 2 (volume.restrict unitCube) := by
    have hr := periodicToTorus_chart hφ r s (hp r r.property)
    have htr := periodicToTorus_chart hφ t s (hp t htS)
    have hfun : (fun z => u r (torusChart hφ r s z) - u ⟨t, htS⟩ (torusChart hφ t s z)) =
        periodicToTorus (fun x => θ r (AVRegularity.streamFlow φ hφ s x r) -
          θ t (AVRegularity.streamFlow φ hφ s x t)) := by
      funext z
      exact congrArg₂ (· - ·) (congrFun hr z).symm (congrFun htr z).symm
    rw [hfun]
    exact he r
  change Tendsto (fun r : S => eLpNorm
    (fun z => u r (torusChart hφ r s z) - u ⟨t, htS⟩ (torusChart hφ t s z)) 2 volume)
    (𝓝 (⟨t, htS⟩ : S)) (𝓝 0) at h
  have hfinal := h.congr' (Filter.Eventually.of_forall (fun r => heq r))
  convert hfinal using 1
  funext r
  rfl

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Interior molecular radius and conversion to the old preparation radius. -/

theorem bandChain_molecular_radius {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m < M → ∀ cMol : ℝ, 0 < cMol →
          ocAsymp C (ocRhoMol α q Λ m cMol (κ m))
            (cMol * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) ∧
          ocRhoMol α q Λ m cMol (κ m) / ocEpsilon q Λ m ^ (1 + ocC α q) ≤
            C * cMol * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, Lk, hLk, hk⟩ := epsilon_power_scale_asymp hq.1 (-ocDelta α q)
  have hCip : 0 < Ci := by linarith
  have hKp : 0 < K := by linarith
  have hs : 1 ≤ Real.sqrt Ci := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hCi
  have hsp : 0 < Real.sqrt Ci := by linarith
  have hC : 1 ≤ Real.sqrt Ci * K := by nlinarith
  have hSC : Real.sqrt Ci ≤ Real.sqrt Ci * K := by nlinarith
  refine ⟨Real.sqrt Ci * K, hC, max Li Lk, hLi.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM cMol hcMol
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛk : Lk ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLi.trans hΛi
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hA : ocA α q Λ m = ocEpsilon q Λ m ^ ((1 + α) - 2) := rfl
  have hAp : 0 < ocA α q Λ m := by rw [hA]; exact Real.rpow_pos_of_pos he _
  have hnu := hi Λ hΛi M hM κ hκ m (by omega) hmM
  have hquot := asymp_div hCip (by norm_num : (0 : ℝ) < 1)
    (Real.rpow_pos_of_pos he _).le (Real.rpow_pos_of_pos he _) hAp hnu
    (show ocAsymp 1 (ocA α q Λ m) (ocEpsilon q Λ m ^ ((1 + α) - 2)) by
      rw [hA]; exact asymp_one_self _)
  have hpow : ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) /
      ocEpsilon q Λ m ^ ((1 + α) - 2) = ocEpsilon q Λ m ^ (2 + ocGamma α q) := by
    rw [← Real.rpow_sub he]
    congr 1
    ring
  simp only [mul_one, hpow] at hquot
  have hroot := asymp_sqrt hCip (Real.rpow_pos_of_pos he _).le hquot
  have hsPower : Real.sqrt (ocEpsilon q Λ m ^ (2 + ocGamma α q)) =
      ocEpsilon q Λ m ^ (1 + ocGamma α q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.le]
    congr 1
    ring
  rw [hsPower] at hroot
  have hmolecular : ocAsymp (Real.sqrt Ci) (ocRhoMol α q Λ m cMol (κ m))
      (cMol * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) := asymp_scale_left hcMol.le hroot
  refine ⟨asymp_mono_constant hsp hSC
    (mul_pos hcMol (Real.rpow_pos_of_pos he _)).le hmolecular, ?_⟩
  have hdiv := div_le_div_of_nonneg_right hmolecular.2
    (Real.rpow_pos_of_pos he (1 + ocC α q)).le
  have hratio : (Real.sqrt Ci * (cMol * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2))) /
      ocEpsilon q Λ m ^ (1 + ocC α q) =
        Real.sqrt Ci * cMol * ocEpsilon q Λ m ^ (-ocDelta α q) := by
    have hp : ocEpsilon q Λ m ^ (1 + ocGamma α q / 2) / ocEpsilon q Λ m ^ (1 + ocC α q) =
        ocEpsilon q Λ m ^ (-ocDelta α q) := by
      rw [← Real.rpow_sub he, molecular_radius_exponent_identity]
    calc
      _ = Real.sqrt Ci * cMol * (ocEpsilon q Λ m ^ (1 + ocGamma α q / 2) /
          ocEpsilon q Λ m ^ (1 + ocC α q)) := by ring
      _ = _ := by rw [hp]
  rw [hratio] at hdiv
  have hscaled := mul_le_mul_of_nonneg_left (hk Λ m hΛk hm).2 (mul_pos hsp hcMol).le
  have hscaled' : Real.sqrt Ci * cMol * ocEpsilon q Λ m ^ (-ocDelta α q) ≤
      (Real.sqrt Ci * K) * cMol * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)) := by
    convert hscaled using 1; simp only [mul_neg]; ring
  exact hdiv.trans hscaled'

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Filter Topology
open AVenhance.Infra.Torus
open scoped ENNReal
namespace AVRegularity.CycleReference

/-! Continuous periodic L² traces under the renewal chart. -/

local instance torusChartTraceMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusChartTraceHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusChartTraceProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def torusChartContinuousMap {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) : C(ChartTorus, ChartTorus) :=
  ⟨torusChart hφ s t,
    (torusChart_joint_continuous hφ s).comp (continuous_const.prodMk continuous_id)⟩

 theorem torusChartContinuousMap_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) : Continuous (torusChartContinuousMap hφ s) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact torusChart_joint_continuous hφ s

 theorem streamFlow_cell_L2_trace_on {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (S : Set ℝ)
    (θ : ℝ → Vec 2 → ℝ)
    (hp : ∀ t ∈ S, IsZ2Periodic (θ t))
    (hθ : ∀ t ∈ S, MemL2On unitCube (θ t))
    (ht : ∀ t ∈ S, Tendsto (fun r => eLpNorm (fun x => θ r x - θ t x) 2
      (volume.restrict unitCube)) (𝓝[S] t) (𝓝 0)) :
    ∀ t ∈ S, Tendsto (fun r => eLpNorm
      (fun x => θ r (AVRegularity.streamFlow φ hφ r x s) -
        θ t (AVRegularity.streamFlow φ hφ t x s)) 2 (volume.restrict unitCube))
      (𝓝[S] t) (𝓝 0) := by
  let u : S → ChartTorus → ℝ := fun t => periodicToTorus (θ t)
  have hu (t : S) : MemLp (u t) 2 volume := cell_memLp_toTorus (hθ t t.property)
  let F : S → Lp ℝ 2 (volume : Measure ChartTorus) := fun t => (hu t).toLp (u t)
  have hc (t : S) : Tendsto (fun r : S => eLpNorm (fun z => u r z - u t z) 2 volume)
      (𝓝 t) (𝓝 0) := by
    have h := (tendsto_nhdsWithin_iff_subtype t.property _ _).mp (ht t t.property)
    have he (r : S) := cell_eLpNorm_toTorus
      ((hθ r r.property).aestronglyMeasurable.sub (hθ t t.property).aestronglyMeasurable)
      (p := 2)
    convert h using 1
    funext r
    exact he r
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
    simpa only [F, Lp.edist_toLp_toLp, Pi.sub_def] using hc t
  have hcomp := hF.compMeasurePreservingLp
    ((torusChartContinuousMap_continuous hφ s).comp continuous_subtype_val)
    (fun t : S => torusChart_measurePreserving hφ s t)
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro t htS
  apply (tendsto_nhdsWithin_iff_subtype htS _ _).mpr
  have h := hcomp.continuousAt (x := (⟨t, htS⟩ : S))
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0] at h
  simp only [F, Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp, Pi.sub_def,
    Function.comp_def] at h
  have he (r : S) := cell_eLpNorm_toTorus
    ((streamFlow_cell_memL2 hφ r s (hp r r.property) (hθ r r.property)).aestronglyMeasurable.sub
      (streamFlow_cell_memL2 hφ t s (hp t htS) (hθ t htS)).aestronglyMeasurable) (p := 2)
  have heq (r : S) :
      eLpNorm (fun z => u r (torusChart hφ s r z) - u ⟨t, htS⟩ (torusChart hφ s t z)) 2 volume =
      eLpNorm (fun x => θ r (AVRegularity.streamFlow φ hφ r x s) -
        θ t (AVRegularity.streamFlow φ hφ t x s)) 2 (volume.restrict unitCube) := by
    have hr := periodicToTorus_chart hφ s r (hp r r.property)
    have htr := periodicToTorus_chart hφ s t (hp t htS)
    have hfun : (fun z => u r (torusChart hφ s r z) - u ⟨t, htS⟩ (torusChart hφ s t z)) =
        periodicToTorus (fun x => θ r (AVRegularity.streamFlow φ hφ r x s) -
          θ t (AVRegularity.streamFlow φ hφ t x s)) := by
      funext z
      exact congrArg₂ (· - ·) (congrFun hr z).symm (congrFun htr z).symm
    rw [hfun]
    exact he r
  change Tendsto (fun r : S => eLpNorm
    (fun z => u r (torusChart hφ s r z) - u ⟨t, htS⟩ (torusChart hφ s t z)) 2 volume)
    (𝓝 (⟨t, htS⟩ : S)) (𝓝 0) at h
  have hfinal := h.congr' (Filter.Eventually.of_forall (fun r => heq r))
  convert hfinal using 1
  funext r
  rfl

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Recovering the physical drift correction from the pulled-back tested equation. -/

theorem chart_drift_correction_integrable_from_pulled_tests
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s a c : ℝ)
    (bm : ℝ → Vec 2 → Vec 2) (Am : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (qm : ℝ → Vec 2 → Vec 2) (fm θ : ℝ → Vec 2 → ℝ) (Dm : ℝ → Vec 2 → Vec 2)
    (hI : ∀ ζ : ℝ → Vec 2 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ζ p.1 p.2) →
      HasCompactSupport (fun p : ℝ × Vec 2 => ζ p.1 p.2) →
      (∀ t, c ≤ t → ∀ x, ζ t x = 0) →
      Integrable (planeWeakIntegrand bm Am qm fm (chartPull hφ s θ) Dm ζ)
        (volume.restrict (Set.Ioo a c ×ˢ Set.univ)))
    (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hz : ∀ t, c ≤ t → ∀ x, η t x = 0) :
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * vecDot (streamVel φ p.1 p.2)
      (spaceGrad (η p.1) p.2)) (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) := by
  let ζ := chartPull hφ s η
  have hζ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ζ p.1 p.2) :=
    streamFlow_test_smooth hφ s hη
  have hcζ : HasCompactSupport (fun p : ℝ × Vec 2 => ζ p.1 p.2) :=
    streamFlow_test_compact hφ s hc
  have hzζ : ∀ t, c ≤ t → ∀ x, ζ t x = 0 := fun t ht x => hz t ht _
  have hi := tested_integrability_implies_drift_correction_integrability bm Am qm fm
    (chartPull hφ s θ) Dm a c hI (chartVector hφ s (streamVel φ))
    (chartVector_joint_smooth hφ s (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth)
    ζ hζ hcζ hzζ
  let X := streamFlowTimeHomeomorph hφ s
  let g := fun p : ℝ × Vec 2 => θ p.1 p.2 * vecDot (streamVel φ p.1 p.2)
    (spaceGrad (η p.1) p.2)
  have he : g ∘ X = (fun p : ℝ × Vec 2 => chartPull hφ s θ p.1 p.2 *
      vecDot (chartVector hφ s (streamVel φ) p.1 p.2) (spaceGrad (ζ p.1) p.2)) := by
    funext p
    have hs : DifferentiableAt ℝ (η p.1) (AVRegularity.streamFlow φ hφ p.1 p.2 s) :=
      (hη.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _
    have hg := spaceGrad_comp_jacMatrix hs
      ((streamFlow_spatial_smooth hφ p.1 s).differentiable (by simp) p.2)
    change θ p.1 _ * vecDot _ _ = θ p.1 _ * vecDot _ _
    congr 1
    change vecDot _ _ = vecDot ((chartJac hφ s p.1 p.2)⁻¹.mulVec _) (spaceGrad
      (fun x => η p.1 (AVRegularity.streamFlow φ hφ p.1 x s)) p.2)
    rw [hg]
    exact (inverse_pullback_pairing _ (by
      rw [chartJac, streamFlow_jacMatrix_det_one hφ]; exact isUnit_one) _ _).symm
  rw [← he] at hi
  exact ((streamFlowTime_restrict_measurePreserving hφ s a c).integrable_comp_emb
    X.measurableEmbedding).mp hi

end AVRegularity.CycleReference
end
end
