-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneH1TimeMemLpReadouts
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CycleWords.CellTransitionGeometry
import AVRegularity.Weighted.DriftCoefficientEmbedding
import AVRegularity.CycleJoint.PreparationScaledFlowBudget
public import AVRegularity.Analysis.Convolution.Kernel.Commutation.Torus
import AVenhance.Infra.Classical.Drift
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Actual ambient L2 readouts of the native H1 carrier assembled from a weak gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1OfWeakGradient_valueOperator_ae (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E) (hf : MemLp f 2 (volume.restrict univ))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict univ))
    (hw : ∀ i e, HasWeakPartialDerivOn univ i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) :
    (planeHkValueOperator 1 (planeH1OfWeakGradient f G hf hG hw) : Vec 2 → E)
      =ᵐ[volume] f := by
  rw [planeHkValueOperator_apply]
  apply (univToPlane_ae _).trans
  have hp := planeH1OfWeakGradient_value_ae f G hf hG hw
  simpa only [Measure.restrict_univ] using hp

theorem planeH1OfWeakGradient_gradientOperator_ae (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E) (hf : MemLp f 2 (volume.restrict univ))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict univ))
    (hw : ∀ i e, HasWeakPartialDerivOn univ i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) (i : Fin 2) :
    (planeH1GradientOperator (planeH1OfWeakGradient f G hf hG hw) i : Vec 2 → E)
      =ᵐ[volume] G i := by
  rw [planeH1GradientOperator_apply]
  apply (univToPlane_ae _).trans
  have hp := planeH1OfWeakGradient_gradient_ae f G hf hG hw (fun _ => i)
  simpa only [Measure.restrict_univ] using hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Moving the diffusion deviation into the true forcing flux preserves the native Riesz dual exactly. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakDual_diffusion_reallocation
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D D' : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    planeWeakDualRepresentative T D u F =
      planeWeakDualRepresentative T D' u
        ((D - D') (planeH1GradientOperator u) + F) := by
  apply ext_inner_right ℝ
  intro z
  rw [planeWeakDualRepresentative_pair, planeWeakDualRepresentative_pair]
  simp only [sub_apply]
  congr 1
  congr 1
  abel

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Scalar normalization of the actual plane Riesz dual respects every spatial PDE term. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakDualRepresentative_smul (c : ℝ)
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    planeWeakDualRepresentative (c • T) (c • D) u (c • F) =
      c • planeWeakDualRepresentative T D u F := by
  simp only [planeWeakDualRepresentative_eq_adjoint, smul_apply,
    ← smul_add, map_smul, smul_sub, smul_neg]

theorem planeWeakDualRepresentative_diffusion_normalization (ν : ℝ) (hν : ν ≠ 0)
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    ν⁻¹ • planeWeakDualRepresentative T (ν • D) u F =
      planeWeakDualRepresentative (ν⁻¹ • T) D u (ν⁻¹ • F) := by
  rw [← planeWeakDualRepresentative_smul, smul_smul, inv_mul_cancel₀ hν, one_smul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Norm-controlled recentering changes polynomial moments by a fixed dimensional price. -/

theorem polynomialMomentRoot_le_linear_norm (ϖ : ℝ) (z : Vec 2) :
    polynomialMomentRoot ϖ z ≤ 1 + 2 * |ϖ| * ‖z‖ := by
  have h0 := norm_le_pi_norm z (0 : Fin 2)
  have h1 := norm_le_pi_norm z (1 : Fin 2)
  rw [Real.norm_eq_abs] at h0 h1
  have h0sq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg z)).mpr h0
  have h1sq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg z)).mpr h1
  rw [sq_abs] at h0sq h1sq
  have hs := mul_le_mul_of_nonneg_left (add_le_add h0sq h1sq) (sq_nonneg ϖ)
  rw [← sq_abs ϖ] at hs
  unfold polynomialMomentRoot
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hpos : 0 ≤ |ϖ| * ‖z‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  rw [← sq_abs ϖ]
  nlinarith only [hs, hpos, sq_nonneg (|ϖ| * ‖z‖)]

theorem polynomialMomentRoot_le_of_norm_le
    (ϖ L : ℝ) (hϖ : 0 ≤ ϖ) (hL : 0 ≤ L) (x z : Vec 2)
    (h : ‖x‖ ≤ L * ‖z‖) :
    polynomialMomentRoot ϖ x ≤ (1 + 2 * L) * polynomialMomentRoot ϖ z := by
  calc
    _ ≤ 1 + 2 * |ϖ| * ‖x‖ := polynomialMomentRoot_le_linear_norm ϖ x
    _ = 1 + (2 * ϖ) * ‖x‖ := by rw [abs_of_nonneg hϖ]
    _ ≤ 1 + (2 * ϖ) * (L * ‖z‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) hϖ))
    _ = 1 + (2 * L) * (ϖ * ‖z‖) := by ring
    _ ≤ 1 + (2 * L) * polynomialMomentRoot ϖ z :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (scaledNorm_le_polynomialMomentRoot hϖ z)
        (mul_nonneg (by norm_num) hL))
    _ ≤ polynomialMomentRoot ϖ z + (2 * L) * polynomialMomentRoot ϖ z :=
      add_le_add (polynomialMomentRoot_one_le ϖ z) le_rfl
    _ = _ := by ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! A fixed finite lattice window contains every live cutoff derivative at an observation point. -/

theorem integer_close_mem_floor_window (y : ℝ) (k : ℤ) (hk : |y - k| ≤ 2 / 3) :
    k ∈ Finset.Icc (⌊y⌋ - 1) (⌊y⌋ + 1) := by
  have hlo := Int.floor_le y
  have hhi := Int.lt_floor_add_one y
  have hab := abs_le.mp hk
  have hkr : (⌊y⌋ : ℝ) - 1 ≤ k := by linarith
  have hki : ⌊y⌋ - 1 ≤ k := by exact_mod_cast hkr
  have hur : (k : ℝ) < (⌊y⌋ : ℝ) + 2 := by linarith
  have hui : k < ⌊y⌋ + 2 := by exact_mod_cast hur
  exact Finset.mem_Icc.mpr ⟨hki, by omega⟩

def spatialPatchOverlapIndices (y : Vec 2) : Finset (Fin 2 → ℤ) :=
  ((Finset.Icc (⌊y 0⌋ - 1) (⌊y 0⌋ + 1)) ×ˢ
    (Finset.Icc (⌊y 1⌋ - 1) (⌊y 1⌋ + 1))).map (finTwoArrowEquiv ℤ).symm.toEmbedding

theorem spatialPatchOverlapIndices_card (y : Vec 2) :
    (spatialPatchOverlapIndices y).card = 9 := by
  have he (n : ℤ) : n + 1 + 1 - (n - 1) = 3 := by ring
  simp [spatialPatchOverlapIndices, Int.card_Icc, he]

theorem mem_spatialPatchOverlapIndices (y : Vec 2) (k : Fin 2 → ℤ)
    (hk : ∀ i, |y i - k i| ≤ 2 / 3) : k ∈ spatialPatchOverlapIndices y := by
  apply Finset.mem_map.mpr
  refine ⟨(k 0, k 1), Finset.mem_product.mpr
    ⟨integer_close_mem_floor_window _ _ (hk 0), integer_close_mem_floor_window _ _ (hk 1)⟩, ?_⟩
  exact (finTwoArrowEquiv ℤ).symm_apply_apply k

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Compact smooth Hilbert-valued fields define genuine native H1 tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem smoothHilbert_weakPartial (f : Vec 2 → E) (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (e : E) :
    HasWeakPartialDerivOn univ i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (fderiv ℝ f x (basisVec i))) := by
  have hq : ContDiff ℝ 1 (fun x => inner ℝ e (f x)) := (innerSL ℝ e).contDiff.comp hf
  have he (x : Vec 2) : fderiv ℝ (fun y => inner ℝ e (f y)) x (basisVec i) =
      inner ℝ e (fderiv ℝ f x (basisVec i)) := by
    have hd := (innerSL ℝ e).hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt
    exact congrArg (fun A : Vec 2 →L[ℝ] ℝ => A (basisVec i)) hd.fderiv
  simpa only [he] using HasWeakPartialDerivOn.of_contDiff (U := univ) (i := i) hq

def compactSmoothHilbertH1 (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) : PlaneHk univ 1 E :=
  planeH1OfWeakGradient f (fun i x => fderiv ℝ f x (basisVec i))
    ((hf.continuous.memLp_of_hasCompactSupport hs).mono_measure Measure.restrict_le_self)
    (fun i => (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ (basisVec i))).mono_measure Measure.restrict_le_self)
    (fun i e => smoothHilbert_weakPartial f (hf.of_le (by simp)) i e)

theorem compactSmoothHilbertH1_value_ae (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) :
    (planeHkValueOperator 1 (compactSmoothHilbertH1 f hf hs) : Vec 2 → E) =ᵐ[volume] f := by
  unfold compactSmoothHilbertH1
  exact planeH1OfWeakGradient_valueOperator_ae _ _ _ _ _

theorem compactSmoothHilbertH1_gradient_ae (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (i : Fin 2) :
    (planeH1GradientOperator (compactSmoothHilbertH1 f hf hs) i : Vec 2 → E)
      =ᵐ[volume] fun x => fderiv ℝ f x (basisVec i) := by
  unfold compactSmoothHilbertH1
  exact planeH1OfWeakGradient_gradientOperator_ae _ _ _ _ _ i

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Periodic L2 fields pair integrably with the genuine localized H1 torus test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem periodic_unitPatch_test_pairings_integrable (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (hfp : AVenhance.IsZ2Periodic f)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 E) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    Integrable (fun x => inner ℝ (f x) (ψ.toFunction.jet (valueIndex2 1) x)) volume ∧
      ∀ k : Fin 2, Integrable (fun x => inner ℝ (f x)
        (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x)) volume := by
  dsimp only
  let χ := spatialPatchCutoff ζ 1 0
  have hχ : Continuous χ := (spatialPatchCutoff_smooth hζ 1 0).continuous
  have hcχ : HasCompactSupport χ := spatialPatchCutoff_compact hζ 1 (by norm_num) 0
  have hpair (a : JetIndex2 1) (θ : Vec 2 → ℝ) (hθ : Continuous θ)
      (hcθ : HasCompactSupport θ) :
      Integrable (fun x => inner ℝ (f x) (φ.toFunction.jet a x) * θ x) volume := by
    simpa only [ContinuousLinearMap.id_apply] using
      periodic_compact_coefficient_pairing_integrable f (φ.toFunction.jet a) hf
        (periodicJetRepresentative_memL2 φ.val a) hfp (periodicJetRepresentative_periodic φ.val a)
        (fun _ => ContinuousLinearMap.id ℝ E) continuous_const 1 (by norm_num)
        (fun _ => ContinuousLinearMap.norm_id_le) θ hθ hcθ
  constructor
  · apply (hpair (valueIndex2 1) χ hχ hcχ).congr
    filter_upwards [spatialPatchLocalization_value_ae hζ 1 (by norm_num) 0 φ] with x hx
    rw [hx, inner_smul_right]
    ring
  · intro k
    let dχ := fun x => fderiv ℝ χ x (basisVec k)
    have hdχ : Continuous dχ :=
      (((spatialPatchCutoff_smooth hζ 1 0).fderiv_right (m := (0 : ℕ)) (by simp)).continuous.clm_apply
        continuous_const)
    have hcdχ : HasCompactSupport dχ := hcχ.fderiv_apply (𝕜 := ℝ) (basisVec k)
    apply ((hpair (valueIndex2 1) dχ hdχ hcdχ).add
      (hpair ⟨⟨1, by decide⟩, fun _ => k⟩ χ hχ hcχ)).congr
    filter_upwards [spatialPatchLocalization_gradient_ae hζ 1 (by norm_num) 0 φ k] with x hx
    rw [hx, inner_add_right, inner_smul_right, inner_smul_right]
    dsimp only [χ, dχ, Pi.add_apply]
    ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Strong convergence of the native value and gradient readouts implies strong H1 convergence. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_tendsto_of_readouts {ι : Type*} {l : Filter ι}
    (u : ι → PlaneHk univ 1 E) (z : PlaneHk univ 1 E)
    (hv : Tendsto (fun i => planeHkValueOperator 1 (u i)) l (𝓝 (planeHkValueOperator 1 z)))
    (hg : Tendsto (fun i => planeH1GradientOperator (u i)) l (𝓝 (planeH1GradientOperator z))) :
    Tendsto u l (𝓝 z) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := (hv.sub (tendsto_const_nhds (x := planeHkValueOperator 1 z))).norm.add
    (hg.sub (tendsto_const_nhds (x := planeH1GradientOperator z))).norm
  simp only [sub_self, norm_zero, add_zero] at hlim
  apply squeeze_zero (fun i => norm_nonneg (u i - z)) _ hlim
  intro i
  have hb := planeH1_norm_le_value_add_gradient (u i - z)
  simpa only [map_sub] using hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Translation followed by restriction is an actual contraction on plane L2. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def restrictPlaneLpCLM (U : Set (Vec 2)) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume.restrict U) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_le_self (μ := (volume : Measure (Vec 2))) (s := U))

theorem restrictPlaneLpCLM_ae (U : Set (Vec 2)) (f : Lp E 2 (volume : Measure (Vec 2))) :
    restrictPlaneLpCLM U f =ᵐ[volume.restrict U] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

def translatedPlaneLpCLM (U : Set (Vec 2)) (z : Vec 2) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume.restrict U) :=
  (restrictPlaneLpCLM U).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (fun x : Vec 2 => x + z)
      (measurePreserving_add_right volume z)).toContinuousLinearMap

theorem translatedPlaneLpCLM_ae (U : Set (Vec 2)) (z : Vec 2)
    (f : Lp E 2 (volume : Measure (Vec 2))) :
    translatedPlaneLpCLM U z f =ᵐ[volume.restrict U] fun x => f (x + z) := by
  have ht := (Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume z)).restrict (s := U)
  exact (restrictPlaneLpCLM_ae U _).trans ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every localized torus test jet vanishes outside its actual compact patch. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem spatialPatchLocalization_jet_support_ae {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → ℤ) (K : ℕ) (φ : TorusHk K E)
    (a : JetIndex2 K) :
    ∀ᵐ x ∂volume, x ∉ tsupport (spatialPatchCutoff ζ N j) →
      (spatialPatchLocalization hζ N hN j K φ).toFunction.jet a x = 0 := by
  filter_upwards [localizeTorusCarrier_jet_ae φ (spatialPatchCoefficient ζ N j)
    (spatialPatchCoefficient_smooth hζ N j K) (spatialPatchCoefficient_compact hζ N hN j) a]
    with x hx
  intro hn
  change (localizeTorusCarrier φ (spatialPatchCoefficient ζ N j)
    (spatialPatchCoefficient_smooth hζ N j K)
    (spatialPatchCoefficient_compact hζ N hN j)).toFunction.jet a x = 0
  rw [hx]
  apply multiplicationRawJet_zero_of_not_tsupport
  intro hc
  exact hn ((tsupport_smul_subset_left _ (fun _ => ContinuousLinearMap.id ℝ E)) hc)

theorem unitPatchLocalization_jet_ball_support_ae {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (K : ℕ) (φ : TorusHk K E) (a : JetIndex2 K) :
    ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Vec 2) 2 →
      (spatialPatchLocalization hζ 1 (by decide) 0 K φ).toFunction.jet a x = 0 := by
  filter_upwards [spatialPatchLocalization_jet_support_ae hζ 1 (by decide) 0 K φ a]
    with x hx
  intro hn
  apply hx
  intro hs
  have hb : ‖x‖ ≤ (2 / 3 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    simpa using spatialPatchCutoff_tsupport_coordinate hζ 1 0 x hs i
  have hlt : (2 / 3 : ℝ) < 2 := by norm_num
  exact hn (Metric.mem_ball.mpr (by simpa [dist_zero_right] using hb.trans_lt hlt))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Filter
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! The unit lattice partition is a fixed finite sum on a neighborhood of every point. -/

theorem integer_close_mem_floor_window_one (y : ℝ) (k : ℤ) (hk : |y - k| < 1) :
    k ∈ Finset.Icc (⌊y⌋ - 1) (⌊y⌋ + 1) := by
  have hlo := Int.floor_le y
  have hhi := Int.lt_floor_add_one y
  have hab := abs_lt.mp hk
  have hkr : (⌊y⌋ : ℝ) - 1 ≤ k := by linarith
  have hki : ⌊y⌋ - 1 ≤ k := by exact_mod_cast hkr
  have hur : (k : ℝ) < (⌊y⌋ : ℝ) + 2 := by linarith
  have hui : k < ⌊y⌋ + 2 := by exact_mod_cast hur
  exact Finset.mem_Icc.mpr ⟨hki, by omega⟩

theorem unitPatch_live_index_near {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (x y : Vec 2) (hy : y ∈ Metric.ball x (1 / 6)) (k : Fin 2 → ℤ)
    (hk : spatialPatchCutoff ζ 1 k y ≠ 0) : k ∈ spatialPatchOverlapIndices x := by
  have hclose (i : Fin 2) : |x i - k i| < 1 := by
    have hs := spatialPatchCutoff_coordinate_support hζ 1 k y hk i
    simp only [Nat.cast_one, one_mul] at hs
    have hdist : |x i - y i| < 1 / 6 := by
      have hnorm := norm_le_pi_norm (x - y) i
      have hb : ‖x - y‖ < 1 / 6 := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
      have hcoord : |x i - y i| ≤ ‖x - y‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using hnorm
      exact hcoord.trans_lt hb
    have ha := abs_add_le (x i - y i) (y i - k i)
    have he : x i - y i + (y i - k i) = x i - k i := by ring
    rw [he] at ha
    linarith
  apply Finset.mem_map.mpr
  refine ⟨(k 0, k 1), Finset.mem_product.mpr
    ⟨integer_close_mem_floor_window_one _ _ (hclose 0),
      integer_close_mem_floor_window_one _ _ (hclose 1)⟩, ?_⟩
  exact (finTwoArrowEquiv ℤ).symm_apply_apply k

theorem unitPatch_eventually_zero_outside {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (x : Vec 2) :
    ∀ᶠ y in 𝓝 x, ∀ k, k ∉ spatialPatchOverlapIndices x → spatialPatchCutoff ζ 1 k y = 0 := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 6)] with y hy
  intro k hk
  by_contra hn
  exact hk (unitPatch_live_index_near hζ x y hy k hn)

theorem unitPatch_local_partition {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (x : Vec 2) :
    ∀ᶠ y in 𝓝 x, (∑ k ∈ spatialPatchOverlapIndices x, spatialPatchCutoff ζ 1 k y) = 1 := by
  filter_upwards [unitPatch_eventually_zero_outside hζ x] with y hy
  rw [← spatialPatchCutoff_partition hζ 1 y]
  exact (tsum_eq_sum (s := spatialPatchOverlapIndices x) hy).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual cell metrics are measurable jointly and on every fixed spatial slice. -/

theorem cellMetric_joint_measurable (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2) :
    Measurable (fun p : ℝ × Vec 2 => ocCellMetric α q Λ m φ hφ l ν yc p.1 p.2) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (ocCellMetric_joint_contDiff α q Λ m hφ l ν yc i j).continuous.measurable

theorem cellMetric_time_slice_measurable (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc X : Vec 2) (i j : Fin 2) :
    Measurable (fun t => ocCellMetric α q Λ m φ hφ l ν yc t X i j) := by
  have hc := (ocCellMetric_joint_contDiff α q Λ m hφ l ν yc i j).comp
    (contDiff_id.prodMk (contDiff_const (c := X)))
  exact hc.continuous.measurable

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Compact support of the actual native jets permits every continuous weight. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeHk_weighted_jets_memLp_of_compact_support
    (U : PlaneHk Set.univ K E) (S : Set (Vec 2)) (hS : IsCompact S)
    (hs : ∀ a : JetIndex2 K, ∀ᵐ x ∂volume, x ∉ S → U.toFunction.jet a x = 0)
    (q : Vec 2 → ℝ) (hq : Continuous q) :
    ∀ a : JetIndex2 K, MemLp (fun x => q x • U.toFunction.jet a x) 2 volume := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hq.continuousOn
  intro a
  have hu : MemLp (U.toFunction.jet a) 2 volume := by
    simpa only [Measure.restrict_univ] using U.toFunction.memL2 a
  apply hu.of_le_mul (hq.aestronglyMeasurable.smul hu.aestronglyMeasurable) (c := max C 0)
  filter_upwards [hs a] with x hx
  change ‖q x • U.toFunction.jet a x‖ ≤ max C 0 * ‖U.toFunction.jet a x‖
  by_cases hm : x ∈ S
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right ((hC x hm).trans (le_max_left C 0)) (norm_nonneg _)
  · simp only [hx hm, smul_zero, norm_zero, mul_zero, le_refl]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The actual centre-frozen chart metric is measurable in time before any window restriction. -/

theorem frozenCellMetric_measurable (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2) :
    Measurable (fun t => ocCellMetric α q Λ m φ hφ l ν yc t 0) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hc := (ocCellMetric_frozen_joint_contDiff α q Λ m hφ l ν yc i j).comp
    (contDiff_id.prodMk (contDiff_const (c := (0 : Vec 2))))
  exact hc.continuous.measurable

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Compactly supported weak tests turn global plane pairings into actual local Hilbert pairings. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem plane_pairing_eq_local_inner (U : Set (Vec 2))
    (f g : Lp E 2 (volume : Measure (Vec 2)))
    (hg : ∀ᵐ x ∂volume, x ∉ U → g x = 0) :
    (∫ x, inner ℝ (f x) (g x)) =
      inner ℝ (restrictPlaneLpCLM U f) (restrictPlaneLpCLM U g) := by
  have he : (∫ x in U, inner ℝ (f x) (g x)) = ∫ x, inner ℝ (f x) (g x) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hg] with x hx hxu
    rw [hx hxu, inner_zero_right]
  rw [← he, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictPlaneLpCLM_ae U f, restrictPlaneLpCLM_ae U g] with x hf hg'
  rw [hf, hg']

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Literal H1 value and gradient readouts satisfy the weak derivative identities. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_value_gradient_weakPartial (u : PlaneHk univ 1 E) (i : Fin 2) (e : E) :
    HasWeakPartialDerivOn univ i
      (fun x => inner ℝ e (planeHkValueOperator 1 u x))
      (fun x => inner ℝ e (planeH1GradientOperator u i x)) := by
  have hw := u.toFunction.hasWeakJet ⟨0, by omega⟩ Fin.elim0 i e
  change HasWeakPartialDerivOn univ i
    (fun x => inner ℝ e (u.val (valueIndex2 1) x))
    (fun x => inner ℝ e (u.val ⟨⟨1, by omega⟩, fun _ => i⟩ x)) at hw
  apply hasWeakPartialDerivOn_congr_ae _ _ hw
  · rw [planeHkValueOperator_apply]
    apply ae_restrict_of_ae
    filter_upwards [univToPlane_ae (u.val (valueIndex2 1))] with x hx
    exact congrArg (fun y => inner ℝ e y) hx.symm
  · rw [planeH1GradientOperator_apply]
    apply ae_restrict_of_ae
    filter_upwards [univToPlane_ae (u.val ⟨⟨1, by omega⟩, fun _ => i⟩)] with x hx
    exact congrArg (fun y => inner ℝ e y) hx.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Each translated localized jet is a continuous linear readout of the plane carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def planeImageJetCLM (U : Set (Vec 2)) (z : Vec 2) (a : JetIndex2 K) :
    PlaneHk Set.univ K E →L[ℝ] Lp E 2 (volume.restrict U) :=
  (translatedPlaneLpCLM U z).comp (planeJetReadoutOperator K a)

theorem planeImageJetCLM_ae (U : Set (Vec 2)) (z : Vec 2) (a : JetIndex2 K)
    (f : PlaneHk Set.univ K E) :
    planeImageJetCLM U z a f =ᵐ[volume.restrict U] fun x => f.toFunction.jet a (x + z) := by
  have ht := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae_eq_comp
    (univToPlane_ae (f.val a))
  have he := translatedPlaneLpCLM_ae U z (planeJetReadoutOperator K a f)
  rw [planeJetReadoutOperator_apply] at he
  exact he.trans (ht.restrict (s := U))

theorem planeImageJetCLM_continuousOn {X : Type*} [TopologicalSpace X]
    (U : Set (Vec 2)) (z : Vec 2) (a : JetIndex2 K)
    (f : X → PlaneHk Set.univ K E) (s : Set X) (hf : ContinuousOn f s) :
    ContinuousOn (fun t => planeImageJetCLM U z a (f t)) s :=
  (planeImageJetCLM U z a).continuous.comp_continuousOn hf

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Filter
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Cutoff derivative terms cancel in the complete integer-image weak equation. -/

theorem unitPatch_derivative_zero_outside {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (x : Vec 2) (k : Fin 2 → ℤ) (hk : k ∉ spatialPatchOverlapIndices x) :
    fderiv ℝ (spatialPatchCutoff ζ 1 k) x = 0 := by
  have he : spatialPatchCutoff ζ 1 k =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    (unitPatch_eventually_zero_outside hζ x).mono (fun _ hy => hy k hk)
  simpa only [fderiv_fun_const, Pi.zero_apply] using he.fderiv_eq (𝕜 := ℝ)

theorem unitPatch_finite_derivative_partition {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (x : Vec 2) :
    (∑ k ∈ spatialPatchOverlapIndices x, fderiv ℝ (spatialPatchCutoff ζ 1 k) x) = 0 := by
  have he : (fun y => ∑ k ∈ spatialPatchOverlapIndices x, spatialPatchCutoff ζ 1 k y)
      =ᶠ[𝓝 x] fun _ => (1 : ℝ) := unitPatch_local_partition hζ x
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_sum (fun k _ =>
    ((spatialPatchCutoff_smooth hζ 1 k).differentiable (by simp)) x), fderiv_fun_const] at hd
  exact hd

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! A smooth representative of a genuine native H1 value has its literal classical gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_smooth_value_gradient_ae (u : PlaneHk univ 1 E) (f : Vec 2 → E)
    (hf : ContDiff ℝ 1 f)
    (hval : (planeHkValueOperator 1 u : Vec 2 → E) =ᵐ[volume] f) (i : Fin 2) :
    (planeH1GradientOperator u i : Vec 2 → E) =ᵐ[volume]
      fun x => fderiv ℝ f x (basisVec i) := by
  let b := stdOrthonormalBasis ℝ E
  have hp : ∀ k, (fun x => inner ℝ (b k) (planeH1GradientOperator u i x)) =ᵐ[volume]
      fun x => inner ℝ (b k) (fderiv ℝ f x (basisVec i)) := by
    intro k
    let q := fun x => inner ℝ (b k) (f x)
    have hq : ContDiff ℝ 1 q := (innerSL ℝ (b k)).contDiff.comp hf
    have he (x : Vec 2) : fderiv ℝ q x (basisVec i) =
        inner ℝ (b k) (fderiv ℝ f x (basisVec i)) := by
      have hd := (innerSL ℝ (b k)).hasFDerivAt.comp x
        (hf.differentiable (by norm_num) x).hasFDerivAt
      exact congrArg (fun A : Vec 2 →L[ℝ] ℝ => A (basisVec i)) hd.fderiv
    have hw : HasWeakPartialDerivOn univ i q
        (fun x => inner ℝ (b k) (planeH1GradientOperator u i x)) := by
      apply hasWeakPartialDerivOn_congr_ae _ (Filter.Eventually.of_forall fun _ => rfl)
        (planeH1_value_gradient_weakPartial u i (b k))
      simpa only [Measure.restrict_univ, Function.comp_def, q] using hval.fun_comp (inner ℝ (b k))
    have hg := (innerSL ℝ (b k)).comp_memLp' (Lp.memLp (planeH1GradientOperator u i))
    have hc : Continuous (fun x => fderiv ℝ q x (basisVec i)) :=
      (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hu := HasWeakPartialDerivOn.ae_eq isOpen_univ
      (locallyIntegrableOn_univ.mpr (hg.locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_univ.mpr hc.locallyIntegrable) hw
      (HasWeakPartialDerivOn.of_contDiff hq)
    simpa only [Measure.restrict_univ, Function.comp_def, innerSL_apply_apply, he] using hu
  filter_upwards [ae_all_iff.mpr hp] with x hx
  apply b.repr.injective
  ext k
  simpa only [b.repr_apply_apply] using hx k

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Exact cancellation of the cutoff derivative flux in integer-image weak tests. -/

theorem unitPatch_directional_derivative_partition {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (x v : Vec 2) :
    (∑' k : Fin 2 → ℤ, fderiv ℝ (spatialPatchCutoff ζ 1 k) x v) = 0 := by
  rw [tsum_eq_sum (s := spatialPatchOverlapIndices x) (fun k hk => by
    rw [unitPatch_derivative_zero_outside hζ x k hk, zero_apply])]
  have he := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L v)
    (unitPatch_finite_derivative_partition hζ x)
  simpa only [sum_apply, zero_apply] using he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Qualitative finite drift budgets for existence; these do not assert uniform model estimates. -/

local instance admissibleStreamDriftBudgetsBoundedSMul : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ] ℝ) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := (PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ] ℝ)

theorem streamSeq_current_admissible {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    IsAdmissibleStream (Φ m) := by
  obtain ⟨h, _⟩ := hΦ.2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  simpa only [Nat.add_sub_cancel] using h

theorem admissible_stream_spatial_jet_bound (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖iteratedFDeriv ℝ j (streamVel φ t) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := Infra.Classical.streamVel_global_derivative_bound φ hφ j
  refine ⟨C, hC, ?_⟩
  intro t x
  let L := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  let f : ℝ × Vec 2 → Vec 2 := fun p => streamVel φ (p.1 + t) p.2
  have hf : ContDiff ℝ (j : ℕ) f := by
    have hfull : ContDiff ℝ (j : ℕ) (Function.uncurry (streamVel φ)) :=
      (Infra.Classical.streamVel_smoothPeriodic φ hφ).smooth.of_le (by simp)
    convert hfull.comp (contDiff_id.add (contDiff_const (c := (t, (0 : Vec 2))))) using 1
    funext p
    simp [f, Function.uncurry]
  have he : streamVel φ t = f ∘ L := by
    funext y
    simp [f, L]
  rw [he, L.iteratedFDeriv_comp_right hf x le_rfl]
  have hn : (∏ _ : Fin j, ‖L‖) ≤ 1 := by
    apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L)
      (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ (Vec 2))).trans_eq
    simp
  have hnorm := (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j f (L x)) (fun _ => L)).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
  rw [mul_one] at hnorm
  have hshift : f = fun p => Function.uncurry (streamVel φ) (p + (t, 0)) := by
    funext p
    simp [f, Function.uncurry]
  rw [hshift, iteratedFDeriv_comp_add_right] at hnorm ⊢
  exact hnorm.trans (hb (L x + (t, 0)))

theorem admissible_stream_coefficient_array_budget (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (K : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, j ≤ K → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) j x‖ ≤ M := by
  classical
  choose C hC hb using admissible_stream_spatial_jet_bound φ hφ
  let M := ∑ j ∈ Finset.range (K + 1),
    (Fintype.card (DerivativeWord2 j) : ℝ) * ‖Weighted.driftCoefficientEmbedding‖ * C j
  have hm j : 0 ≤ (Fintype.card (DerivativeWord2 j) : ℝ) *
      ‖Weighted.driftCoefficientEmbedding‖ * C j :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (ContinuousLinearMap.opNorm_nonneg Weighted.driftCoefficientEmbedding)) (hC j)
  refine ⟨M, Finset.sum_nonneg (fun j _ => hm j), ?_⟩
  intro j hj t x
  have hv : ContDiff ℝ (j : ℕ) (streamVel φ t) :=
    ((Infra.Classical.streamVel_smoothPeriodic φ hφ).smooth.of_le (show (j : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by simp)).comp
      (contDiff_const.prodMk contDiff_id)
  exact (Weighted.driftCoefficient_array_norm_le_iterated _ j hv x).trans
    ((mul_le_mul_of_nonneg_left (hb j t x) (by positivity)).trans
      (Finset.single_le_sum (fun j _ => hm j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Literal source word-array fluxes expand into the coefficient entries used by image weak testing. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem couplingEntryCoefficient_expansion {m : ℕ} (i i' : ι)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (u : PiLp 2 (fun _ : DerivativeWord2 m => h i'))
    (x : Vec 2) (k : Fin 2) :
    A x u k = ∑ w : DerivativeWord2 m, couplingEntryCoefficient i i' A w k x (u w) := by
  have he : u = ∑ w : DerivativeWord2 m, PiLp.single 2 w (u w) := by
    apply PiLp.ext
    intro w
    simp
  calc
    _ = A x (∑ w : DerivativeWord2 m, PiLp.single 2 w (u w)) k := congrArg (fun v => A x v k) he
    _ = ∑ w : DerivativeWord2 m, A x (PiLp.single 2 w (u w)) k := by
      rw [map_sum]
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
    _ = _ := rfl

theorem couplingEntryCoefficient_inner_expansion {m : ℕ} (i i' : ι)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (u : PiLp 2 (fun _ : DerivativeWord2 m => h i'))
    (x : Vec 2) (k : Fin 2) (z : h i) :
    inner ℝ (A x u k) z = ∑ w : DerivativeWord2 m,
      inner ℝ (couplingEntryCoefficient i i' A w k x (u w)) z := by
  rw [couplingEntryCoefficient_expansion, sum_inner]
end

/-! Measurability is inherited by every source word and output-direction coefficient entry. -/

section
variable {ι X : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [MeasurableSpace X]

theorem couplingEntryCoefficient_joint_measurable {m : ℕ} (i i' : ι)
    (A : X → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : Measurable (Function.uncurry A)) (w : DerivativeWord2 m) (k : Fin 2) :
    Measurable (fun z : X × Vec 2 => couplingEntryCoefficient i i' (A z.1) w k z.2) := by
  have hc : Continuous (fun T : PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i) =>
        (PiLp.proj 2 (fun _ : Fin 2 => h i) k).comp
          (T.comp (tensorEntryCLM (E := h i') w))) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  exact hc.measurable.comp hA
end

/-! Actual bounded word-array coefficients preserve the spatial L2 flux at every time. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem couplingFlux_component_memLp {r : ℕ} (i i' : ι) (U : Set (Vec 2))
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (hc : Continuous A)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖A x‖ ≤ M)
    (D : DerivativeWord2 r → Vec 2 → h i')
    (hD : ∀ w, MemLp (D w) 2 (volume.restrict U)) (k : Fin 2) :
    MemLp (fun x => A x (WithLp.toLp 2 (fun w => D w x)) k) 2 (volume.restrict U) := by
  have hi (w : DerivativeWord2 r) : MemLp
      (fun x => couplingEntryCoefficient i i' A w k x (D w x)) 2 (volume.restrict U) :=
    memLp_operator_mul (couplingEntryCoefficient_continuous i i' A hc w k) (hD w) hM
      (fun x => (couplingEntryCoefficient_norm_le i i' A w k x).trans (hb x))
  have he : (fun x => A x (WithLp.toLp 2 (fun w => D w x)) k) =
      fun x => ∑ w : DerivativeWord2 r, couplingEntryCoefficient i i' A w k x (D w x) := by
    funext x
    exact couplingEntryCoefficient_expansion i i' A (WithLp.toLp 2 (fun w => D w x)) x k
  rw [he]
  exact memLp_finsetSum Finset.univ (fun w _ => hi w)
end

/-! Integrable coefficient entries assemble into the literal source word-array flux pairing. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem couplingFlux_pairing_integral {r : ℕ} (i i' : ι) (μ : Measure (Vec 2))
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (D : DerivativeWord2 r → Vec 2 → h i')
    (φ : Vec 2 → h i) (k : Fin 2)
    (hi : ∀ w, Integrable (fun x => inner ℝ (couplingEntryCoefficient i i' A w k x (D w x)) (φ x)) μ) :
    Integrable (fun x => inner ℝ (A x (WithLp.toLp 2 (fun w => D w x)) k) (φ x)) μ ∧
      (∫ x, inner ℝ (A x (WithLp.toLp 2 (fun w => D w x)) k) (φ x) ∂μ) =
        ∑ w : DerivativeWord2 r, ∫ x, inner ℝ (couplingEntryCoefficient i i' A w k x (D w x)) (φ x) ∂μ := by
  have he : (fun x => inner ℝ (A x (WithLp.toLp 2 (fun w => D w x)) k) (φ x)) =
      fun x => ∑ w : DerivativeWord2 r,
        inner ℝ (couplingEntryCoefficient i i' A w k x (D w x)) (φ x) := by
    funext x
    exact couplingEntryCoefficient_inner_expansion i i' A (WithLp.toLp 2 (fun w => D w x)) x k (φ x)
  rw [he]
  exact ⟨integrable_finsetSum Finset.univ (fun w _ => hi w),
    integral_finsetSum Finset.univ (fun w _ => hi w)⟩
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Each actual drift pairing is a bounded scalar coefficient entry for image transfer. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace X]

def driftPairingCoefficient (v : Vec 2) (k : Fin 2) : E →L[ℝ] E :=
  v k • ContinuousLinearMap.id ℝ E

omit [MeasurableSpace X] in
theorem driftPairingCoefficient_norm_le (v : Vec 2) (k : Fin 2) :
    ‖driftPairingCoefficient (E := E) v k‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖v k‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul_le _ _
    _ ≤ ‖v k‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ ‖v‖ := by simpa only [mul_one] using norm_le_pi_norm v k

omit [MeasurableSpace X] in
theorem driftPairingCoefficient_continuous (v : Vec 2 → Vec 2) (hv : Continuous v) (k : Fin 2) :
    Continuous (fun x => driftPairingCoefficient (E := E) (v x) k) := by
  exact ((continuous_apply k).comp hv).smul continuous_const

theorem driftPairingCoefficient_joint_measurable (v : X → Vec 2 → Vec 2)
    (hv : Measurable (Function.uncurry v)) (k : Fin 2) :
    Measurable (fun p : X × Vec 2 => driftPairingCoefficient (E := E) (v p.1 p.2) k) := by
  exact ((measurable_pi_apply k).comp hv).smul_const (ContinuousLinearMap.id ℝ E)

omit [MeasurableSpace X] in
theorem driftPairingCoefficient_inner (v : Vec 2) (k : Fin 2) (u φ : E) :
    inner ℝ (driftPairingCoefficient v k u) φ = v k * inner ℝ u φ := by
  change inner ℝ (v k • u) φ = _
  exact real_inner_smul_left _ _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The positive profile partition localizes periodic L2 data without enlarging its total energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spatialPatch_multiplier_memLp {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (hp : AVenhance.IsZ2Periodic f) :
    MemLp (fun x => spatialPatchCutoff ζ N k x • f x) 2 volume := by
  simpa only [spatialPatchCoefficient, smul_apply,
    ContinuousLinearMap.id_apply] using periodic_compact_operator_memLp f hf hp
      (spatialPatchCoefficient (E := E) ζ N k)
      (spatialPatchCoefficient_smooth hζ N k 0).continuous
      (spatialPatchCoefficient_compact hζ N hN k)

theorem periodic_patch_l2_integral_budget [MeasurableSpace E] [BorelSpace E]
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N) (f : Vec 2 → E)
    (hfm : Measurable f) (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hp : AVenhance.IsZ2Periodic f) :
    (∑ j : Fin 2 → Fin N, ∫ x,
      ‖spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x • f x‖ ^ 2 ∂volume) ≤
      ∫ x in AVenhance.unitCube, ‖f x‖ ^ 2 ∂volume := by
  have hi (j : Fin 2 → Fin N) :=
    (spatialPatch_multiplier_memLp hζ N hN (fun i => (j i : ℤ)) f hf hp).norm.integrable_sq
  have hb := periodic_patch_integral_budget hζ N hN
    (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) (hfm.norm.pow_const 2).ennreal_ofReal
    (fun n x => by
      change ENNReal.ofReal (‖f (x + AVenhance.latticeShift n)‖ ^ 2) =
        ENNReal.ofReal (‖f x‖ ^ 2)
      rw [hp n x])
  have he (j : Fin 2 → Fin N) (x : Vec 2) :
      ENNReal.ofReal (‖spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x • f x‖ ^ 2) =
      ENNReal.ofReal ((spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x) ^ 2) *
        ENNReal.ofReal (‖f x‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      ENNReal.ofReal_mul (sq_nonneg _)]
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))]
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hi _) (Filter.Eventually.of_forall (fun _ => sq_nonneg _)), he]
  rw [ofReal_integral_eq_lintegral_ofReal hf.norm.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  rwa [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube] at hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! A convolution average acts on the genuine native H1 carrier with exact value and gradient averages. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeH1Average (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) (u : PlaneHk univ 1 E) : PlaneHk univ 1 E :=
  let f := averagingOperator ρ hρ κ hκ (planeHkValueOperator 1 u)
  let G := fun i => averagingOperator ρ hρ κ hκ (planeH1GradientOperator u i)
  planeH1OfWeakGradient (fun x => f x) (fun i x => G i x)
    ((Lp.memLp f).mono_measure Measure.restrict_le_self)
    (fun i => (Lp.memLp (G i)).mono_measure Measure.restrict_le_self)
    (fun i => averagingOperator_hasWeakPartialDeriv
      (fun e => planeH1_value_gradient_weakPartial u i e) ρ hρ hκ)

theorem planeH1Average_value (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) (u : PlaneHk univ 1 E) :
    planeHkValueOperator 1 (planeH1Average ρ hρ κ hκ u) =
      averagingOperator ρ hρ κ hκ (planeHkValueOperator 1 u) := by
  apply Lp.ext
  unfold planeH1Average
  exact planeH1OfWeakGradient_valueOperator_ae _ _ _ _ _

theorem planeH1Average_gradient (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) (u : PlaneHk univ 1 E) (i : Fin 2) :
    planeH1GradientOperator (planeH1Average ρ hρ κ hκ u) i =
      averagingOperator ρ hρ κ hκ (planeH1GradientOperator u i) := by
  apply Lp.ext
  unfold planeH1Average
  exact planeH1OfWeakGradient_gradientOperator_ae _ _ _ _ _ i

end AVRegularity.CycleJointProofs
end
end
