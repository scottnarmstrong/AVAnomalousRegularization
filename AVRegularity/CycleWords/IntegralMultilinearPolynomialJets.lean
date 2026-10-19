-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneFourierDerivativeCriterion
import AVRegularity.Analysis.Convolution.Kernel.PulseAxes
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Weighted.MetricWordCoefficientArrayBound
public import AVRegularity.CycleWords.JointDiagonalChainRule
import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
import AVRegularity.CycleWords.NativeScalarErrorChain

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped SchwartzMap LineDeriv
namespace AVRegularity.CycleWords

/-! Every ordered scalar derivative is moved onto the Schwartz kernel. -/

def schwartzWordKernel (w : List (Fin 2)) (k : 𝓢(Vec 2, ℝ)) : 𝓢(Vec 2, ℝ) :=
  w.foldl (fun k' i => ∂_{basisVec i} k') k

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartzConvolution_foldl (w : List (Fin 2)) (k : 𝓢(Vec 2, ℝ))
    (f : Vec 2 → E) (hf : Integrable f) :
    w.foldl (fun g i => fun x => fderiv ℝ g x (basisVec i)) (schwartzConvolution k f) =
      schwartzConvolution (schwartzWordKernel w k) f := by
  induction w generalizing k with
  | nil => rfl
  | cons i w ih =>
    simp only [List.foldl_cons, schwartzWordKernel]
    have he : (fun x => fderiv ℝ (schwartzConvolution k f) x (basisVec i)) =
        schwartzConvolution (∂_{basisVec i} k) f :=
      funext (fun x => schwartzConvolution_directional_deriv k f hf x (basisVec i))
    rw [he]
    exact ih (∂_{basisVec i} k)

theorem schwartzConvolution_orderedDerivative {n : ℕ} (w : DerivativeWord2 n)
    (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E) (hf : Integrable f) :
    orderedDerivative w (schwartzConvolution k f) =
      schwartzConvolution (schwartzWordKernel (List.ofFn w) k) f :=
  schwartzConvolution_foldl (List.ofFn w) k f hf

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The L2 norm of a classical smooth word is exactly its native stored jet norm. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smooth_orderedDerivative_Lp_norm {K j : ℕ} (hj : j ≤ K)
    (U : PlaneHk Set.univ K E) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (w : DerivativeWord2 j) (hmem : MemLp (orderedDerivative w f) 2 volume) :
    ‖hmem.toLp (orderedDerivative w f)‖ = ‖U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩‖ := by
  have he : planeJetOrder U j w =
      (U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ : Vec 2 → E) := by
    rw [planeJetOrder_eq_stored hj]
    rfl
  have ha := planeHk_smooth_jet_readout U hf hu j hj w
  rw [he] at ha
  rw [Lp.norm_toLp, Lp.norm_def]
  simp only [Measure.restrict_univ]
  rw [eLpNorm_congr_ae ha]
end

/-! Weighted classical jets of a smooth value representative are the actual native weighted jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_smooth_jet_ae {K j : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (q : Vec 2 → ℝ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    (fun x => q x • U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x) =ᵐ[volume]
      (fun x => q x • orderedDerivative w f x) := by
  have hh := planeHk_smooth_jet_readout U hf hu j hj w
  rw [planeJetOrder_eq_stored hj] at hh
  exact hh.mono (fun x hx => congrArg (fun e : E => q x • e) hx)

theorem weighted_smooth_jet_memLp {K j : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (q : Vec 2 → ℝ) (hj : j ≤ K) (w : DerivativeWord2 j)
    (hw : MemLp (fun x => q x • U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x)
      2 volume) : MemLp (fun x => q x • orderedDerivative w f x) 2 volume :=
  hw.ae_eq (weighted_smooth_jet_ae U hf hu q hj w)

theorem weighted_smooth_jet_Lp_norm {K j : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (q : Vec 2 → ℝ) (hj : j ≤ K) (w : DerivativeWord2 j)
    (hw : MemLp (fun x => q x • U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x)
      2 volume) (hc : MemLp (fun x => q x • orderedDerivative w f x) 2 volume) :
    ‖hc.toLp (fun x => q x • orderedDerivative w f x)‖ =
      ‖hw.toLp (fun x => q x • U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x)‖ := by
  rw [MemLp.toLp_congr hc hw (weighted_smooth_jet_ae U hf hu q hj w).symm]
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory LineDeriv AVRegularity.CoupledEnergyPlane.Fourier
open scoped SchwartzMap ComplexConjugate
namespace AVRegularity.CycleWords

/-! Complex plane distributional derivatives give every real Hilbert weak test. -/

theorem planeDistributionDerivative_smul
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) =
      ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) (c : ℂ) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (c • f) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) =
      ((coordinateL2Equiv (c • g) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) := by
  apply planeFourier_distribution_derivative_of_ae
  rw [map_smul, map_smul]
  filter_upwards [planeFourier_distribution_derivative_ae f g i hfg,
    Lp.coeFn_smul c (fourierL2 f), Lp.coeFn_smul c (fourierL2 g)] with ξ hξ hf hg
  rw [hf, hg]
  change c * fourierL2 g ξ = (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * (c * fourierL2 f ξ)
  rw [hξ]
  ring

theorem planeDistributionDerivative_real_inner
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) =
      ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) (e : ℂ) :
    HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (f x)) (fun x => inner ℝ e (g x)) := by
  have hw := hasWeakPartialDerivOn_re_of_distribution (conj e • f) (conj e • g) i
    (planeDistributionDerivative_smul f g i hfg (conj e))
  apply AVRegularity.Sobolev.hasWeakPartialDerivOn_congr_ae _ _ hw
  · rw [Measure.restrict_univ]
    filter_upwards [Lp.coeFn_smul (conj e) f] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    rfl
  · rw [Measure.restrict_univ]
    filter_upwards [Lp.coeFn_smul (conj e) g] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The literal scalar cutoff is a bounded operator on genuine plane L2 data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem seamCutoffKernel_integrable (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) : Integrable (cutoffKernel m) := by
  rw [← seamRealCutoffSchwartz_eq m R hm hs]
  exact (seamRealCutoffSchwartz m R hm hs).integrable

def seamCutoffL2 (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) :
    MeasureTheory.Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] MeasureTheory.Lp E 2 (volume : Measure (Vec 2)) :=
  planeAveragingOperator 1 (ContinuousLinearMap.id ℝ (Vec 2)) (cutoffKernel m)
    (seamCutoffKernel_integrable m R hm hs)

theorem seamCutoffL2_ae (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) (f : MeasureTheory.Lp E 2 (volume : Measure (Vec 2))) :
    seamCutoffL2 m R hm hs f =ᵐ[volume] fourierCutoff m f := by
  have hh := averagingOperator_ae (displacement 1 (ContinuousLinearMap.id ℝ (Vec 2)))
    (continuous_displacement _ _) (seamCutoffKernel_integrable m R hm hs) f
  have he : pointwiseAverage (displacement 1 (ContinuousLinearMap.id ℝ (Vec 2))) (cutoffKernel m) f =
      fourierCutoff m f := by
    funext y
    unfold pointwiseAverage fourierCutoff
    simp only [displacement_apply, ContinuousLinearMap.id_apply, one_smul]
  rw [he] at hh
  exact hh

theorem seamFourierCutoff_memLp (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) (f : MeasureTheory.Lp E 2 (volume : Measure (Vec 2))) :
    MemLp (fourierCutoff m f) 2 volume :=
  MemLp.ae_eq (seamCutoffL2_ae m R hm hs f) (MeasureTheory.Lp.memLp (seamCutoffL2 m R hm hs f))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory LineDeriv AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped SchwartzMap
namespace AVRegularity.CycleWords

/-! Genuine complex plane H1 carriers from L2 distributional derivative data. -/

def planeComplexFirstJet (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2))) : RawJet2 1 ℂ := fun a x =>
  if h : a.1.val = 0 then f x else g (a.2 ⟨0, by omega⟩) x

theorem planeComplexFirstJet_lower (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2)))
    (j : Fin 1) (w : DerivativeWord2 j.val) :
    planeComplexFirstJet f g (lowerIndex2 j w) = f := by
  funext x
  simp [planeComplexFirstJet, lowerIndex2, lowerIndex]

theorem planeComplexFirstJet_next (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2)))
    (j : Fin 1) (w : DerivativeWord2 j.val) (i : Fin 2) :
    planeComplexFirstJet f g (nextIndex2 j w i) = g i := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  funext x
  simp [planeComplexFirstJet, nextIndex2, nextIndex, Fin.snoc]

theorem planeComplexFirstJet_memL2 (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2))) :
    JetMemL2On Set.univ (planeComplexFirstJet f g) := by
  intro a
  unfold planeComplexFirstJet
  split
  · exact (Lp.memLp f).mono_measure Measure.restrict_le_self
  · exact (Lp.memLp (g _)).mono_measure Measure.restrict_le_self

def planeComplexH1OfDistribution (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) = ((coordinateL2Equiv (g i) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) :
    PlaneHk Set.univ 1 ℂ :=
  PlaneHkFunction.toHk
    { jet := planeComplexFirstJet f g
      memL2 := planeComplexFirstJet_memL2 f g
      hasWeakJet := by
        intro j w i e
        rw [planeComplexFirstJet_lower, planeComplexFirstJet_next]
        exact planeDistributionDerivative_real_inner f (g i) i (hfg i) e }

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Every classical derivative of a smooth Sobolev pullback lies in the actual plane L2 space. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smooth_planeHk_orderedDerivative_memLp {K : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    MemLp (orderedDerivative w f) 2 volume :=
  MemLp.ae_eq (planeHk_smooth_jet_readout U hf hu j hj w) (planeJetOrder_memLp hj U w)

theorem smooth_planeHk_pullback_word_memLp {K : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    MemLp (orderedDerivative w (f ∘ X)) 2 volume := by
  have hm : MemLp (fun z => ∑ c : OrderedFinpartition n,
      (∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
        ∏ i : Fin c.length, B (c.partSize i)) 2 volume := by
    apply memLp_finsetSum
    intro c _
    apply MemLp.mul_const
    apply memLp_finsetSum
    intro v _
    exact ((smooth_planeHk_orderedDerivative_memLp U hf hu c.length
      (c.length_le.trans hn) v).comp_measurePreserving hμ).norm
  apply hm.mono' (ChartTransport.continuous_orderedDerivative w
    ((hf.comp hX).of_le (by simp))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => smooth_composition_word_norm_bound hf hX B n
    (fun j hj0 hj => hb j hj0 (hj.trans hn)) w z)
end

/-! A smooth Sobolev representative pulled through a genuine renewal remains in the native weak graph. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def smoothPlanePullback {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j) :
    PlaneHk Set.univ K E :=
  smoothPlaneHk K (f ∘ X) (hf.comp hX) (fun a =>
    smooth_planeHk_pullback_word_memLp U hf hu hX hμ B hb a.1.val
      (Nat.le_of_lt_succ a.1.isLt) a.2)

theorem smoothPlanePullback_jet_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (smoothPlanePullback U f hf hu X hX hμ B hb) j w =ᵐ[volume]
      orderedDerivative w (f ∘ X) :=
  smoothPlaneHk_jet_ae K (f ∘ X) (hf.comp hX) _ j hj w

theorem smoothPlanePullback_value_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j) :
    planeValue (smoothPlanePullback U f hf hu X hX hμ B hb) =ᵐ[volume] f ∘ X := by
  have hh := smoothPlanePullback_jet_ae U f hf hu X hX hμ B hb 0 (Nat.zero_le K) Fin.elim0
  rw [orderedDerivative_zero] at hh
  exact hh
end

/-! The sharp finite chain rule budget, read entirely through the native weak-jet accessors. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smoothPlanePullback_word_budget_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ∀ᵐ z ∂volume, ‖planeJetOrder (smoothPlanePullback U f hf hu X hX hμ B hb) n w z‖ ≤
      ∑ a : (Σ c : OrderedFinpartition n, DerivativeWord2 c.length),
        (∏ i : Fin a.1.length, B (a.1.partSize i)) *
          ‖planeJetOrder U a.1.length a.2 (X z)‖ := by
  have hi : ∀ᵐ z ∂volume, ∀ a : (Σ c : OrderedFinpartition n, DerivativeWord2 c.length),
      planeJetOrder U a.1.length a.2 (X z) = orderedDerivative a.2 f (X z) := by
    apply ae_all_iff.mpr
    intro a
    exact hμ.quasiMeasurePreserving.ae_eq_comp
      (planeHk_smooth_jet_readout U hf hu a.1.length (a.1.length_le.trans hn) a.2)
  filter_upwards [hi, smoothPlanePullback_jet_ae U f hf hu X hX hμ B hb n hn w] with z hi ho
  rw [ho]
  have hh := smooth_composition_word_norm_bound hf hX B n
    (fun j hj0 hj => hb j hj0 (hj.trans hn)) w z
  simpa only [hi, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul, mul_comm] using hh
end

/-! A finite component norm budget for the actual smooth Sobolev pullback. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smoothPlanePullback_component_norm_le {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ‖(smoothPlanePullback U f hf hu X hX hμ B hb).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) *
        ∑ v : DerivativeWord2 c.length,
          ‖U.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖ := by
  let J := Σ c : OrderedFinpartition n, DerivativeWord2 c.length
  let g (a : J) : Vec 2 → E := fun z => orderedDerivative a.2 f (X z)
  let c (a : J) : ℝ := ∏ i : Fin a.1.length, B (a.1.partSize i)
  have hg (a : J) : MemLp (g a) 2 volume :=
    (smooth_planeHk_orderedDerivative_memLp U hf hu a.1.length
      (a.1.length_le.trans hn) a.2).comp_measurePreserving hμ
  have hcomp : MemLp (orderedDerivative w (f ∘ X)) 2 volume :=
    smooth_planeHk_pullback_word_memLp U hf hu hX hμ B hb n hn w
  have hc (a : J) : 0 ≤ c a := by
    apply Finset.prod_nonneg
    intro i _
    exact (norm_nonneg _).trans (hb _ (a.1.partSize_pos i)
      ((a.1.partSize_le i).trans hn) 0)
  have hbound : ∀ᵐ z ∂volume, ‖orderedDerivative w (f ∘ X) z‖ ≤ ∑ a : J, c a * ‖g a z‖ := by
    apply Filter.Eventually.of_forall
    intro z
    have hh := smooth_composition_word_norm_bound hf hX B n
      (fun j hj0 hj => hb j hj0 (hj.trans hn)) w z
    simpa only [J, c, g, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul, mul_comm] using hh
  have hlp := finite_Lp_norm_majorant volume (orderedDerivative w (f ∘ X)) g hcomp hg c hc hbound
  have hnorm (a : J) : ‖(hg a).toLp (g a)‖ =
      ‖U.val ⟨⟨a.1.length, Nat.lt_succ_of_le (a.1.length_le.trans hn)⟩, a.2⟩‖ := by
    change ‖((smooth_planeHk_orderedDerivative_memLp U hf hu a.1.length
      (a.1.length_le.trans hn) a.2).comp_measurePreserving hμ).toLp
        (orderedDerivative a.2 f ∘ X)‖ = _
    rw [← Lp.toLp_compMeasurePreserving (smooth_planeHk_orderedDerivative_memLp U hf hu
      a.1.length (a.1.length_le.trans hn) a.2) hμ, Lp.norm_compMeasurePreserving]
    exact smooth_orderedDerivative_Lp_norm (a.1.length_le.trans hn) U hf hu a.2 _
  have hout := smooth_orderedDerivative_Lp_norm hn
    (smoothPlanePullback U f hf hu X hX hμ B hb) (hf.comp hX)
    (smoothPlanePullback_value_ae U f hf hu X hX hμ B hb) w hcomp
  rw [hout] at hlp
  simp_rw [hnorm] at hlp
  simpa only [J, c, Fintype.sum_sigma, Finset.mul_sum] using hlp
end

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Cell ellipticity preserves half-gradient dissipation in the compact chart test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem cellMetric_cutoff_chart_metric_pointwise
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hCell : IsCellMetric G)
    (t : ℝ) (x : Vec 2)
    (v p Φ h : PiLp 2 (fun _ : Fin 2 => ℝ))
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E)
    {q lam M χ η : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) (hM : 0 ≤ M)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hη : 0 ≤ η)
    (hv : ‖v‖ ≤ 2 * M) (hp : ‖p‖ ≤ Real.sqrt lam * q)
    (hΦ : ‖Φ‖ ≤ Real.sqrt lam * q) (hh : ‖h‖ ≤ 2 * η) :
    2 * lam * χ ^ 2 * q * ‖u‖ ^ 2 + cutoffEnergyResidual (G t x) v p Φ h du F u χ q -
      2 * χ ^ 2 * q * (∑ k : Fin 2, ∑ j : Fin 2,
        G t x k j * inner ℝ (du k) (du j)) + (1 / 2) * χ ^ 2 * q * ‖du‖ ^ 2 ≤
    18 * lam * χ ^ 2 * q * ‖u‖ ^ 2 + 8 * q * ‖F‖ ^ 2 +
      (4096 * η ^ 2 + 16 * M * η) * q * ‖u‖ ^ 2 := by
  have hGn (p : PiLp 2 (fun _ : Fin 2 => ℝ)) : ‖finiteMetricFlux (G t x) p‖ ≤ 5 * ‖p‖ :=
    cellMetric_finiteMetricFlux_scalar_norm_le_five G hCell t x p
  have hQ : (1 / 2 : ℝ) * ‖du‖ ^ 2 ≤
      ∑ k : Fin 2, ∑ j : Fin 2, G t x k j * inner ℝ (du k) (du j) := by
    rw [PiLp.norm_sq_eq_of_L2 _ du]
    exact cellMetric_hilbert_quadratic_lower G hCell t x du
  exact halfCoercive_cutoff_pointwise_energy_absorption hχ hχ1 hη hM hq (Real.sq_sqrt hlam) hQ
    (boundedMetric_cutoff_residual_bound (G t x) hGn v p Φ h du F u hq (Real.sqrt_nonneg _) hM
      hχ hη hv hp hΦ hh)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Composition budgets consume the supplied native weighted jets of a smooth value representative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_smooth_native_composition_budget {K : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 0 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ n ≤ L * qin (X z))
    (hw : ∀ a : JetIndex2 K, MemLp (fun x => qin x • U.toFunction.jet a x) 2 volume) :
    ∃ hm : MemLp (fun z => qout z • orderedDerivative w (f ∘ X) z) 2 volume,
      ‖hm.toLp (fun z => qout z • orderedDerivative w (f ∘ X) z)‖ ≤
        L * ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) *
          ∑ v : DerivativeWord2 c.length,
            ‖(hw ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩).toLp
              (fun x => qin x • U.toFunction.jet
                ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩ x)‖ := by
  have hwin (j : ℕ) (hj : j ≤ n) (v : DerivativeWord2 j) :
      MemLp (fun x => qin x • orderedDerivative v f x) 2 volume :=
    weighted_smooth_jet_memLp U hf hu qin (hj.trans hn) v
      (hw ⟨⟨j, Nat.lt_succ_of_le (hj.trans hn)⟩, v⟩)
  let hm := weighted_smooth_composition_word_memLp hf hX hμ qout qin P hqout hout hin B n w L hL
    hP hB hb hweight hwin
  refine ⟨hm, ?_⟩
  have hh := weighted_smooth_composition_word_Lp_norm_le hf hX hμ qout qin P hqout hout hin
    B n w L hL hP hB hb hweight hwin
  have he (c : OrderedFinpartition n) (v : DerivativeWord2 c.length) :
      ‖(hwin c.length c.length_le v).toLp (fun x => qin x • orderedDerivative v f x)‖ =
      ‖(hw ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩).toLp
        (fun x => qin x • U.toFunction.jet
          ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩ x)‖ :=
    weighted_smooth_jet_Lp_norm U hf hu qin (c.length_le.trans hn) v _ _
  simpa only [he] using hh
end

/-! The finite derivative budget gives a bounded smooth pullback in the native Sobolev norm. -/

section
def smoothPullbackOrderBound (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) * (2 : ℝ) ^ c.length

def smoothPullbackNormBound (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ a : JetIndex2 K, smoothPullbackOrderBound B a.1.val

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smoothPlanePullback_order_norm_le {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ‖(smoothPlanePullback U f hf hu X hX hμ B hb).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      smoothPullbackOrderBound B n * ‖U‖ := by
  apply (smoothPlanePullback_component_norm_le U f hf hu X hX hμ B hb n hn w).trans
  unfold smoothPullbackOrderBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  have hp : 0 ≤ ∏ i : Fin c.length, B (c.partSize i) := by
    apply Finset.prod_nonneg
    intro i _
    exact (norm_nonneg _).trans (hb _ (c.partSize_pos i) ((c.partSize_le i).trans hn) 0)
  have hs : (∑ v : DerivativeWord2 c.length,
      ‖U.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖) ≤
      (2 : ℝ) ^ c.length * ‖U‖ := by
    calc
      _ ≤ ∑ _ : DerivativeWord2 c.length, ‖U‖ := by
        apply Finset.sum_le_sum
        intro v _
        exact PiLp.norm_apply_le U.val _
      _ = _ := by simp [DerivativeWord2, DerivativeWord]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hp

theorem smoothPlanePullback_norm_le {K : ℕ} (U : PlaneHk Set.univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j) :
    ‖smoothPlanePullback U f hf hu X hX hμ B hb‖ ≤ smoothPullbackNormBound B K * ‖U‖ := by
  change ‖(smoothPlanePullback U f hf hu X hX hμ B hb).val‖ ≤ _
  apply (finiteHilbert_norm_le_sum _).trans
  unfold smoothPullbackNormBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  exact smoothPlanePullback_order_norm_le U f hf hu X hX hμ B hb a.1.val
    (Nat.le_of_lt_succ a.1.isLt) a.2
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! Genuine weak plane derivatives give the exact shifted fibre Fourier coefficients. -/

theorem planeBloch_distribution_derivative_coeff_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) = ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (planeScalarBlochTransform a P hP g θ) n =
        (2 * (Real.pi : ℂ) * Complex.I) * ((planeLatticeEmbedding P n + θ) i : ℂ) *
          mFourierCoeff (planeScalarBlochTransform a P hP f θ) n := by
  have hd := planeFourier_distribution_derivative_ae f g i hfg
  have hn (n : Fin 2 → ℤ) : ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P),
      fourierL2 g (planeLatticeEmbedding P n + θ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((planeLatticeEmbedding P n + θ) i : ℂ) *
          fourierL2 f (planeLatticeEmbedding P n + θ) :=
    ae_restrict_of_ae ((measurePreserving_add_left volume (planeLatticeEmbedding P n)).quasiMeasurePreserving.ae hd)
  filter_upwards [ae_all_iff.mpr hn, planeScalarBlochTransform_fourierCoeff_ae a P hP f,
    planeScalarBlochTransform_fourierCoeff_ae a P hP g] with θ hdθ hf hg n
  rw [hf n, hg n]
  exact hdθ n

theorem planeBloch_real_weakDerivative_coeff_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : HasWeakPartialDerivOn Set.univ i f g) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (planeScalarBlochTransform a P hP (ofRealL2 volume g) θ) n =
        (2 * (Real.pi : ℂ) * Complex.I) * ((planeLatticeEmbedding P n + θ) i : ℂ) *
          mFourierCoeff (planeScalarBlochTransform a P hP (ofRealL2 volume f) θ) n :=
  planeBloch_distribution_derivative_coeff_ae a P hP _ _ i
    (coordinate_lineDerivOp_of_weakPartial f g i hfg)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CoupledEnergyPlane.Fourier
open scoped SchwartzMap LineDeriv
namespace AVRegularity.CycleWords

/-! Removing the Bloch phase gives the exact cell derivative Fourier multiplier. -/

local instance planeBlochCellDerivativeMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

def planeBlochCellDerivative (θ : Vec 2) (i : Fin 2)
    (u v : ScalarTorusL2) : ScalarTorusL2 :=
  v - ((2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ)) • u

theorem planeBlochCellDerivative_fourierCoeff (θ : Vec 2) (i : Fin 2)
    (u v : ScalarTorusL2)
    (h : ∀ n : Fin 2 → ℤ, mFourierCoeff v n =
      (2 * (Real.pi : ℂ) * Complex.I) * ((n i : ℝ) + θ i : ℂ) *
        mFourierCoeff u n) (n : Fin 2 → ℤ) :
    mFourierCoeff (planeBlochCellDerivative θ i u v) n =
      (2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ) * mFourierCoeff u n := by
  rw [← mFourierBasis_repr]
  change ((mFourierBasis (d := Fin 2)).repr
    (v - ((2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ)) • u)) n = _
  rw [map_sub, map_smul]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, mFourierBasis_repr]
  rw [h n]
  push_cast
  ring

theorem planeBlochCellDerivative_real_weakDerivative_ae (a : Vec 2)
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : HasWeakPartialDerivOn Set.univ i f g) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a 1), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (planeBlochCellDerivative θ i
        (planeScalarBlochTransform a 1 (by norm_num) (ofRealL2 volume f) θ)
        (planeScalarBlochTransform a 1 (by norm_num) (ofRealL2 volume g) θ)) n =
      (2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ) *
        mFourierCoeff (planeScalarBlochTransform a 1 (by norm_num)
          (ofRealL2 volume f) θ) n := by
  filter_upwards [planeBloch_real_weakDerivative_coeff_ae a 1 (by norm_num) f g i hfg]
    with θ hθ n
  apply planeBlochCellDerivative_fourierCoeff θ i _ _ _ n
  intro m
  have hm := hθ m
  have he : ((planeLatticeEmbedding 1) m + θ) i = (m i : ℝ) + θ i := by
    change m i • (1 : ℝ) + θ i = (m i : ℝ) + θ i
    simp only [zsmul_eq_mul, mul_one]
  rw [he, Complex.ofReal_add, Complex.ofReal_intCast] at hm
  exact hm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory LineDeriv AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
open scoped SchwartzMap
namespace AVRegularity.CycleWords

/-! Exact native value and gradient readouts of the constructed complex plane H1 carrier. -/

theorem planeComplexH1OfDistribution_component
    (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, ∂_{AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, ℂ)) = ((coordinateL2Equiv (g i) : Lp ℂ 2 volume) : 𝓢'(AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, ℂ)))
    (a : JetIndex2 1) :
    univToPlane ((planeComplexH1OfDistribution f g hfg).val a) =
      if h : a.1.val = 0 then f else g (a.2 ⟨0, by omega⟩) := by
  have hr := jetToL2_ae (planeComplexFirstJet f g) (planeComplexFirstJet_memL2 f g) a
  change (planeComplexH1OfDistribution f g hfg).val a =ᵐ[volume.restrict Set.univ]
    planeComplexFirstJet f g a at hr
  have hr' : (planeComplexH1OfDistribution f g hfg).val a =ᵐ[volume]
      planeComplexFirstJet f g a := by
    simpa only [Measure.restrict_univ] using hr
  split_ifs with ha
  · apply Lp.ext
    filter_upwards [univToPlane_ae ((planeComplexH1OfDistribution f g hfg).val a), hr']
      with x hx hrx
    rw [hx, hrx]
    simp only [planeComplexFirstJet, dite_eq_left ha]
  · apply Lp.ext
    filter_upwards [univToPlane_ae ((planeComplexH1OfDistribution f g hfg).val a), hr']
      with x hx hrx
    rw [hx, hrx]
    simp only [planeComplexFirstJet, dite_eq_right ha]

theorem planeComplexH1OfDistribution_value
    (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, ∂_{AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, ℂ)) = ((coordinateL2Equiv (g i) : Lp ℂ 2 volume) : 𝓢'(AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, ℂ))) :
    planeHkValueOperator 1 (planeComplexH1OfDistribution f g hfg) = f := by
  rw [planeHkValueOperator_apply, planeComplexH1OfDistribution_component]
  simp [valueIndex2, valueIndex]

/-! Exact graph norm of the genuine complex plane H1 construction. -/

theorem planeComplexH1OfDistribution_norm_sq
    (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℂ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, ∂_{AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, ℂ)) = ((coordinateL2Equiv (g i) : Lp ℂ 2 volume) : 𝓢'(AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, ℂ))) :
    ‖planeComplexH1OfDistribution f g hfg‖ ^ 2 = ‖f‖ ^ 2 + ∑ i : Fin 2, ‖g i‖ ^ 2 := by
  let z := planeComplexH1OfDistribution f g hfg
  have hn (a : JetIndex2 1) : ‖z.val a‖ =
      ‖if h : a.1.val = 0 then f else g (a.2 ⟨0, by omega⟩)‖ := by
    rw [← univToPlane.norm_map, planeComplexH1OfDistribution_component]
  change ‖z.val‖ ^ 2 = _
  rw [jet_norm_sq_eq_sum, Fin.sum_univ_two]
  have h0 : derivativeNormSq z.val (0 : Fin 2) = ‖f‖ ^ 2 := by
    unfold derivativeNormSq
    simp only [hn, Fin.val_zero]
    change (∑ _w : Fin 0 → Fin 2, ‖f‖ ^ 2) = ‖f‖ ^ 2
    rw [Fintype.sum_unique]
  have h1 : derivativeNormSq z.val (1 : Fin 2) = ∑ i : Fin 2, ‖g i‖ ^ 2 := by
    unfold derivativeNormSq
    simp only [hn, Fin.val_one, dite_eq_right (by decide : (1 : ℕ) ≠ 0)]
    change (∑ w : Fin 1 → Fin 2, ‖g (w 0)‖ ^ 2) = _
    exact ((Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp
      (fun w : Fin 1 → Fin 2 => ‖g (w 0)‖ ^ 2)).symm
  rw [h0, h1]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Polynomial chart composition has a uniform bound in the finite array of actual weighted L2 jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_composition_jet_array_bound {K : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 0 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ n ≤ L * qin (X z))
    (R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => qin x • U.toFunction.jet a x)) :
    ∃ hm : MemLp (fun z => qout z • orderedDerivative w (f ∘ X) z) 2 volume,
      ‖hm.toLp (fun z => qout z • orderedDerivative w (f ∘ X) z)‖ ≤
        L * smoothPullbackOrderBound B n * ‖R‖ := by
  have hw (a : JetIndex2 K) : MemLp (fun x => qin x • U.toFunction.jet a x) 2 volume :=
    (Lp.memLp (R a)).ae_eq (hR a)
  have he (a : JetIndex2 K) :
      (hw a).toLp (fun x => qin x • U.toFunction.jet a x) = R a := by
    apply Lp.ext
    exact (hw a).coeFn_toLp.trans (hR a).symm
  obtain ⟨hm, hnorm⟩ := weighted_smooth_native_composition_budget U hf hu hX hμ qout qin P
    hqout hout hin B n hn w L hL hP hB hb hweight hw
  refine ⟨hm, hnorm.trans ?_⟩
  have hs : (∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) *
      ∑ v : DerivativeWord2 c.length,
        ‖(hw ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩).toLp
          (fun x => qin x • U.toFunction.jet
            ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩ x)‖) ≤
      smoothPullbackOrderBound B n * ‖R‖ := by
    unfold smoothPullbackOrderBound
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c _
    have hp : 0 ≤ ∏ i : Fin c.length, B (c.partSize i) :=
      Finset.prod_nonneg (fun i _ => hB _ (c.partSize_pos i) (c.partSize_le i))
    have hsum : (∑ v : DerivativeWord2 c.length,
        ‖(hw ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩).toLp
          (fun x => qin x • U.toFunction.jet
            ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩ x)‖) ≤
        (2 : ℝ) ^ c.length * ‖R‖ := by
      calc
        _ ≤ ∑ _v : DerivativeWord2 c.length, ‖R‖ := by
          apply Finset.sum_le_sum
          intro v _
          rw [he]
          exact PiLp.norm_apply_le R _
        _ = _ := by simp [DerivativeWord2, DerivativeWord]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hp
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hL

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Reserved ordered slow derivatives commute with measurable time integration. -/

open AVRegularity.CycleComparison.Lift
variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem orderedDerivative_parameter_integral_growth (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (p : ℕ)
    (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j * (1 + ‖x‖) ^ p)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) :
    orderedDerivative α (fun x => ∫ t, f t x ∂μ) =
      fun x => ∫ t, orderedDerivative α (f t) x ∂μ := by
  induction q with
  | zero => simp [orderedDerivative]
  | succ q ih =>
    let β : DerivativeWord2 q := fun i => α i.castSucc
    have hh := ih (by omega) β
    have hf : ∀ t, ContDiff ℝ (1 : ℕ∞) (orderedDerivative β (f t)) := by
      intro t
      exact contDiff_orderedDerivative β ((hs t).of_le
        (by exact_mod_cast (show 1 + q ≤ n by omega)))
    have hme : ∀ x, Measurable (fun t => orderedDerivative β (f t) x) :=
      fun x => orderedDerivative_parameter_measurable f n hm hs q (by omega) β x
    have h₀ : ∀ t x, ‖orderedDerivative β (f t) x‖ ≤ C q * (1 + ‖x‖) ^ p := by
      intro t x
      exact (norm_orderedDerivative_le ((hs t).of_le (by exact_mod_cast (show q ≤ n by omega)))
        β x).trans (hb q (by omega) t x)
    have h₁ : ∀ t x, ‖fderiv ℝ (orderedDerivative β (f t)) x‖ ≤ C (q + 1) * (1 + ‖x‖) ^ p := by
      intro t x
      have hl := norm_iteratedFDeriv_orderedDerivative_le (p := 1) β
        ((hs t).of_le (by exact_mod_cast (show 1 + q ≤ n by omega))) x
      simpa only [norm_iteratedFDeriv_one, Nat.add_comm 1 q] using
        hl.trans (hb (1 + q) (by omega) t x)
    have hd := parameter_integral_hasFDerivAt_growth μ
      (fun t x => orderedDerivative β (f t) x) hme
      (fun t => (hf t).differentiable one_ne_zero) (C q) (C (q + 1)) (hC (q + 1)) p h₀ h₁
    rw [orderedDerivative_succ, hh]
    funext x
    rw [(hd x).fderiv]
    have hi : Integrable (fun t => fderiv ℝ (orderedDerivative β (f t)) x) μ :=
      (integrable_const (C (q + 1) * (1 + ‖x‖) ^ p)).mono'
        (fderiv_parameter_stronglyMeasurable _ hme
          (fun t => (hf t).differentiable one_ne_zero) x).aestronglyMeasurable
        (ae_of_all μ (fun t => h₁ t x))
    rw [ContinuousLinearMap.integral_apply hi]
    apply integral_congr_ae
    exact ae_of_all μ (fun t => (congrFun (orderedDerivative_succ α (f t)) x).symm)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus LineDeriv
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped SchwartzMap
namespace AVRegularity.CycleWords

/-! Fibre Fourier derivative identities reconstruct actual plane distributional derivatives. -/

local instance planeBlochReconstructDerivativeMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem planeBlochReconstruct_distribution_derivative (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F G : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P))) (i : Fin 2)
    (hfg : ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (G θ) n = (2 * (Real.pi : ℂ) * Complex.I) *
        ((planeLatticeEmbedding P n + θ) i : ℂ) * mFourierCoeff (F θ) n) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (planeScalarBlochReconstruct a P hP F) :
      Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) =
      ((coordinateL2Equiv (planeScalarBlochReconstruct a P hP G) : Lp ℂ 2 volume) :
        𝓢'(HilbertTwo, ℂ)) := by
  apply planeFourier_distribution_derivative_of_ae
  apply planeFrequency_ae_of_cell_shifts a P hP
  have hF := planeScalarBlochTransform_fourierCoeff_ae a P hP
    (planeScalarBlochReconstruct a P hP F)
  have hG := planeScalarBlochTransform_fourierCoeff_ae a P hP
    (planeScalarBlochReconstruct a P hP G)
  rw [planeScalarBlochTransform_reconstruct] at hF hG
  filter_upwards [hfg, hF, hG] with θ hθ hf hg n
  rw [← hg n, ← hf n]
  exact hθ n

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Explicit uniform slow-jet bounds after integration over a finite time measure. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_integral_orderedDerivative_growth_le (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (p : ℕ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j * (1 + ‖x‖) ^ p)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) (x : Vec 2) :
    ‖orderedDerivative α (fun x => ∫ t, f t x ∂μ) x‖ ≤ C q * (1 + ‖x‖) ^ p * μ.real Set.univ := by
  rw [orderedDerivative_parameter_integral_growth μ n f hm hs C hC p hb q hq α]
  apply norm_integral_le_of_norm_le_const
  exact ae_of_all μ (fun t => (norm_orderedDerivative_le
    ((hs t).of_le (by exact_mod_cast hq)) α x).trans (hb q hq t x))

theorem parameter_integral_iteratedFDeriv_growth_le (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (p : ℕ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j * (1 + ‖x‖) ^ p)
    (q : ℕ) (hq : q ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun x => ∫ t, f t x ∂μ) x‖ ≤
      (2 : ℝ) ^ q * (C q * (1 + ‖x‖) ^ p * μ.real Set.univ) := by
  have hi : ContDiff ℝ (q : ℕ∞) (fun x => ∫ t, f t x ∂μ) :=
    (parameter_integral_contDiff_growth μ n f hm hs C hC p hb).of_le
    (by exact_mod_cast hq)
  apply (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words hi x).trans
  calc
    _ ≤ ∑ α : DerivativeWord2 q, C q * (1 + ‖x‖) ^ p * μ.real Set.univ :=
      Finset.sum_le_sum (fun α _ =>
        parameter_integral_orderedDerivative_growth_le μ n f hm hs C hC p hb q hq α x)
    _ = _ := by simp

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.ChartTransport
namespace AVRegularity.CycleWords

/-! Pointwise normalized jet bounds pass through a finite parameter integral. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_integral_normalized_jet_le (μ : Measure T) [IsFiniteMeasure μ]
    (N : ℕ) (f : T → Vec 2 → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (N : ℕ∞) (f t)) (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (p : ℕ) (hb : ∀ j ≤ N, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j * (1 + ‖x‖) ^ p)
    (ρ A : ℝ) (hρ : 0 < ρ) (j : ℕ) (hj : j ≤ N) (x : Vec 2)
    (hpoint : ∀ t, ρ ^ j * ‖iteratedFDeriv ℝ j (f t) x‖ ≤ A) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => ∫ t, f t x ∂μ) x‖ ≤
      2 ^ j * A * μ.real Set.univ := by
  have hi : ContDiff ℝ (j : ℕ∞) (fun x => ∫ t, f t x ∂μ) :=
    (parameter_integral_contDiff_growth μ N f hm hs C hC p hb).of_le (by exact_mod_cast hj)
  have hw (w : DerivativeWord2 j) :
      ‖orderedDerivative w (fun x => ∫ t, f t x ∂μ) x‖ ≤ (A / ρ ^ j) * μ.real Set.univ := by
    rw [orderedDerivative_parameter_integral_growth μ N f hm hs C hC p hb j hj w]
    apply norm_integral_le_of_norm_le_const
    apply ae_of_all μ
    intro t
    apply (norm_orderedDerivative_le ((hs t).of_le (by exact_mod_cast hj)) w x).trans
    exact (le_div_iff₀ (pow_pos hρ j)).mpr (by simpa only [mul_comm] using hpoint t)
  calc
    _ ≤ ρ ^ j * ∑ w : DerivativeWord2 j,
        ‖orderedDerivative w (fun x => ∫ t, f t x ∂μ) x‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_sum_words hi x) (pow_nonneg hρ.le _)
    _ ≤ ρ ^ j * ∑ _w : DerivativeWord2 j, (A / ρ ^ j) * μ.real Set.univ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ => hw w)) (pow_nonneg hρ.le _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A finite integral of variable multilinear diagonals retains a linear coefficient budget. -/

theorem integralMultilinear_polynomial_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : Type*} [MeasurableSpace T]
      (μ : Measure T) [IsFiniteMeasure μ]
      (a : T → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ),
      (∀ x, Measurable (fun t => a t x (fun _ => x))) →
      (∀ t, ContDiff ℝ (J : ℕ) (a t)) → ∀ B : ℝ, 0 ≤ B →
      (∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => a t x (fun i => basisVec (w i))) x‖ ≤ B) →
      ∀ j ≤ J, ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => ∫ t, a t x (fun _ => x) ∂μ) x‖ ≤
          C * B * μ.real Set.univ * (1 + ‖x‖) ^ r := by
  obtain ⟨C, hC, hb⟩ := variableMultilinear_polynomial_jet_budget r J
  refine ⟨2 ^ J * C, by positivity, ?_⟩
  intro T _ μ _ a hm ha B hB hab j hj x
  let f := fun t (x : Vec 2) => a t x (fun _ => x)
  have hf : ∀ t, ContDiff ℝ (J : ℕ∞) (f t) := by
    intro t
    have hh := Weighted.multilinear_diagonal_contDiff J (a t) (ha t) 1
    simpa only [f, one_smul] using hh.of_le (by exact_mod_cast le_refl J)
  have hme : ∀ x, Measurable (fun t => f t x) := hm
  have hbound : ∀ k ≤ J, ∀ t y, ‖iteratedFDeriv ℝ k (f t) y‖ ≤
      C * B * (1 + ‖y‖) ^ r := by
    intro k hk t y
    exact hb a ha B hB hab t k hk y
  have hi := parameter_integral_iteratedFDeriv_growth_le μ J f hme hf
    (fun _ => C * B) (fun _ => mul_nonneg hC hB) r hbound j hj x
  apply hi.trans
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
  have hnonneg : 0 ≤ C * B * (1 + ‖x‖) ^ r * μ.real Set.univ := by positivity
  convert mul_le_mul_of_nonneg_right hpow hnonneg using 1; ring

end AVRegularity.CycleWords
end
