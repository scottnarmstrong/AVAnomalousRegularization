-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.ScalarWeightedJetSumMemL2
import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
public import AVRegularity.CycleJoint.PlaneTimeAllMomentCarrier
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite polynomial dissipation has its literal weighted gradient Hilbert representative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}

theorem polynomialWeightedGradientJet_memL2
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (U : PlaneHk Set.univ (K + 1) E)
    (he : weightedGradFactorialNormSq n ϖ zc ρ K U ≠ ⊤) :
    JetMemL2On Set.univ (fun β x => planeMomentSquareRoot n ϖ zc x •
      (planeGradientTensor U).toFunction.jet β x) := by
  have hq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  apply weighted_raw_jets_memL2On_of_stored_energy ρ hρ _
    (planeMomentSquareRoot_continuous n ϖ zc)
  rw [hq, ← weightedFactorialNormSq_stored_readout, planeGradientTensor_weightedFactorialNormSq]
  exact he

/-- The actual weighted first-derivative jet array; finite dissipation supplies its L2 class. -/
def polynomialWeightedGradientJet
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (U : PlaneHk Set.univ (K + 1) E)
    (he : weightedGradFactorialNormSq n ϖ zc ρ K U ≠ ⊤) :
    JetL2 (volume.restrict Set.univ) K (PiLp 2 (fun _ : Fin 2 => E)) :=
  scalarWeightedFactorialJet ρ (planeMomentSquareRoot n ϖ zc) (planeGradientTensor U)
    (polynomialWeightedGradientJet_memL2 n ϖ zc ρ hρ U he)

theorem polynomialWeightedGradientJet_normSq
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (U : PlaneHk Set.univ (K + 1) E)
    (he : weightedGradFactorialNormSq n ϖ zc ρ K U ≠ ⊤) :
    ENNReal.ofReal (‖polynomialWeightedGradientJet n ϖ zc ρ hρ U he‖ ^ 2) =
      weightedGradFactorialNormSq n ϖ zc ρ K U := by
  rw [polynomialWeightedGradientJet, scalarWeightedFactorialJet_moment_normSq,
    planeGradientTensor_weightedFactorialNormSq]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Original pointwise molecular constituent prices control genuine natural-flow Taylor remainders. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem familyPointwiseMolecular_natural_remainder_uniform_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ τ, (∀ Y : Vec 2, (τ, Y) ∈ dom p c) →
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
            derivativeReserveFactor (ρ / e) (K v) (d - 2)
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      F.flux p c v u γ d I τ (E⁻¹ • Y x) (e⁻¹ • Y x) k -
        taylorSlow 0 Ks (fun X => F.flux p c v u γ d I τ X (e⁻¹ • Y x) k)
          (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      ((K v).factorial : ℝ) * Dchart ^ K v * ((K v + 1 : ℕ) * (CR * B * ζ ^ (Ks + 1))) *
        (3 + max (Cchart 0) 0) ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  obtain ⟨CR, hCR, hb⟩ := naturalPreparation_physical_remainder_uniform_jet_budget
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) Ks (K v)
  refine ⟨CR, hCR, ?_⟩
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn τ hdom yc z k j hj
  let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
    molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
          derivativeReserveFactor (ρ / e) (K v) (d - 2)
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
        (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
    · unfold derivativeReserveFactor
      positivity
  have hf : ContDiff ℝ (K v + (Ks + 1) : ℕ)
      (Function.uncurry (fun X y => F.flux p c v u γ d I τ X y k)) := by
    have hh := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c τ hdom v u γ d I
    have hh0 : ContDiff ℝ (K v + (Ks + 1) : ℕ)
        (Function.uncurry (F.flux p c v u γ d I τ)) :=
      hh.of_le (by exact_mod_cast Nat.add_le_add_left hKs (K v))
    exact (ContinuousLinearMap.proj k).contDiff.comp hh0
  have hmix := familyPointwiseMolecular_scalar_mixed_budget F π hπ K Kmax hK dom
    ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ d hd I (Ks + 1) hKs p c τ hdom 0 k
  simp only [add_zero] at hmix
  exact hb hc ha r σ hr hσ hage e E he yc (ρ / e) ϖ ζ B (div_pos hρ he) hsE
    hϖ hscale hζ hB hδ hn _ hf hmix z j hj

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! The exact finite Faà di Bruno majorant controls each native output derivative of rough data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkSmoothPullback_component_norm_le {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    (U : PlaneHk univ K E) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ‖(planeHkSmoothPullback X hX hμ B hB hb U).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) *
        ∑ v : DerivativeWord2 c.length,
          ‖U.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖ := by
  obtain ⟨UN, fN, hUN, hfN, hvN⟩ := exists_smooth_planeHk_approximation U
  have hjet (a : JetIndex2 K) : Continuous (fun V : PlaneHk univ K E => V.val a) :=
    (PiLp.continuous_apply 2 (fun _ : JetIndex2 K => ComponentL2 (volume.restrict univ) E) a).comp
      continuous_subtype_val
  have hl := ((hjet ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩).comp
    (planeHkSmoothPullback_continuous X hX hμ B hB hb)).tendsto U |>.comp hUN
  have hr : Continuous (fun V : PlaneHk univ K E =>
      ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) *
        ∑ v : DerivativeWord2 c.length,
          ‖V.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖) := by
    apply continuous_finsetSum
    intro c _
    apply continuous_const.mul
    apply continuous_finsetSum
    intro v _
    exact (hjet _).norm
  apply le_of_tendsto_of_tendsto' hl.norm ((hr.tendsto U).comp hUN)
  intro N
  dsimp only [Function.comp_apply]
  rw [planeHkSmoothPullback_eq_smooth X hX hμ B hB hb (UN N) (fN N) (hfN N) (hvN N)]
  exact smoothPlanePullback_component_norm_le (UN N) (fN N) (hfN N) (hvN N) X hX hμ B hb n hn w

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual native solution curves with all finite moments give elements of the genuine time moment domain. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance momentOfCurveNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance momentOfCurveModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k
local instance momentOfCurveLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance momentOfCurveLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ

def planeTimeAllMomentCarrierOfCurve (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (w : ℝ → PlaneHk Set.univ K E) (hw : MemLp w 2 μ)
    (he : ∀ n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (w t) ∂μ) ≠ ⊤) :
    PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ := by
  refine ⟨hw.toLp w, (mem_planeTimeAllMomentSubmodule K ϖ ρ zc μ _).mpr ?_⟩
  intro n
  have hAE : (fun t => weightedFactorialNormSq n ϖ zc ρ K ((hw.toLp w) t)) =ᵐ[μ]
      fun t => weightedFactorialNormSq n ϖ zc ρ K (w t) := by
    filter_upwards [hw.coeFn_toLp] with t ht
    rw [ht]
  rw [lintegral_congr_ae hAE]
  exact he n

theorem planeTimeAllMomentCarrierOfCurve_represents (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (w : ℝ → PlaneHk Set.univ K E) (hw : MemLp w 2 μ)
    (he : ∀ n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (w t) ∂μ) ≠ ⊤) :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (planeTimeAllMomentCarrierOfCurve K ϖ ρ zc μ w hw he) w :=
  hw.coeFn_toLp
end

/-! Zero tests use native time-L2 equality, rather than pointwise representatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance momentZeroNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance momentZeroNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k
local instance momentZeroLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance momentZeroLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ

theorem planeTimeAllMomentCarrierToLp_injective (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    Function.Injective (planeTimeAllMomentCarrierToLp (E := E) K ϖ ρ zc μ) :=
  Subtype.val_injective

theorem planeTimeAllMomentCarrier_zero_representative (K : ℕ) (ϖ ρ : ℝ)
    (zc : Vec 2) (μ : Measure ℝ)
    (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) (hf : f = 0) :
    (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f t) =ᵐ[μ] fun _ => 0 := by
  rw [hf, map_zero]
  exact Lp.coeFn_zero _ _ _

theorem planeTimeAllMomentRepresents_zero (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w : ℝ → PlaneHk Set.univ K E)
    (hrep : PlaneTimeAllMomentRepresents K ϖ ρ zc μ f w)
    (hw : w =ᵐ[μ] fun _ => 0) : f = 0 := by
  apply planeTimeAllMomentCarrierToLp_injective K ϖ ρ zc μ
  rw [map_zero]
  apply Lp.ext
  exact (hrep.trans hw).trans (Lp.coeFn_zero _ _ _).symm
end

/-! The literal native time-curve readout, with its coercions elaborated once. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance nativeReadoutNormed (K : ℕ) : NormedAddCommGroup (PlaneHk Set.univ K E) :=
  allMomentTimeNativeNormed K

def planeTimeAllMomentReadout (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (X : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) : ℝ → PlaneHk Set.univ K E :=
  planeTimeAllMomentCarrierToLp K ϖ ρ zc μ X
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The preparation cover supplies weights on native chart subwindows at the full renewal memory scale. -/

def windowCover_subwindowChartWeights {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    {ν B tA tZ ρs g g0 a B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (hg0 : g0 ≤ 1 / 4) {C : ℝ} (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (T : ℝ) (hT : T = ocTauPP α q Λ m) (hTp : 0 < T)
    (Kcut : ℝ) (hKcut : 0 ≤ Kcut)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ Kcut / ocTau α q Λ m)
    (i : Fin (P + 2)) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) ∨
      G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) t 0)
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hlength : u1 - u0 ≤ T / ocEll q Λ m ν ^ 2) (N : ℕ) :
    ChartWeights G (ocCellDrift α q Λ ζ m ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0) (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 N
      (adjointWeightConstant C Kcut) := by
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
  have hnear : IsMetricNearIdentityOn (Set.Icc u0 (u0 + (u1 - u0))) G g := by
    have hbound := cellMetricChoice_nearIdentityOn α q Λ m hφ (l₀ - 1 + i) ν yc G hG
      (windowCoverChartWindow α q Λ m ν tA tZ l₀ P i) g (cov.metric_near i)
    intro t ht
    exact hbound t (hwindow (by simpa only [add_sub_cancel] using ht))
  apply adjointSubwindowChartWeights hΛ hζ cov.pos.1 cov.pos.2.1 hTp hC he
    (by simpa only [hT] using cov.ellT) Kcut hKcut hb _ yc G
    (fun j k => cellMetricChoice_joint_contDiff α q Λ m hφ (l₀ - 1 + i) ν yc G hG j k)
    (cellMetricChoice_symmetric α q Λ m hφ (l₀ - 1 + i) ν yc G hG)
    g (cov.g_range.2.trans hg0) u0 (u1 - u0) (sub_pos.mpr hu) hlength hnear N
  simpa only [hT, neg_mul] using cov.dur

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A native lift determines its continuous lower-order trace, including both endpoints of a nondegenerate window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance allMomentTraceNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := allMomentTimeNativeNormed k

theorem planeAllMoment_same_carrier_continuous_traces (K : ℕ) (ϖ ρ a b : ℝ)
    (hab : a < b) (zc : Vec 2)
    (W : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ zc (volume.restrict (Set.Icc a b)))
    (u u' : ℝ → PlaneHk Set.univ K E) (w w' : ℝ → PlaneHk Set.univ (K + 1) E)
    (hu : ContinuousOn u (Set.Icc a b)) (hu' : ContinuousOn u' (Set.Icc a b))
    (htr : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (htr' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (w' t) = u' t)
    (hw : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ zc (volume.restrict (Set.Icc a b)) W w)
    (hw' : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ zc (volume.restrict (Set.Icc a b)) W w') :
    Set.EqOn u u' (Set.Icc a b) := by
  have he : u =ᵐ[volume.restrict (Set.Icc a b)] u' := by
    filter_upwards [htr, htr', hw.symm.trans hw'] with t ht ht' hwt
    rw [← ht, ← ht', hwt]
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne he hu hu'
end

/-! Almost-everywhere linear native curves with all finite moments produce actual linear maps into the native moment carrier. -/

section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

local instance momentRepNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance momentRepNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k
local instance momentRepLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance momentRepLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ

def HasPlaneTimeAllMomentLinearRepresentation (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (F : X → ℝ → PlaneHk Set.univ K E) : Prop :=
  ∃ T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ,
    ∀ x, PlaneTimeAllMomentRepresents K ϖ ρ zc μ (T x) (F x)

theorem planeTimeAllMoment_curve_linear_representation
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (F : X → ℝ → PlaneHk Set.univ K E)
    (hF : ∀ x, MemLp (F x) 2 μ)
    (hadd : ∀ x y, F (x + y) =ᵐ[μ] fun t => F x t + F y t)
    (hsmul : ∀ (c : ℝ) x, F (c • x) =ᵐ[μ] fun t => c • F x t)
    (he : ∀ x n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (F x t) ∂μ) ≠ ⊤) :
    HasPlaneTimeAllMomentLinearRepresentation K ϖ ρ zc μ F := by
  let T₀ := timeLpCurveLinearMap μ F hF hadd hsmul
  exact ⟨planeTimeAllMomentCarrierLinearMap K ϖ ρ zc μ T₀ F hF (fun _ => rfl) he,
    fun x => planeTimeAllMomentCarrierLinearMap_represents K ϖ ρ zc μ
      T₀ F hF (fun _ => rfl) he x⟩
end

/-! Native lift representatives can be added and identified in their true time-L2 domain. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance repArithmeticNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance repArithmeticModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k
local instance repArithmeticLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance repArithmeticLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ

variable (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)

theorem planeTimeAllMomentRepresents_add
    (f g : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w w' : ℝ → PlaneHk Set.univ K E)
    (hf : PlaneTimeAllMomentRepresents K ϖ ρ zc μ f w)
    (hg : PlaneTimeAllMomentRepresents K ϖ ρ zc μ g w') :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (f + g) (fun t => w t + w' t) := by
  have he := planeTimeAllMomentCarrier_add K ϖ ρ zc μ f g
  filter_upwards [he, hf, hg] with t ht hft hgt
  rw [ht, hft, hgt]

theorem planeTimeAllMomentRepresents_unique
    (f g : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w : ℝ → PlaneHk Set.univ K E)
    (hf : PlaneTimeAllMomentRepresents K ϖ ρ zc μ f w)
    (hg : PlaneTimeAllMomentRepresents K ϖ ρ zc μ g w) : f = g := by
  apply planeTimeAllMomentCarrierToLp_injective K ϖ ρ zc μ
  exact Lp.ext (hf.trans hg.symm)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.CycleReference
open AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Construction-uniform full-memory weights on every certified native subwindow of the preparation cover. -/

theorem windowCover_uniform_subwindow_adjoint_weights {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cw : ℕ → ℝ, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (M : ℕ) (κ : ℕ → ℝ),
      IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (ν B : ℝ), κ m = ν → κ (m - 1) = B →
    ∀ (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tA tZ ρs g g0 a B₀ lam Cb : ℝ) (qJ Kmax : ℕ) (CG : ℕ → ℝ)
      (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2),
      IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ →
      g0 ≤ 1 / 4 →
    ∀ (i : Fin (P + 2)) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ),
      (G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) ∨
       G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) t 0) →
    ∀ (u0 u1 : ℝ), u0 < u1 →
      Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i →
      u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    ∀ N : ℕ, Nonempty (ChartWeights G (ocCellDrift α q Λ ζ m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 N Cw) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, he⟩ := bandChain_enhancement_bound hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, hb⟩ := cutoff_derivative_uniform_bound
  refine ⟨adjointWeightConstant C K, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ Φ M κ hκ m hm hmM ν B hν hB hφ tA tZ ρs g g0 a B₀ lam Cb
    qJ Kmax CG l₀ P y₀ cov hg0 i G hG u0 u1 hu hwindow hlength N
  have hΛ1 : 1 ≤ Λ := by omega
  have hen := he Λ hΛ M (by omega) κ hκ m hm hmM
  rw [hν, hB] at hen
  exact ⟨windowCover_subwindowChartWeights hΛ1 hζ hφ cov hg0
    (le_trans (by norm_num) hC) hen (ocTauPP α q Λ m) rfl
    (Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1)
    K hK.le (hb α q Λ m hΛ1) i G hG u0 u1 hu hwindow hlength N⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Original pointwise molecular constituent prices control genuine natural-flow Taylor remainders. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem familyPointwiseMolecular_natural_remainder_bounded_price_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ τ, (∀ Y : Vec 2, (τ, Y) ∈ dom p c) →
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
            derivativeReserveFactor (ρ / e) (K v) (d - 2)
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      F.flux p c v u γ d I τ (E⁻¹ • Y x) (e⁻¹ • Y x) k -
        taylorSlow 0 Ks (fun X => F.flux p c v u γ d I τ X (e⁻¹ • Y x) k)
          (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      (Kmax.factorial : ℝ) * Dchart ^ Kmax * ((Kmax + 1 : ℕ) * (centeredSlowRemainderBoundedJetPrice Ks Kmax * B * ζ ^ (Ks + 1))) *
        (3 + max (Cchart 0) 0) ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  have hb := naturalPreparation_physical_remainder_bounded_price_jet_bound
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) Ks (K v) Kmax (hK v)
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn τ hdom yc z k j hj
  let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
    molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
          derivativeReserveFactor (ρ / e) (K v) (d - 2)
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
        (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
    · unfold derivativeReserveFactor
      positivity
  have hf : ContDiff ℝ (K v + (Ks + 1) : ℕ)
      (Function.uncurry (fun X y => F.flux p c v u γ d I τ X y k)) := by
    have hh := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c τ hdom v u γ d I
    have hh0 : ContDiff ℝ (K v + (Ks + 1) : ℕ)
        (Function.uncurry (F.flux p c v u γ d I τ)) :=
      hh.of_le (by exact_mod_cast Nat.add_le_add_left hKs (K v))
    exact (ContinuousLinearMap.proj k).contDiff.comp hh0
  have hmix := familyPointwiseMolecular_scalar_mixed_budget F π hπ K Kmax hK dom
    ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ d hd I (Ks + 1) hKs p c τ hdom 0 k
  simp only [add_zero] at hmix
  exact hb hc ha r σ hr hσ hage e E he yc (ρ / e) ϖ ζ B (div_pos hρ he) hsE
    hϖ hscale hζ hB hδ hn _ hf hmix z j hj

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual native family moment energies separate finite mass summation from the scalar PDE estimates. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance massMomentFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E i)) := inferInstance
local instance massMomentFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E i)) := inferInstance
local instance massMomentNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance massMomentFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeNormed k

def planeAllMomentFamilyEnergy (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (π : ι → ℝ) (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ) : ℝ≥0∞ :=
  ∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := E i) (K i) ϖ ρ 0 μ (X i) t) ∂μ

def planeAllMomentFamilyGradientEnergy (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (π : ι → ℝ) (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ) : ℝ≥0∞ :=
  ∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedGradFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t) ∂μ

theorem planeAllMomentFamily_gradient_energy_of_component_budget
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (X : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0 μ)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ) (B : ℝ≥0∞)
    (hb : ∀ i,
      (∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ (K i)
        (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t) ∂μ) ≤
      B * ∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ (K i)
        (planeTimeAllMomentCarrierToLp (E := PiLp 2 (fun _ : Fin 2 => E i))
          (K i) ϖ ρ 0 μ (X i) t) ∂μ) :
    planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π W ≤
      B * planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i))
        K n ϖ ρ μ π X := by
  let G := fun i t => weightedGradFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t)
  let F := fun i t => weightedFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := PiLp 2 (fun _ : Fin 2 => E i))
      (K i) ϖ ρ 0 μ (X i) t)
  have hG (i : ι) : AEMeasurable (G i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i))
  have hF (i : ι) : AEMeasurable (F i) μ :=
    weightedFactorialNormSq_time_aemeasurable (E := PiLp 2 (fun _ : Fin 2 => E i)) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := PiLp 2 (fun _ : Fin 2 => E i))
        (K i) ϖ ρ 0 μ (X i))
  exact finite_mass_time_integral_budget μ (fun i => ENNReal.ofReal ((π i)⁻¹))
    G F B hG hF hb

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Every finite raw jet array of the zero native carrier vanishes almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance zeroJetArrayNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k

theorem planeAllMoment_zero_jet_array (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2)
    (μ : Measure ℝ) (j : ℕ) :
    ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      WithLp.toLp 2 (fun I : DerivativeWord2 j => planeJetOrder
        (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ
          (0 : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) t) j I z) = 0 := by
  filter_upwards [planeTimeAllMomentCarrier_zero_representative (E := E) K ϖ ρ zc μ 0 rfl] with t ht
  rw [ht]
  by_cases hj : j ≤ K
  · have hz : ∀ᵐ z ∂volume, ∀ I : DerivativeWord2 j,
        planeJetOrder (0 : PlaneHk Set.univ K E) j I z = 0 :=
      ae_all_iff.mpr (fun I => planeJetOrder_zero_ae hj I)
    filter_upwards [hz] with z hz
    apply PiLp.ext
    exact hz
  · exact Filter.Eventually.of_forall (fun z => by
      apply PiLp.ext
      intro I
      simp only [planeJetOrder, dite_eq_right hj]
      rfl)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Each actual material output derivative has a radius-scaled budget with the input derivative powers retained. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkScaledPullback_component_norm_le {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (U : PlaneHk univ K E) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ρ ^ n * ‖(planeHkSmoothPullback X hX hμ B hB hb U).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, C (c.partSize i)) *
        ∑ v : DerivativeWord2 c.length,
          ρ ^ c.length * ‖U.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖ := by
  apply (mul_le_mul_of_nonneg_left
    (planeHkSmoothPullback_component_norm_le X hX hμ B hB hb U n hn w) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hp := scaled_partition_product_le c hρ B C
    (fun j hj hjn => hB j hj (hjn.trans hn))
    (fun j hj hjn => hscale j hj (hjn.trans hn))
  have hs : 0 ≤ ∑ v : DerivativeWord2 c.length,
      ‖U.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hp hs
  rw [← mul_assoc]
  apply hh.trans_eq
  rw [← Finset.mul_sum]
  ring

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Negation and subtraction of native carriers retain their actual lift representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance repNegationNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance repNegationModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k

variable (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)

theorem planeTimeAllMomentRepresents_neg
    (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w : ℝ → PlaneHk Set.univ K E)
    (hf : PlaneTimeAllMomentRepresents K ϖ ρ zc μ f w) :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (-f) (fun t => -w t) := by
  have he := planeTimeAllMomentCarrier_smul K ϖ ρ zc μ (-1) f
  simp only [neg_one_smul] at he
  filter_upwards [he, hf] with t ht hft
  exact ht.trans (congrArg Neg.neg hft)

theorem planeTimeAllMomentRepresents_sub
    (f g : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w w' : ℝ → PlaneHk Set.univ K E)
    (hf : PlaneTimeAllMomentRepresents K ϖ ρ zc μ f w)
    (hg : PlaneTimeAllMomentRepresents K ϖ ρ zc μ g w') :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (f - g) (fun t => w t - w' t) := by
  simpa only [sub_eq_add_neg] using planeTimeAllMomentRepresents_add K ϖ ρ zc μ
    f (-g) w (fun t => -w' t) hf (planeTimeAllMomentRepresents_neg K ϖ ρ zc μ g w' hg)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! The literal physical constituent flux reads the actual scalar Sobolev row operators of its finitely many active pieces. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem constituentPhysical_flux_jet_row_ae
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (t : ℝ)
    (v u : ι) (γ : F.Γ v u) (k : Fin 2)
    (J : ℕ) (hJ : (F.identity v u γ).maxOrder ≤ J + 1)
    (hc : ∀ p : (F.locally_finite t t).toFinset, ∀ j,
      Continuous (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k j))
    (M : (F.locally_finite t t).toFinset → JetIndex2 J → ℝ)
    (hM : ∀ p j, 0 ≤ M p j)
    (hb : ∀ (p : (F.locally_finite t t).toFinset) j x,
      |pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k j x|
        ≤ M p j)
    (U : PlaneHk Set.univ J (h u)) :
    (fun x => (∑ d : admissibleOrders K D v u,
      constituentPhysical F ν e E actual v u γ d t x
        (WithLp.toLp 2 (planeNativeJetExtension U x (d.1 - 1)))) k) =ᵐ[volume]
      fun x => ∑ p : (F.locally_finite t t).toFinset, F.weight p t •
        planeScalarJetRow
          (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k)
          (hc p) (M p) (hM p) (hb p) (mapPlaneHk (F.identity v u γ).map U) x := by
  classical
  have hmap : ∀ᵐ x ∂volume, ∀ j : JetIndex2 J,
      (mapPlaneHk (F.identity v u γ).map U).toFunction.jet j x =
        (F.identity v u γ).map (U.toFunction.jet j x) :=
    ae_all_iff.mpr (fun j => AVRegularity.CycleWords.planeHkMapRawReadout
      (F.identity v u γ).map U j)
  have hrow : ∀ᵐ x ∂volume, ∀ p : (F.locally_finite t t).toFinset,
      planeScalarJetRow
          (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k)
          (hc p) (M p) (hM p) (hb p) (mapPlaneHk (F.identity v u γ).map U) x =
        ∑ j : JetIndex2 J,
          pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k j x •
            (mapPlaneHk (F.identity v u γ).map U).toFunction.jet j x :=
    ae_all_iff.mpr (fun p => planeScalarJetRow_ae _ (hc p) (M p) (hM p) (hb p) _)
  filter_upwards [hmap, hrow] with x hm hr
  rw [constituentPhysical_flux_jet_row F K hdesc ν e E actual t t t ⟨le_rfl, le_rfl⟩ v u γ x k J hJ]
  simp_rw [planeNativeJetExtension_index]
  rw [← Finset.sum_coe_sort (F.locally_finite t t).toFinset
    (fun p => F.weight p t • ∑ j : JetIndex2 J,
      transportedNativeScalarJetCoefficient ((F.piece p).material t)
        (F.identity v u γ).maxOrder
        (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k j x •
          (F.identity v u γ).map (U.toFunction.jet j x))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hr p]
  simp only [hm, pieceTransportedNativeScalarJetCoefficient]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The finite native family has finite original-mass forcing energy at every retained moment. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyEnergyFiniteNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k

theorem planeAllMomentFamilyEnergy_ne_top
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ) :
    planeAllMomentFamilyEnergy K n ϖ ρ μ π X ≠ ⊤ := by
  unfold planeAllMomentFamilyEnergy
  have hm (i : ι) := weightedFactorialNormSq_time_aemeasurable n ϖ 0 ρ μ _
    (planeTimeAllMomentCarrier_memLp (K i) ϖ ρ 0 μ (X i))
  rw [lintegral_finsetSum' _ (fun i _ => (hm i).const_mul _)]
  apply ENNReal.sum_ne_top.mpr
  intro i _
  rw [lintegral_const_mul'' _ (hm i)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (planeTimeAllMomentCarrier_moment (K i) ϖ ρ 0 μ (X i) n)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The native mass energy is exactly the literal energy of every represented forcing curve. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyEnergyReadoutNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k

theorem planeAllMomentFamilyEnergy_represented
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i))
    (hF : ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 μ (X i) (F i)) :
    planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π X =
      ∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ 0 ρ (K i) (F i t) ∂μ := by
  unfold planeAllMomentFamilyEnergy
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr hF] with t ht
  exact Finset.sum_congr rfl (fun i _ => congrArg
    (fun U => ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K i) U) (ht i))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Native family gradient budgets apply to every actual represented trajectory. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyGradientReadoutNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k

theorem planeAllMomentFamilyGradientEnergy_represented
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (E i))
    (hw : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 μ (X i) (w i)) :
    planeAllMomentFamilyGradientEnergy K n ϖ ρ μ π X =
      ∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedGradFactorialNormSq n ϖ 0 ρ (K i) (w i t) ∂μ := by
  unfold planeAllMomentFamilyGradientEnergy
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr hw] with t ht
  exact Finset.sum_congr rfl (fun i _ => congrArg
    (fun U => ENNReal.ofReal ((π i)⁻¹) * weightedGradFactorialNormSq n ϖ 0 ρ (K i) U) (ht i))

theorem planeAllMomentFamilyGradientEnergy_component_ne_top
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i)
    (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (E i))
    (hw : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 μ (X i) (w i))
    (he : planeAllMomentFamilyGradientEnergy K n ϖ ρ μ π X ≠ ⊤) (i : ι) :
    (∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ (K i) (w i t) ∂μ) ≠ ⊤ := by
  have hb : ENNReal.ofReal ((π i)⁻¹) *
      (∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ (K i) (w i t) ∂μ) ≤
        planeAllMomentFamilyGradientEnergy K n ϖ ρ μ π X := by
    rw [planeAllMomentFamilyGradientEnergy_represented K n ϖ ρ μ π X w hw,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro t
    exact Finset.single_le_sum (f := fun j => ENNReal.ofReal ((π j)⁻¹) *
      weightedGradFactorialNormSq n ϖ 0 ρ (K j) (w j t))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top he hb)
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hπ i))).ne').ne

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The public polynomial factorial energy of localized torus data has a uniform moment price. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatchLocalization_weightedFactorialNormSq_bound {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) {K : ℕ} (f : TorusHk K E)
    (ρ : ℝ) (n : ℕ) (ϖ R : ℝ) (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R)
    (hscale : ϖ / (N : ℝ) ≤ R) :
    weightedFactorialNormSq n ϖ (spatialPatchCenter N k) ρ K
      (spatialPatchLocalization hζ N hN k K f) ≤
      ENNReal.ofReal ((1 + 2 * R ^ 2) ^ n) * ENNReal.ofReal
        (factorialNormSq ρ (spatialPatchLocalization hζ N hN k K f).val) := by
  rw [weightedFactorialNormSq_stored_readout]
  apply storedChartFactorialEnergy_supported_bound _ _ _ _ (by positivity)
  intro a
  have he := localizeTorusCarrier_jet_ae f (spatialPatchCoefficient (E := E) ζ N k)
    (spatialPatchCoefficient_smooth hζ N k K) (spatialPatchCoefficient_compact hζ N hN k) a
  filter_upwards [he] with x hx
  intro hn
  change (localizeTorusCarrier f _ _ _).toFunction.jet a x ≠ 0 at hn
  rw [hx] at hn
  have hc := multiplicationRawJet_support_subset
    (spatialPatchCoefficient (E := E) ζ N k) f.toFunction.jet a hn
  have hs : tsupport (spatialPatchCoefficient (E := E) ζ N k) ⊆
      tsupport (spatialPatchCutoff ζ N k) :=
    tsupport_smul_subset_left _ (fun _ => ContinuousLinearMap.id ℝ E)
  exact spatialPatch_polynomial_moment_bound hζ N hN k x (hs hc) n ϖ R hϖ hR hscale

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Dimension-free fixed-order composition budgets in the native factorial norm. -/

def compositionFactorialOrderBound (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, C (c.partSize i)) *
    (2 : ℝ) ^ c.length * (c.length.factorial : ℝ)

theorem compositionFactorialOrderBound_nonneg (C : ℕ → ℝ) (n : ℕ)
    (hC : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ C j) : 0 ≤ compositionFactorialOrderBound C n := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (mul_nonneg
    (Finset.prod_nonneg (fun i _ => hC _ (c.partSize_pos i) (c.partSize_le i)))
    (pow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkScaledPullback_component_le_factorial {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (U : PlaneHk univ K E) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ρ ^ n * ‖(planeHkSmoothPullback X hX hμ B hB hb U).val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      compositionFactorialOrderBound C n * Real.sqrt (factorialNormSq ρ U.val) := by
  apply (planeHkScaledPullback_component_norm_le X hX hμ B hB hb hρ C hscale U n hn w).trans
  unfold compositionFactorialOrderBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  have hc : 0 ≤ ∏ i : Fin c.length, C (c.partSize i) := by
    apply Finset.prod_nonneg
    intro i _
    exact (mul_nonneg (pow_nonneg hρ _) (hB _ (c.partSize_pos i) ((c.partSize_le i).trans hn))).trans
      (hscale _ (c.partSize_pos i) ((c.partSize_le i).trans hn))
  have hs : (∑ v : DerivativeWord2 c.length,
      ρ ^ c.length * ‖U.val ⟨⟨c.length, Nat.lt_succ_of_le (c.length_le.trans hn)⟩, v⟩‖) ≤
      (2 : ℝ) ^ c.length * (c.length.factorial : ℝ) * Real.sqrt (factorialNormSq ρ U.val) := by
    calc
      _ ≤ ∑ _v : DerivativeWord2 c.length,
          (c.length.factorial : ℝ) * Real.sqrt (factorialNormSq ρ U.val) := by
        apply Finset.sum_le_sum
        intro v _
        exact scaled_jet_norm_le_factorial hρ U.val c.length (c.length_le.trans hn) v
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul];
                  simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin,
                    Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hc

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Initial-data gradient bounds sum with the original family masses. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance initialGradientNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k

theorem planeAllMomentFamily_gradient_energy_of_initial_budget
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ)
    (I : ι → ℝ≥0∞) (B : ℝ≥0∞)
    (hb : ∀ i, (∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ (K i)
      (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t) ∂μ) ≤ B * I i) :
    planeAllMomentFamilyGradientEnergy K n ϖ ρ μ π W ≤
      B * ∑ i, ENNReal.ofReal ((π i)⁻¹) * I i := by
  classical
  let G := fun i t => weightedGradFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t)
  have hG (i : ι) : AEMeasurable (G i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i))
  unfold planeAllMomentFamilyGradientEnergy
  rw [lintegral_finsetSum' _ (fun i _ => (hG i).const_mul _), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [lintegral_const_mul'' _ (hG i)]
  exact (mul_le_mul_of_nonneg_left (hb i) zero_le).trans_eq (mul_left_comm _ _ _)

theorem planeAllMomentFamily_gradient_energy_of_represented_initial_budget
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (E i))
    (hw : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 μ (W i) (w i))
    (I : ι → ℝ≥0∞) (B : ℝ≥0∞)
    (hb : ∀ i, (∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ (K i) (w i t) ∂μ) ≤ B * I i) :
    planeAllMomentFamilyGradientEnergy K n ϖ ρ μ π W ≤
      B * ∑ i, ENNReal.ofReal ((π i)⁻¹) * I i := by
  apply planeAllMomentFamily_gradient_energy_of_initial_budget K n ϖ ρ μ π W I B
  intro i
  convert hb i using 1
  apply lintegral_congr_ae
  filter_upwards [hw i] with t ht
  rw [ht]

end AVRegularity.CycleJointProofs
end
