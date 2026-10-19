-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.WeakIdentityZeroForcings
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleEvolution.CellBochnerCarrier
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Statements.Intermediate.Families.MolecularJet
public import AVRegularity.CycleWords.FinitePiLpStrongMeasurable
import AVRegularity.CycleWords.ShearFrequencyAlgebra
import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.CoupledEnergyPlane.CarrierMapOperator
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
public import AVRegularity.Analysis.Convolution.Kernel.Spatial
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
@[expose] public noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact product L2 norm and membership of genuine total slice classes. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [MeasurableSpace X] in
theorem bochnerL2TotalSlice_norm_sq (ν : Measure Y) (f : X → Y → E) (x : X)
    (hx : MemLp (f x) 2 ν) :
    ‖bochnerL2TotalSlice ν f x‖ ^ 2 = ∫ y, ‖f x y‖ ^ 2 ∂ν := by
  rw [lpTwoHilbert_normSq_integral]
  apply integral_congr_ae
  filter_upwards [bochnerL2TotalSlice_ae ν f x hx] with y hy
  rw [hy]

omit [InnerProductSpace ℝ E] in
theorem bochnerL2Product_memLp_slices (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → Y → E) (hf : MemLp (Function.uncurry f) 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (f x) 2 ν := by
  have hm := hf.aestronglyMeasurable.prodMk_left
  have hi := (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).prod_right_ae
  filter_upwards [hm, hi] with x hx hi'
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi'

theorem bochnerL2TotalSlice_memLp (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (f : X → Y → E) (hm : StronglyMeasurable (Function.uncurry f))
    (hf : MemLp (Function.uncurry f) 2 (μ.prod ν)) :
    MemLp (bochnerL2TotalSlice ν f) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (bochnerL2TotalSlice_stronglyMeasurable ν f hm).aestronglyMeasurable).mpr
  have hi := (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).integral_prod_left
  apply hi.congr
  filter_upwards [bochnerL2Product_memLp_slices μ ν f hf] with x hx
  exact (bochnerL2TotalSlice_norm_sq ν f x hx).symm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization UnitAddTorus MeasureTheory
namespace AVRegularity.CycleWords

/-! The ambient complex Fourier modes have the literal unit lattice period. -/

theorem cellComplexFourierMode_periodic (n : Fin 2 → ℤ) :
    AVenhance.IsZ2Periodic (cellComplexFourierMode n) := by
  intro k x
  rw [cellComplexFourierMode_eq, cellComplexFourierMode_eq]
  congr 1
  funext i
  change ((x i + (k i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  have hk : (((k i : ℝ) : ℝ) : UnitAddCircle) = 0 := by
    have he : (k i : ℝ) = k i • (1 : ℝ) := by simp
    rw [he, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  rw [AddCircle.coe_add, hk, add_zero]

theorem cellComplexFourierMode_norm_le_one (n : Fin 2 → ℤ) (x : Vec 2) :
    ‖cellComplexFourierMode n x‖ ≤ 1 := by
  rw [cellComplexFourierMode_eq]
  exact (mFourier n).norm_coe_le_norm (fun i => (x i : UnitAddCircle)) |>.trans
    (le_of_eq mFourier_norm)

local instance cellComplexFourierModePeriodicFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ] using
    AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weak_unitCube_volume_lt_top

theorem cellComplexFourierMode_memLp (n : Fin 2 → ℤ) :
    MemLp (cellComplexFourierMode n) 2 (volume.restrict AVenhance.unitCube) :=
  MemLp.of_bound (cellComplexFourierMode_contDiff n).continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (cellComplexFourierMode_norm_le_one n))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The Pi norm is bounded by the literal Euclidean fibre norm. -/

theorem fibrePiNorm_le_fibreNorm (ξ : Fin 2 → ℂ) : ‖ξ‖ ≤ fibreNorm ξ :=
  (pi_norm_le_iff_of_nonneg (fibreNorm_nonneg ξ)).mpr (fibreNorm_coordinate_le ξ)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Integrating-factor energy bounds for fixed finite ODE observables. -/

theorem finiteObservable_weighted_energy {H F Q : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    {a b : ℝ} (hab : a ≤ b) {y dy : ℝ → H}
    (h : StrongTimeRegularity a b y dy) (J : H →L[ℝ] F) (L : H →L[ℝ] Q) (A : ℝ)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (J (dy t)) (J (y t)) + (1 / 2) * ‖L (y t)‖ ^ 2 ≤ A * ‖J (y t)‖ ^ 2) :
    Real.exp (-A * (b - a)) * ‖J (y b)‖ ^ 2 +
      (∫ t in a..b, Real.exp (-A * (t - a)) * ((1 / 2) * ‖L (y t)‖ ^ 2)) ≤
      ‖J (y a)‖ ^ 2 := by
  have hc : ContinuousOn (fun t => (1 / 2) * ‖L (y t)‖ ^ 2) (uIcc a b) :=
    continuousOn_const.mul ((L.continuous.comp_continuousOn h.ac.continuousOn).norm.pow 2)
  have hd : IntervalIntegrable (fun t => (1 / 2) * ‖L (y t)‖ ^ 2) volume a b :=
    hc.intervalIntegrable
  have he := (strongTime_scalar_norm_energy (h.map J)).scalar_weighted_bound hab (-A) 0
    (fun t => (1 / 2) * ‖L (y t)‖ ^ 2) intervalIntegrable_const hd (by
      filter_upwards [hg] with t ht
      simp only [Pi.zero_apply]
      linarith)
  simpa only [Pi.zero_apply, mul_zero, intervalIntegral.integral_zero, add_zero] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! Character modulation intertwines the actual Fourier unitary and frequency translation. -/

local instance hilbertCharacterL2FourierRealComplexSpace : NormedSpace ℝ ℂ :=
  NormedSpace.complexToReal

theorem hilbertSchwartzModulation_fourier_apply (v ξ : HilbertTwo) (f : 𝓢(HilbertTwo, ℂ)) :
    𝓕 (hilbertSchwartzModulation v f) ξ = 𝓕 f (ξ - v) := by
  change 𝓕 (⇑(hilbertSchwartzModulation v f)) ξ = 𝓕 (⇑f) (ξ - v)
  have he : ⇑(hilbertSchwartzModulation v f) =
      fun x => hilbertModulationCharacter v x * f x :=
    funext (fun x => hilbertSchwartzModulation_apply v x f)
  rw [he]
  exact hilbertModulation_fourier v f ξ

theorem hilbertCharacterModulationOperator_fourier_schwartz (v : HilbertTwo)
    (f : 𝓢(HilbertTwo, ℂ)) :
    𝓕 (hilbertCharacterModulationOperator v (f.toLp 2)) =
      hilbertFrequencyTranslation v (𝓕 (f.toLp 2)) := by
  rw [hilbertCharacterModulationOperator_schwartz, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (hilbertSchwartzModulation v f)).coeFn_toLp 2,
    hilbertFrequencyTranslation_ae v ((𝓕 f).toLp 2),
    (hilbertFrequencyTranslation_measurePreserving v).quasiMeasurePreserving.ae
      ((𝓕 f).coeFn_toLp 2 (volume : Measure HilbertTwo))] with ξ h₁ h₂ h₃
  rw [h₁, h₂, h₃, hilbertSchwartzModulation_fourier_apply]

theorem hilbertCharacterModulationOperator_fourier (v : HilbertTwo)
    (f : Lp ℂ 2 (volume : Measure HilbertTwo)) :
    𝓕 (hilbertCharacterModulationOperator v f) = hilbertFrequencyTranslation v (𝓕 f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := HilbertTwo) (F := ℂ) (μ := volume)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction_on
      (p := fun h : Lp ℂ 2 (volume : Measure HilbertTwo) =>
        𝓕 (hilbertCharacterModulationOperator v h) = hilbertFrequencyTranslation v (𝓕 h)) f ?_ ?_
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ HilbertTwo ℂ).continuous.comp
        (hilbertCharacterModulationOperator v).continuous)
      ((hilbertFrequencyTranslation v).continuous.comp
        (Lp.fourierTransformₗᵢ HilbertTwo ℂ).continuous)
  · intro φ
    exact hilbertCharacterModulationOperator_fourier_schwartz v φ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Coefficient evaluations of an iterated derivative use the same finite derivative reserve. -/

theorem norm_iterated_coefficient_word_jet_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec 2 → E} (r j : ℕ)
    (hf : ContDiff ℝ (j + r : ℕ) f) (w : DerivativeWord2 r) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => iteratedFDeriv ℝ r f x (fun i => basisVec (w i))) x‖ ≤
      ‖iteratedFDeriv ℝ (j + r) f x‖ := by
  let v : DerivativeWord2 r := fun i => w (Fin.rev i)
  have he : (fun x => iteratedFDeriv ℝ r f x (fun i => basisVec (w i))) = orderedDerivative v f := by
    rw [orderedDerivative_eq_iteratedFDeriv v (hf.of_le (by exact_mod_cast Nat.le_add_left r j))]
    funext y
    simp only [v, Fin.rev_rev]
  rw [he]
  exact norm_iteratedFDeriv_orderedDerivative_le v hf x

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The molecular envelope bounds each actual mixed jet almost everywhere in time. -/

theorem mixedJet_ae_le_jetSupOn (dom : Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) :
    ∀ᵐ t ∂volume, ∀ Y, (t, Y) ∈ dom → ∀ z,
      ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ ≤
        jetSupOn dom r q f := by
  filter_upwards [ENNReal.ae_le_essSup (μ := volume)
    (fun t : ℝ => ⨆ Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}, ⨆ z : Vec 2,
      ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ)] with t ht
  intro Y hY z
  have hz := le_iSup (fun z : Vec 2 =>
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ) z
  exact (le_iSup₂_of_le Y hY hz).trans ht

theorem molecularJet_term_le {ι : Type*} (ρ e : ℝ) (k j : ℕ)
    (dom : ι → Set (ℝ × Vec 2)) (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2)
    (r q : ℕ) (hrq : r + q ≤ k) :
    ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      jetSupFam dom (r + j) q f ≤ molecularJet ρ e k j dom f := by
  unfold molecularJet
  apply le_trans _ (Finset.single_le_sum (fun _ _ => by positivity)
    (Finset.mem_range.mpr (by omega : r < k + 1)))
  exact Finset.single_le_sum
    (f := fun q => ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      jetSupFam dom (r + j) q f) (fun _ _ => by positivity)
    (Finset.mem_range.mpr (by omega : q < k + 1 - r))

theorem mixedJet_ae_molecular_term {ι : Type*} (ρ e : ℝ) (k j : ℕ)
    (dom : ι → Set (ℝ × Vec 2)) (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2)
    (i : ι) (r q : ℕ) (hrq : r + q ≤ k) :
    ∀ᵐ t ∂volume, ∀ Y, (t, Y) ∈ dom i → ∀ z,
      ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
        ‖iteratedFDeriv ℝ (r + j) (fun Y' => iteratedFDeriv ℝ q (f i t Y') z) Y‖ₑ ≤
          molecularJet ρ e k j dom f := by
  filter_upwards [mixedJet_ae_le_jetSupOn (dom i) (r + j) q (f i)] with t ht
  intro Y hY z
  apply le_trans _ (molecularJet_term_le ρ e k j dom f r q hrq)
  exact mul_le_mul_right ((ht Y hY z).trans (le_iSup (fun i => jetSupOn (dom i) (r + j) q (f i)) i)) _

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Negation and subtraction of actual native time trajectories preserve the
energy-class time integrability. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeTime_neg_memLp {K : ℕ} (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) :
    MemLp (fun t => -U t) 2 μ := hU.neg

theorem nativeTime_sub_memLp {K : ℕ} (μ : Measure ℝ)
    (U V : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    MemLp (fun t => U t - V t) 2 μ := by
  simpa only [sub_eq_add_neg] using nativeTime_add_memLp μ U (fun t => -V t) hU (nativeTime_neg_memLp μ V hV)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Enhanced-normalized frequency coordinates stay in the same complex frequency disc. -/

theorem normalizedFrequency_coordinate_le {η : ℝ} (hη : η ≤ 1)
    (ξ : Fin 2 → ℂ) (i : Fin 2) :
    ‖(Real.sqrt η : ℂ) * ξ i‖ ≤ fibreNorm ξ := by
  have hs : ‖(Real.sqrt η : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg η)]
    exact (Real.sqrt_le_sqrt hη).trans_eq Real.sqrt_one
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans
    (by simpa only [one_mul] using CycleEvolution.fibreNorm_coordinate_le ξ i)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual lattice fibre is strongly measurable as an l2-valued field. -/

variable {E : Type*} [NormedAddCommGroup E]

def planeFrequencyFibre (P : ℝ) (f : Vec 2 → E) (θ : Vec 2) : lp (fun _ : Fin 2 → ℤ => E) 2 := by
  classical
  exact if h : Memℓp (fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ)) 2 then
    ⟨_, h⟩ else 0

theorem planeFrequencyFibre_coeff (P : ℝ) (f : Vec 2 → E) (θ : Vec 2)
    (hθ : Memℓp (fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ)) 2)
    (n : Fin 2 → ℤ) : planeFrequencyFibre P f θ n = f (planeLatticeEmbedding P n + θ) := by
  simp only [planeFrequencyFibre, dite_eq_left hθ]

theorem planeFrequencyFibre_aestronglyMeasurable (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (planeFrequencyFibre P f) (volume.restrict (planeFrequencyCell a P)) := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (Fin 2 → ℤ)))
    (f := fun s θ => ∑ n ∈ s, lp.single 2 n (f (planeLatticeEmbedding P n + θ)))
  · intro s
    have hm (n : Fin 2 → ℤ) : AEStronglyMeasurable
        (fun θ => lp.single (E := fun _ : Fin 2 → ℤ => E) 2 n (f (planeLatticeEmbedding P n + θ)))
        (volume.restrict (planeFrequencyCell a P)) := by
      apply (lp.isometry_single (E := fun _ : Fin 2 → ℤ => E) (p := 2) n).continuous.comp_aestronglyMeasurable
      exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (measurePreserving_add_left volume (planeLatticeEmbedding P n)).quasiMeasurePreserving).mono_measure
          Measure.restrict_le_self
    simpa only [Finset.sum_fn] using s.aestronglyMeasurable_sum (fun n _ => hm n)
  · filter_upwards [planeFrequency_L2_fibre_memℓp a P hP f hf] with θ hθ
    let F : lp (fun _ : Fin 2 → ℤ => E) 2 := ⟨_, hθ⟩
    have he : planeFrequencyFibre P f θ = F := by
      unfold planeFrequencyFibre
      rw [dite_eq_left hθ]
    rw [he]
    have hh := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) F
    exact hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The zero Sobolev carrier has the literal zero representative almost everywhere. -/

theorem planeZeroJetRepresentative_ae
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (K : ℕ) (a : JetIndex2 K) :
    (0 : PlaneHk Set.univ K E).toFunction.jet a =ᵐ[volume] fun _ => 0 := by
  change (fun x => ((0 : JetL2 (volume.restrict Set.univ) K E) a) x) =ᵐ[volume] _
  simp only [PiLp.zero_apply]
  have hz := Lp.coeFn_zero E 2 (volume.restrict (Set.univ : Set (Vec 2)))
  change (∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
    (0 : Lp E 2 (volume.restrict Set.univ)) x = 0) at hz
  rw [ae_restrict_iff' MeasurableSet.univ] at hz
  filter_upwards [hz] with x hx
  exact hx (Set.mem_univ x)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Actual complex multiplication by a real coefficient inherits its scalar jet price. -/

def realScalarMultiplierMap : ℝ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.ofRealCLM

theorem realScalarMultiplierMap_apply (r : ℝ) :
    realScalarMultiplierMap r = ContinuousLinearMap.mul ℝ ℂ (r : ℂ) := rfl

theorem realScalarMultiplier_jet_array_bound (a : Vec 2 → ℝ) (q : ℕ)
    (ha : ContDiff ℝ (q : ℕ) a) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun x => ContinuousLinearMap.mul ℝ ℂ (a x : ℂ)) q x‖ ≤
      (Fintype.card (DerivativeWord2 q) : ℝ) * ‖realScalarMultiplierMap‖ *
        ‖iteratedFDeriv ℝ q a x‖ := by
  let C := realScalarMultiplierMap ∘ a
  have hC : ContDiff ℝ (q : ℕ) C := realScalarMultiplierMap.contDiff.comp ha
  have hj := realScalarMultiplierMap.norm_iteratedFDeriv_comp_left (x := x) ha.contDiffAt le_rfl
  have hh := coefficientDerivativeArray_norm_le_iterated_bound C q hC x
    (‖realScalarMultiplierMap‖ * ‖iteratedFDeriv ℝ q a x‖)
    (mul_nonneg (norm_nonneg realScalarMultiplierMap) (norm_nonneg (iteratedFDeriv ℝ q a x))) hj
  simpa only [C, Function.comp_def, realScalarMultiplierMap_apply, mul_assoc] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Descending graph control for a scalar forced component estimate. -/

theorem forcedGraph_mass_budget {ι : Type*} [Fintype ι]
    (H : ℕ) (rank : ι → ℕ) (hrank : ∀ v, rank v ≤ H)
    (α : ι → ℝ) (hα : ∀ v, 0 ≤ α v) (p : ι → ι → ℝ)
    (hp : ∀ v u, 0 ≤ p v u) (A θ B : ℝ) (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (_hB : 0 ≤ B) (hAB : A ≤ B) (hSB : A * (32 * θ * (1 + θ)) ≤ B) (hMB : A * 32 ≤ B)
    (hcol : ∀ u, ∑ v, ENNReal.ofReal (normalizedFiniteGraph θ p v u) ≤ 1)
    (hsupport : ∀ v u, ENNReal.ofReal (normalizedFiniteGraph θ p v u) ≠ 0 → rank u < rank v)
    (energy data forcing grad remainder : ι → ℝ≥0∞)
    (hgrad : ∀ v, grad v ≤ energy v)
    (he : ∀ v, energy v ≤ ENNReal.ofReal A * (data v + 16 * forcing v))
    (hf : ∀ v, ENNReal.ofReal (α v) * forcing v ≤
      2 * (ENNReal.ofReal θ * ∑ u, ENNReal.ofReal (p v u * α u) * grad u) + 2 * remainder v) :
    (∑ v, ENNReal.ofReal (α v) * energy v) ≤
      (1 + ENNReal.ofReal B) ^ H * ENNReal.ofReal B *
        ((∑ v, ENNReal.ofReal (α v) * data v) + ∑ v, remainder v) := by
  classical
  let b := fun v u => ENNReal.ofReal (normalizedFiniteGraph θ p v u)
  let e := fun v => ENNReal.ofReal (α v) * energy v
  let d := fun v => ENNReal.ofReal B * (ENNReal.ofReal (α v) * data v + remainder v)
  have hrec (v : ι) : e v ≤ d v + ENNReal.ofReal B * ∑ u, b v u * e u := by
    have hn := normalized_forced_component_budget (α v) A θ hA
      (energy v) (data v) (forcing v) (∑ u, ENNReal.ofReal (p v u * α u) * grad u)
      (remainder v) (he v) (hf v)
    have hs := normalized_response_source_budget θ hθ (p v) α (hp v) hα grad energy hgrad
    have hne : e v ≤ ENNReal.ofReal A *
        (ENNReal.ofReal (α v) * data v +
          ENNReal.ofReal (32 * θ * (1 + θ)) * ∑ u, b v u * e u + 32 * remainder v) := by
      exact hn.trans (mul_le_mul_right (add_le_add_left (add_le_add_right hs _) _) _)
    have hcoeff := response_row_coefficient_budget (ENNReal.ofReal A)
      (ENNReal.ofReal (32 * θ * (1 + θ))) 32 (ENNReal.ofReal B) 1
      (e v) (ENNReal.ofReal (α v) * data v) (∑ u, b v u * e u) (remainder v)
      (ENNReal.ofReal_le_ofReal hAB)
      (by rw [← ENNReal.ofReal_mul hA]; exact ENNReal.ofReal_le_ofReal hSB)
      (by rw [show (32 : ℝ≥0∞) = ENNReal.ofReal (32 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul hA]; exact ENNReal.ofReal_le_ofReal hMB)
      (by simpa only [mul_one] using hne)
    simpa only [d, mul_one, mul_add, add_assoc] using hcoeff
  have hh := ennRank_energy_sum_le rank H hrank b hcol hsupport (ENNReal.ofReal B) e d hrec
  simp only [d, e] at hh
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hh
  simpa only [mul_assoc] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Gronwall with a literal lower-integral forcing bound; the forcing need not itself be measurable. -/

theorem positive_part_le_majorant {x f : ℝ} (hf : 0 ≤ f) (h : x ≤ f) :
    (x + |x|) / 2 ≤ f := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    linarith

theorem scalar_energy_lower_integral_gronwall {a b : ℝ} (hab : a ≤ b)
    {E P : ℝ → ℝ} (hE : AVRegularity.CycleEvolution.StrongTimeRegularity a b E P)
    (C : ℝ) (hC : 0 ≤ C) (f d : ℝ → ℝ)
    (hd : IntervalIntegrable d volume a b)
    (hf0 : ∀ t, 0 ≤ f t) (hEa : 0 ≤ E a)
    (hd0 : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ d t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b), P t + d t ≤ C * E t + f t) :
    ∀ t ∈ Icc a b,
      ENNReal.ofReal (E t + ∫ s in a..t, d s) ≤
        (ENNReal.ofReal (E a) + ∫⁻ s in Icc a b, ENNReal.ofReal (f s)) *
          ENNReal.ofReal (Real.exp (C * (t - a))) := by
  let q := fun t => P t + d t - C * E t
  let F := fun t => (q t + |q t|) / 2
  have hEc : ContinuousOn E (Icc a b) := by
    simpa only [uIcc_of_le hab] using hE.ac.continuousOn
  have hEi : IntervalIntegrable E volume a b := hEc.intervalIntegrable_of_Icc hab
  have hPi := hE.scalar_derivative_intervalIntegrable
  have hqi : IntervalIntegrable q volume a b := (hPi.add hd).sub (hEi.const_mul C)
  have hFi : IntervalIntegrable F volume a b := (hqi.add hqi.abs).div_const 2
  have hF0 t : 0 ≤ F t := by
    dsimp only [F]
    have hq := neg_le_abs (q t)
    linarith
  have hgr := scalar_energy_dissipation_le_gronwall hab hE C hC F d hFi hd
    (Filter.Eventually.of_forall hF0) hd0 (Filter.Eventually.of_forall (fun t => by
      dsimp only [F, q]
      have hq := le_abs_self (P t + d t - C * E t)
      linarith))
  have hFbound : ∀ᵐ t ∂volume.restrict (Icc a b), F t ≤ f t := by
    filter_upwards [hgrowth] with t ht
    apply positive_part_le_majorant (hf0 t)
    dsimp only [q]
    linarith
  have hFintegrable : Integrable F (volume.restrict (Icc a b)) := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    simpa only [IntegrableOn, uIoc_of_le hab] using (intervalIntegrable_iff.mp hFi)
  have hFlin := ofReal_intervalIntegral_nonneg hab F hFintegrable hF0
  have hmono : (∫⁻ s in Icc a b, ENNReal.ofReal (F s)) ≤
      ∫⁻ s in Icc a b, ENNReal.ofReal (f s) :=
    lintegral_mono_ae (hFbound.mono (fun _ hs => ENNReal.ofReal_le_ofReal hs))
  intro t ht
  have hh := ENNReal.ofReal_le_ofReal (hgr t ht)
  have hFI0 : 0 ≤ ∫ s in a..b, F s :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hF0)
  rw [ENNReal.ofReal_mul (add_nonneg hEa hFI0), ENNReal.ofReal_add hEa hFI0, hFlin] at hh
  exact hh.trans (mul_le_mul (add_le_add (le_refl _) hmono) (le_refl _) zero_le zero_le)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite molecular envelopes control the literal real-valued mixed jets almost everywhere. -/

theorem molecularJet_ae_real_term {ι : Type*} (ρ e : ℝ) (hρ : 0 ≤ ρ) (he : 0 < e)
    (k j : ℕ) (dom : ι → Set (ℝ × Vec 2))
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2)
    (hM : molecularJet ρ e k j dom f ≠ ⊤) (i : ι)
    (a b : ℕ) (hab : a + b ≤ k) :
    ∀ᵐ t ∂volume, ∀ Y, (t, Y) ∈ dom i → ∀ z,
      ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) *
        ‖iteratedFDeriv ℝ (a + j) (fun Y' => iteratedFDeriv ℝ b (f i t Y') z) Y‖ ≤
          (molecularJet ρ e k j dom f).toReal := by
  filter_upwards [mixedJet_ae_molecular_term ρ e k j dom f i a b hab] with t ht
  intro Y hY z
  have hh := ENNReal.toReal_mono hM (ht Y hY z)
  have hw : 0 ≤ ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) := by positivity
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw, enorm_eq_nnnorm,
    ENNReal.coe_toReal, coe_nnnorm] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Typed finite sums and differences of native trajectories avoid repeated
unfolding of the carrier norm during family weak-equation elaboration. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeTime_sum_memLp {K : ℕ} {L : Type*} [Fintype L] (μ : Measure ℝ)
    (Z : L → ℝ → PlaneHk Set.univ K E) (hZ : ∀ j, MemLp (Z j) 2 μ) :
    MemLp (fun t => ∑ j, Z j t) 2 μ :=
  memLp_finsetSum (ε' := PlaneHk Set.univ K E) (f := Z) Finset.univ (fun j _ => hZ j)

theorem nativeTime_sub_sum_memLp {K : ℕ} {L : Type*} [Fintype L] (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (Z : L → ℝ → PlaneHk Set.univ K E)
    (hU : MemLp U 2 μ) (hZ : ∀ j, MemLp (Z j) 2 μ) :
    MemLp (fun t => U t - ∑ j, Z j t) 2 μ :=
  nativeTime_sub_memLp μ U (fun t => ∑ j, Z j t) hU (nativeTime_sum_memLp μ Z hZ)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A normalized scalar jet budget transfers to a fixed Hilbert map. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalized_scalar_operator_word_le (c : Vec 2 → ℝ) (j : ℕ)
    (hc : ContDiff ℝ (j : ℕ) c) (T : E →L[ℝ] F) (ρ A : ℝ) (hρ : 0 ≤ ρ)
    (x : Vec 2) (hb : ρ ^ j * ‖iteratedFDeriv ℝ j c x‖ ≤ A) (w : DerivativeWord2 j) :
    ρ ^ j * ‖orderedCoefficientDerivative (fun y => c y • T) j w x‖ ≤ A * ‖T‖ := by
  rw [congrFun (Weighted.orderedCoefficientDerivative_smul_const c j hc T w) x]
  have hs := ContinuousLinearMap.opNorm_smul_le (Weighted.orderedScalarDerivative c j w x) T
  have hw := Weighted.orderedScalarDerivative_norm_le c j hc w x
  have hh := mul_le_mul_of_nonneg_left
    (hs.trans (mul_le_mul_of_nonneg_right hw (ContinuousLinearMap.opNorm_nonneg T))) (pow_nonneg hρ j)
  have hb' := mul_le_mul_of_nonneg_right hb (ContinuousLinearMap.opNorm_nonneg T)
  exact hh.trans (by simpa only [mul_assoc] using hb')

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Almost-everywhere congruence and linearity of genuine lattice fibres. -/

section
variable {E : Type*} [NormedAddCommGroup E]

theorem planeFrequencyFibre_congr_ae (a : Vec 2) (P : ℝ) {f g : Vec 2 → E}
    (hfg : f =ᵐ[volume] g) :
    planeFrequencyFibre P f =ᵐ[volume.restrict (planeFrequencyCell a P)] planeFrequencyFibre P g := by
  have hn (n : Fin 2 → ℤ) : ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P),
      f (planeLatticeEmbedding P n + θ) = g (planeLatticeEmbedding P n + θ) :=
    ae_restrict_of_ae ((measurePreserving_add_left volume (planeLatticeEmbedding P n)).quasiMeasurePreserving.ae hfg)
  filter_upwards [ae_all_iff.mpr hn] with θ hθ
  have he : (fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ)) =
      fun n => g (planeLatticeEmbedding P n + θ) := funext hθ
  unfold planeFrequencyFibre
  rw [he]

theorem planeFrequencyFibre_add_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f g : Vec 2 → E) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    planeFrequencyFibre P (fun x => f x + g x) =ᵐ[volume.restrict (planeFrequencyCell a P)]
      fun θ => planeFrequencyFibre P f θ + planeFrequencyFibre P g θ := by
  filter_upwards [planeFrequency_L2_fibre_memℓp a P hP f hf,
    planeFrequency_L2_fibre_memℓp a P hP g hg] with θ hθf hθg
  have hθsum : Memℓp (fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ) +
      g (planeLatticeEmbedding P n + θ)) 2 :=
    Memℓp.add (f := fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ))
      (g := fun n : Fin 2 → ℤ => g (planeLatticeEmbedding P n + θ)) hθf hθg
  simp only [planeFrequencyFibre, dite_eq_left hθsum, dite_eq_left hθf, dite_eq_left hθg]
  apply Subtype.ext
  rfl

variable [NormedSpace ℝ E]

theorem planeFrequencyFibre_smul_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (c : ℝ) (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    planeFrequencyFibre P (fun x => c • f x) =ᵐ[volume.restrict (planeFrequencyCell a P)]
      fun θ => c • planeFrequencyFibre P f θ := by
  filter_upwards [planeFrequency_L2_fibre_memℓp a P hP f hf] with θ hθf
  have hθsmul : Memℓp (fun n : Fin 2 → ℤ => c • f (planeLatticeEmbedding P n + θ)) 2 :=
    Memℓp.const_smul (f := fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ)) hθf c
  simp only [planeFrequencyFibre, dite_eq_left hθsmul, dite_eq_left hθf]
  apply Subtype.ext
  rfl
end

/-! Exact square-density preservation by the plane lattice fibre map. -/

section
variable {E : Type*} [NormedAddCommGroup E]

theorem lp_two_enorm_square (F : lp (fun _ : Fin 2 → ℤ => E) 2) :
    ‖F‖ₑ ^ (2 : ℝ) = ∑' n : Fin 2 → ℤ, ‖F n‖ₑ ^ (2 : ℝ) := by
  have hn : ‖F‖ ^ 2 = ∑' n : Fin 2 → ℤ, ‖F n‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) F
  have hs : Summable (fun n : Fin 2 → ℤ => ‖F n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      F.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hh := congrArg ENNReal.ofReal hn
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs] at hh
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two] using hh

theorem planeFrequencyFibre_enorm_square_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    (fun θ => ‖planeFrequencyFibre P f θ‖ₑ ^ (2 : ℝ)) =ᵐ[volume.restrict (planeFrequencyCell a P)]
      fun θ => ∑' n : Fin 2 → ℤ, ‖f (planeLatticeEmbedding P n + θ)‖ₑ ^ (2 : ℝ) := by
  filter_upwards [planeFrequency_L2_fibre_memℓp a P hP f hf] with θ hθ
  rw [lp_two_enorm_square]
  apply tsum_congr
  intro n
  rw [planeFrequencyFibre_coeff P f θ hθ n]

theorem planeFrequencyFibre_square_integral (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    (∫⁻ θ in planeFrequencyCell a P, ‖planeFrequencyFibre P f θ‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_congr_ae (planeFrequencyFibre_enorm_square_ae a P hP f hf)]
  exact (planeFrequency_lintegral_fibre_tiling a P hP _
    (hf.aestronglyMeasurable.enorm.pow_const _)).symm

theorem planeFrequencyFibre_memLp (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    MemLp (planeFrequencyFibre P f) 2 (volume.restrict (planeFrequencyCell a P)) := by
  change eLpNorm (planeFrequencyFibre P f) 2 (volume.restrict (planeFrequencyCell a P)) < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (planeFrequencyFibre_aestronglyMeasurable a P hP f hf)]
  simp only [ENNReal.toReal_ofNat]
  rw [planeFrequencyFibre_square_integral a P hP f hf]
  simpa only [ENNReal.toReal_ofNat] using
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords

/-! Fixed fiber maps act literally on every native plane weak-jet representative. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planeHkMapRawReadout {K : ℕ} (L : E →L[ℝ] F)
    (q : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (mapPlaneHk L q).toFunction.jet a =ᵐ[volume] fun x => L (q.toFunction.jet a x) := by
  have he := L.coeFn_compLpL (q.val a)
  simp only [Measure.restrict_univ] at he
  change (fun x => (mapPlaneHk L q).val a x) =ᵐ[volume] fun x => L (q.val a x)
  rw [mapPlaneHk_component]
  filter_upwards [he] with x hx
  exact hx

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Function-level readouts of the actual stored weak jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_eq_stored {K j : ℕ} (hj : j ≤ K) (U : PlaneHk Set.univ K E)
    (w : DerivativeWord2 j) :
    planeJetOrder U j w = U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ := by
  funext x
  simp only [planeJetOrder, dite_eq_left hj]

theorem planeJetOrder_memLp {K j : ℕ} (hj : j ≤ K) (U : PlaneHk Set.univ K E)
    (w : DerivativeWord2 j) : MemLp (planeJetOrder U j w) 2 volume := by
  rw [planeJetOrder_eq_stored hj U w]
  simpa only [Measure.restrict_univ] using
    U.toFunction.memL2 ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Literal coefficient word jets under scalar spatial rescaling. -/

theorem norm_scaled_coefficient_word_jet_le {f : Vec 2 → ℝ} (r j : ℕ)
    (hf : ContDiff ℝ (j + r : ℕ) f) (w : DerivativeWord2 r) (c τ : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => c * iteratedFDeriv ℝ r f (τ • x) (fun i => basisVec (w i))) x‖ ≤
      |c| * |τ| ^ j * ‖iteratedFDeriv ℝ (j + r) f (τ • x)‖ := by
  let g := fun x : Vec 2 => iteratedFDeriv ℝ r f x (fun i => basisVec (w i))
  have hg : ContDiff ℝ (j : ℕ) g :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) ℝ
      (fun i => basisVec (w i))).contDiff.comp
      (hf.iteratedFDeriv_right (by exact_mod_cast le_refl (j + r)))
  have hh : ContDiff ℝ (j : ℕ) (fun x : Vec 2 => g (τ • x)) := hg.comp (contDiff_id.const_smul τ)
  change ‖iteratedFDeriv ℝ j (c • (fun x => g (τ • x))) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hh.contDiffAt, norm_smul, Real.norm_eq_abs]
  have hd := congrFun (iteratedFDeriv_comp_const_smul τ hg) x
  rw [hd, norm_smul, Real.norm_eq_abs, abs_pow]
  have hb := norm_iterated_coefficient_word_jet_le r j hf w (τ • x)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
    (mul_nonneg (abs_nonneg c) (pow_nonneg (abs_nonneg τ) j))

/-! Compact smooth coefficient rescalings have a uniform finite ordered-array budget. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smoothCompact_coefficient_rescale_bound
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (⊤ : ℕ∞) C)
    (hc : HasCompactSupport C) (K : ℕ) :
    ∃ A : Fin (K + 1) → ℝ, (∀ l, 0 ≤ A l) ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ l x,
        ‖coefficientDerivativeArray (fun y => C (ρ • y)) l.val x‖ ≤ A l := by
  classical
  have hb (l : Fin (K + 1)) := exists_smoothCompact_rescale_jet_bound C hC hc l.val
  choose B hB hbound using hb
  refine ⟨fun l => (Fintype.card (DerivativeWord2 l.val) : ℝ) * B l, ?_, ?_⟩
  · intro l
    exact mul_nonneg (Nat.cast_nonneg _) (hB l)
  · intro ρ hρ hρ1 l x
    have hd : ContDiff ℝ (l.val : ℕ) (fun y => C (ρ • y)) :=
      (hC.comp (ρ • ContinuousLinearMap.id ℝ (Vec 2)).contDiff).of_le (by simp)
    exact coefficientDerivativeArray_norm_le_iterated_bound _ l.val hd x (B l) (hB l)
      (hbound l ρ hρ hρ1 x)
end

/-! The exact composition budget uses chart jets at the evaluation point only. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_composition_pointwise_word_norm_bound {f : Vec 2 → E} {X : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (B : ℕ → ℝ) (n : ℕ) (w : DerivativeWord2 n) (z : Vec 2)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j X z‖ ≤ B j) :
    ‖orderedDerivative w (f ∘ X) z‖ ≤
      ∑ c : OrderedFinpartition n,
        (∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
          ∏ i : Fin c.length, B (c.partSize i) := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (f ∘ X) z‖ :=
      ChartTransport.norm_orderedDerivative_le ((hf.comp hX).of_le (by simp)) w z
    _ ≤ ∑ c : OrderedFinpartition n, ‖iteratedFDeriv ℝ c.length f (X z)‖ *
        ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) X z‖ :=
      iteratedFDeriv_composition_norm_le (hf.of_le (by simp)).contDiffAt
        (hX.of_le (by simp)).contDiffAt
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul
        (ChartTransport.norm_iteratedFDeriv_le_sum_words (hf.of_le (by simp)) (X z))
      · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => hb _ (c.partSize_pos i) (c.partSize_le i))
      · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
      · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
end

/-! Finite ordered words under a smooth renewal are bounded by actual input words. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_composition_word_norm_bound {f : Vec 2 → E} {X : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (B : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (w : DerivativeWord2 n) (z : Vec 2) :
    ‖orderedDerivative w (f ∘ X) z‖ ≤
      ∑ c : OrderedFinpartition n,
        (∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
          ∏ i : Fin c.length, B (c.partSize i) := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (f ∘ X) z‖ :=
      ChartTransport.norm_orderedDerivative_le ((hf.comp hX).of_le (by simp)) w z
    _ ≤ ∑ c : OrderedFinpartition n, ‖iteratedFDeriv ℝ c.length f (X z)‖ *
        ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) X z‖ :=
      iteratedFDeriv_composition_norm_le (hf.of_le (by simp)).contDiffAt
        (hX.of_le (by simp)).contDiffAt
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul
        (ChartTransport.norm_iteratedFDeriv_le_sum_words (hf.of_le (by simp)) (X z))
      · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => hb _ (c.partSize_pos i) (c.partSize_le i) z)
      · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
      · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Exact transverse Fourier support uses translation invariance, including merely measurable coefficients. -/

local instance torusTransverseFourierSupportMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance torusTransverseFourierSupportHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

theorem mFourier_parallel_half_shift (e : Fin 2) (n : Fin 2 → ℤ) (hn : n e ≠ 0)
    (y : UnitAddTorus (Fin 2)) :
    mFourier n (y + torusQuotient (((1 : ℝ) / 2 / (n e : ℝ)) • basisVec e)) =
      -mFourier n y := by
  have h := fourier_add_half_inv_index hn (by norm_num : (0 : ℝ) < 1) (y e)
  change (∏ i : Fin 2, fourier (n i) (y i +
    ((((1 : ℝ) / 2 / (n e : ℝ)) * basisVec e i : ℝ) : UnitAddCircle))) =
      -(∏ i : Fin 2, fourier (n i) (y i))
  fin_cases e
  · simpa [Fin.prod_univ_two, basisVec_apply] using
      congrArg (fun z : ℂ => z * fourier (n 1) (y 1)) h
  · simpa [Fin.prod_univ_two, basisVec_apply] using
      congrArg (fun z : ℂ => fourier (n 0) (y 0) * z) h

theorem mFourierCoeff_eq_zero_of_parallel_invariant
    (e : Fin 2) (b : UnitAddTorus (Fin 2) → ℂ)
    (hb : ∀ (y : UnitAddTorus (Fin 2)) (s : ℝ),
      b (y + torusQuotient (s • basisVec e)) = b y)
    (n : Fin 2 → ℤ) (hn : n e ≠ 0) : mFourierCoeff b n = 0 := by
  let s : ℝ := 1 / 2 / ((-n) e : ℝ)
  have hneg : (-n) e ≠ 0 := neg_ne_zero.mpr hn
  have he : mFourierCoeff b n = -mFourierCoeff b n := by
    unfold mFourierCoeff
    calc
      _ = ∫ y, mFourier (-n) (y + torusQuotient (s • basisVec e)) •
          b (y + torusQuotient (s • basisVec e)) :=
        (integral_add_right_eq_self
          (fun y : UnitAddTorus (Fin 2) => mFourier (-n) y • b y)
          (torusQuotient (s • basisVec e))).symm
      _ = ∫ y, -(mFourier (-n) y • b y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [mFourier_parallel_half_shift e (-n) hneg, hb y s, neg_smul]
      _ = _ := integral_neg _
  apply Complex.ext
  · change (mFourierCoeff b n).re = 0
    have hr := congrArg Complex.re he
    simp only [Complex.neg_re] at hr
    linarith
  · change (mFourierCoeff b n).im = 0
    have hi := congrArg Complex.im he
    simp only [Complex.neg_im] at hi
    linarith

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Actual directed path lengths for the finite source graph. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def familyReachableDepth (F : ChartedFamily ι h D P Ctx) (n : ℕ) (v : ι) : Prop :=
  ∃ p : Fin (n + 1) → ι, p (Fin.last n) = v ∧
    ∀ k : Fin n, Nonempty (F.Γ (p k.succ) (p k.castSucc))

theorem familyReachableDepth_zero (F : ChartedFamily ι h D P Ctx) (v : ι) :
    familyReachableDepth F 0 v := by
  refine ⟨fun _ => v, rfl, ?_⟩
  intro k
  exact k.elim0

theorem familyReachableDepth_succ (F : ChartedFamily ι h D P Ctx) {n : ℕ} {u v : ι}
    (hn : familyReachableDepth F n u) (he : Nonempty (F.Γ v u)) :
    familyReachableDepth F (n + 1) v := by
  obtain ⟨p, hp, hedge⟩ := hn
  refine ⟨Fin.snoc p v, by simp, ?_⟩
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simpa only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hp] using he
  · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using hedge j

theorem familyReachableDepth_not_succ_depth (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (hdepth : F.HasDepthAtMost H) (v : ι) : ¬ familyReachableDepth F (H + 1) v := by
  rintro ⟨p, _, hedge⟩
  obtain ⟨k, hk⟩ := hdepth p
  exact hk.false (Classical.choice (hedge k))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Short finite energy windows have fixed propagation and adjacent-reserve prices. -/

theorem finiteObservable_short_window_bounds {H F Q : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    {a b : ℝ} (hab : a ≤ b) {y dy : ℝ → H}
    (h : StrongTimeRegularity a b y dy) (J : H →L[ℝ] F) (L : H →L[ℝ] Q) (A : ℝ)
    (hA : 0 ≤ A) (hshort : A * (b - a) ≤ 1)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (J (dy t)) (J (y t)) + (1 / 2) * ‖L (y t)‖ ^ 2 ≤ A * ‖J (y t)‖ ^ 2) :
    ‖J (y b)‖ ^ 2 ≤ Real.exp 1 * ‖J (y a)‖ ^ 2 ∧
      (∫ t in a..b, ‖L (y t)‖ ^ 2) ≤ (2 * Real.exp 1) * ‖J (y a)‖ ^ 2 := by
  have hc : ContinuousOn (fun t => (1 / 2) * ‖L (y t)‖ ^ 2) (Icc a b) := by
    have hyc : ContinuousOn y (Icc a b) := by simpa only [uIcc_of_le hab] using h.ac.continuousOn
    exact continuousOn_const.mul ((L.continuous.comp_continuousOn hyc).norm.pow 2)
  obtain ⟨hE, hI⟩ := exponentialWindow_short_energy_budget
    (fun t => ‖J (y t)‖ ^ 2) (fun t => (1 / 2) * ‖L (y t)‖ ^ 2) a b A hab hA hc
    (fun _ _ => mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _) (sq_nonneg _) hshort
    (finiteObservable_weighted_energy hab h J L A hg)
  rw [intervalIntegral.integral_const_mul] at hI
  exact ⟨hE, by linarith⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Time integrability passes from the energy lift to its actual lower carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_lower_memLp_of_lift {K : ℕ} (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (hW : MemLp W 2 μ)
    (hagrees : (fun t => truncatePlaneHk (Nat.le_succ K) (W t)) =ᵐ[μ] U) :
    MemLp U 2 μ :=
  (memLp_congr_ae hagrees).1
    ((truncatePlaneHk (E := E) (Nat.le_succ K)).comp_memLp' hW)

end AVRegularity.CycleWords
end
end
