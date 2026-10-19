-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.CycleReference.ChartCorrectionIntegrability
public import AVRegularity.Construction.Preservation.Buffer.ShiftedEnergyEndpoint
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.Velocity.Port.Section2FlowInverseBounds
public import AVRegularity.Weighted.DriftCoefficientEmbedding
import AVRegularity.CycleComparison.Lift.CellScalarSourceSeries
import AVRegularity.CycleJoint.PeriodicMultiplicationJetEnergy
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVenhance.Infra.Section4.Amnr.SpatialOperatorBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Adjacent-order molecular energies of the same finite Fourier coefficient vector. -/

open CoupledEnergy.Galerkin
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem fourier_mass_adjacent_order (N j : ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (x : CoupledPlainCoefficients (h := h) N) :
    massNormSq ρ π (fun i => (coupledPlainSynthesis N i (j + 1) x).val) ≤
      massNormSq ρ π (fun i => (coupledPlainSynthesis N i 0 x).val) +
        ρ ^ 2 * massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (j + 1) x).val) := by
  have hv (i : ι) : derivativeNormSq (coupledPlainSynthesis N i (j + 1) x).val 0 =
      factorialNormSq ρ (coupledPlainSynthesis N i 0 x).val := by
    rw [← coupledPlainSynthesis_truncate N i (Nat.zero_le (j + 1)) x,
      factorialNormSq_zero_eq_derivative]
    rfl
  simpa only [hv, massNormSq] using
    massNormSq_le_value_add_grad ρ π hπ (fun i => (coupledPlainSynthesis N i (j + 1) x).val)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.Buffer

/-! A literal context mode certificate controls the entire continuous final phase. -/

theorem continuous_phase_norm_le_contextSize
    (D : OCData) (b : ℝ) (hb : 0 ≤ b) (j₀ i : ℕ)
    (F : {p : ℤ // Odd p} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (mres : ℝ) (L : ℕ) (p : {p : ℤ // Odd p})
    (f : C(AddCircle 1, ℂ))
    (hcoeff : ∀ h : ℤ, ‖fourierCoeff f h‖ₑ ≤ ctxModeSup D b j₀ i p.1 (F p) mres h)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ) :
    ‖f‖ ≤ θ := by
  have hsum : (∑' h : ℤ, ‖fourierCoeff f h‖ₑ) ≤ ENNReal.ofReal θ := by
    apply le_trans _ hsize
    unfold ctxSize
    apply ENNReal.tsum_le_tsum
    intro h
    have he : 1 ≤ Real.exp (3 * Real.pi * b * |(h : ℝ)|) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hp : 1 ≤ (1 + |(h : ℝ)|) ^ L :=
      one_le_pow₀ (by linarith only [abs_nonneg (h : ℝ)])
    have hw : (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L) := by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (one_le_mul_of_one_le_of_one_le he hp)
    exact (hcoeff h).trans ((one_mul _).symm.le.trans
      ((mul_le_mul_left hw _).trans (mul_le_mul_right
        (le_iSup (fun p : {p : ℤ // Odd p} => ctxModeSup D b j₀ i p.1 (F p) mres h) p) _)))
  have hs : Summable (fun h : ℤ => ‖fourierCoeff f h‖) :=
    tsum_enorm_ne_top_iff_summable_norm.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum)
  apply (continuous_phase_norm_le_fourier_norm_sum f hs).trans
  apply (ENNReal.ofReal_le_ofReal_iff hθ).mp
  rw [ENNReal.ofReal_tsum_of_nonneg (fun h => norm_nonneg (fourierCoeff f h)) hs]
  simpa only [ofReal_norm] using hsum

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual higher-carrier time classes give integrable weighted dissipation. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem kernel_gradient_time_integrable {k : ℕ} (a b ρ : ℝ) (π : ι → ℝ)
    (w : ∀ i, ℝ → TorusHk (k + 1) (E i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    IntegrableOn (fun t => massGradNormSq ρ π (fun i => (w i t).val)) (Set.Icc a b) := by
  classical
  have he : (fun t => massGradNormSq ρ π (fun i => (w i t).val)) =
      fun t => ∑ i, (π i)⁻¹ * ‖KernelEnergy.torusFactorialGradientReadout ρ k (w i t)‖ ^ 2 := by
    funext t
    unfold massGradNormSq
    simp only [KernelEnergy.torusFactorialGradientReadout_normSq]
  rw [he]
  apply integrable_finsetSum
  intro i _
  have hi := ((KernelEnergy.torusFactorialGradientReadout (E := E i) ρ k).comp_memLp' (hw i)).norm.integrable_sq.const_mul ((π i)⁻¹)
  simpa only [Function.comp_def] using hi

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Recover positive-time higher carriers from the existing ambient weak compactness. -/

open CoupledEnergy.Variational
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def familyGraphReadout (K : ι → ℕ) :
    CoupledLowHilbert (h := h) K →L[ℝ] (∀ i, TorusHk (K i) (h i)) :=
  ContinuousLinearMap.pi (fun i =>
    (closedSubmoduleReadout (torusHkGraph (E := h i) (K i))).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j) (h j)) i))

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem familyGraphReadout_carrier (K : ι → ℕ) (f : ∀ i, TorusHk (K i) (h i)) :
    familyGraphReadout K (WithLp.toLp 2 (fun i => (f i).val)) = f := by
  funext i
  apply Subtype.ext
  change (torusHkGraph (E := h i) (K i)).toSubmodule.starProjection (f i).val = (f i).val
  exact Submodule.starProjection_eq_self_iff.mpr (f i).property

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem familyGraphReadout_val_of_weak_limit (K : ι → ℕ)
    (f : ℕ → ∀ i, TorusHk (K i) (h i)) (V : CoupledLowHilbert (h := h) K)
    (hlim : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (WithLp.toLp 2 (fun i => (f n i).val))) atTop (𝓝 (ell V))) :
    ∀ i, (familyGraphReadout K V i).val = V i := by
  intro i
  have hm : V i ∈ torusHkGraph (E := h i) (K i) :=
    mem_closedSubmodule_of_weak_limit _
      (fun ell => hlim (ell.comp (PiLp.proj (𝕜 := ℝ) 2
        (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j) (h j)) i)))
      (fun n => (f n i).property)
  change (torusHkGraph (E := h i) (K i)).toSubmodule.starProjection (V i) = V i
  exact Submodule.starProjection_eq_self_iff.mpr hm

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem familyGraphReadout_mass_bound (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (M : ℝ) (f : ℕ → ∀ i, TorusHk (K i) (h i))
    (V : CoupledLowHilbert (h := h) K)
    (hlim : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (WithLp.toLp 2 (fun i => (f n i).val))) atTop (𝓝 (ell V)))
    (hbound : ∀ n, Real.sqrt (massNormSq ρ π (fun i => (f n i).val)) ≤ M) :
    Real.sqrt (massNormSq ρ π (fun i => (familyGraphReadout K V i).val)) ≤ M := by
  let L : CoupledLowHilbert (h := h) K →L[ℝ] CoupledLowHilbert (h := h) K :=
    (massWeightedCarrierCLM (E := h) K ρ π).comp (familyGraphReadout (h := h) K)
  have hb : ∀ n, ‖L (WithLp.toLp 2 (fun i => (f n i).val))‖ ≤ M := by
    intro n
    simpa only [L, ContinuousLinearMap.comp_apply, familyGraphReadout_carrier,
      massWeightedCarrierCLM_norm (E := h) K ρ π hπ] using hbound n
  have hw : ‖L V‖ ≤ M := norm_le_of_tendsto_clm hb (fun ell => hlim (ell.comp L))
  change ‖massWeightedCarrierCLM (E := h) K ρ π (familyGraphReadout K V)‖ ≤ M at hw
  rw [massWeightedCarrierCLM_norm (E := h) K ρ π hπ] at hw
  exact hw

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! Structural parallel invariance turns any affine fast trace into one scalar profile. -/

theorem fast_affine_profile_regular_and_jet_bound
    (par : Fin 2) (f : Vec 2 → ℂ)
    (hp : ∀ z : Vec 2, ∀ s : ℝ, f (z + s • basisVec par) = f z)
    (z : Vec 2) (lam : ℝ) (n : ℕ)
    (hs : ContDiff ℝ (n : ℕ∞) (fun s : ℝ => f (z + s • basisVec par.rev)))
    (A : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ s : ℝ,
      ‖iteratedDeriv j (fun s : ℝ => f (z + s • basisVec par.rev)) s‖ ≤ A j) :
    ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => f (z + lam • X)) ∧
      ∀ j ≤ n, ∀ X : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 => f (z + lam • X)) X‖ ≤
          A j * ‖lam • (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ)‖ ^ j := by
  let L : Vec 2 →L[ℝ] ℝ := lam • ContinuousLinearMap.proj par.rev
  let H : ℝ → ℂ := fun s => f (z + s • basisVec par.rev)
  have he : (fun X : Vec 2 => f (z + lam • X)) = H ∘ L := by
    funext X
    exact parallel_invariant_affine_profile par f hp z X lam
  rw [he]
  refine ⟨hs.comp L.contDiff, ?_⟩
  intro j hj X
  rw [L.iteratedFDeriv_comp_right hs X (by exact_mod_cast hj)]
  have hh := (iteratedFDeriv ℝ j H (L X)).norm_compContinuousLinearMap_le (fun _ => L)
  apply (show ‖(iteratedFDeriv ℝ j H (L X)).compContinuousLinearMap (fun _ => L)‖ ≤
      ‖iteratedFDeriv ℝ j H (L X)‖ * ‖L‖ ^ j from by simpa using hh).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hb j hj (L X)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Strong low traces identify the recovered higher carrier without choosing a new evolution. -/

open CoupledEnergy.Variational CoupledEnergy.Galerkin
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def familyValueReadout (K : ι → ℕ) (i : ι) :
    CoupledLowHilbert (h := h) K →L[ℝ] Lp (h i) 2 (volume.restrict AVenhance.unitCube) :=
  (PiLp.proj (𝕜 := ℝ) 2
    (fun _ : JetIndex2 (K i) => Lp (h i) 2 (volume.restrict AVenhance.unitCube))
    (valueIndex2 (K i))).comp
    (PiLp.proj (𝕜 := ℝ) 2
      (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j) (h j)) i)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! Positivity of both diffusivities and the enhanced radius is uniform over the band chain. -/

theorem band_preparation_positivity {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ cr : ℝ, 0 < cr →
        0 < κ m ∧ 0 < κ (m - 1) ∧
          0 < cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hbound⟩ :=
    CycleReference.bandChain_all_level_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M κ hκ m hm hmM cr hcr
  have h128 := hΛ₀.trans hΛ
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hκpos (i : ℕ) (hi : 1 ≤ i) (hiM : i ≤ M) : 0 < κ i := by
    have he := (Scales.epsilon_basic (m := i) hq.1 h128).1
    exact (mul_pos (inv_pos.mpr hCp) (Real.rpow_pos_of_pos he _)).trans_le
      (hbound Λ hΛ M (by omega) κ hκ i hi hiM).1
  have hmpos := hκpos m (by omega) hmM
  have hprev := hκpos (m - 1) (by omega) (by omega)
  have ht : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos (by omega)
  exact ⟨hmpos, hprev, mul_pos hcr (Real.sqrt_pos.2 (mul_pos hprev ht))⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! Reconstruct the literal final phase under its pointwise context certificate. -/

open CycleComparison.Lift

theorem finalPhase_value_norm_le_contextSize
    (D : OCData) (b : ℝ) (hb : 0 ≤ b) (j₀ i : ℕ)
    (F : {p : ℤ // Odd p} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (mres : ℝ) (L : ℕ) (p : {p : ℤ // Odd p}) (dd : ChainData) (n : ℕ)
    (hdd : ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p.1 ch ∧
      ch.data = dd ∧ ch.children.length = n)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p.1)
    (x : ChainParamsC n) (hx : x ∈ carrierC D b dd n mres)
    (hreal : ∀ a, (x.2.2 a).im = 0)
    (hc : Continuous (fun s : ℝ => F p dd n t
      (x.1, x.2.1, x.2.2 + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)))
    (hp : Function.Periodic (fun s : ℝ => F p dd n t
      (x.1, x.2.1, x.2.2 + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) 1)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ) :
    ‖F p dd n t x‖ ≤ θ := by
  let g := fun s : ℝ => F p dd n t
    (x.1, x.2.1, x.2.2 + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
  let C : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, periodic_profileLift_continuous g hc hp⟩
  have hcoeff : ∀ h : ℤ, ‖fourierCoeff C h‖ₑ ≤ ctxModeSup D b j₀ i p.1 (F p) mres h := by
    intro h
    have heq : fourierCoeff C h = finalPhaseCoeff (transverseIndex p.1) (F p dd n t) x h :=
      (unitProfileFourierCoeff_eq_lift_coeff g hp h).symm.trans
        (finalPhaseCoeff_eq_fourierCoeffOn (transverseIndex p.1) (F p dd n t) x h).symm
    rw [heq]
    exact finalPhaseCoeff_enorm_le_ctxModeSup D b j₀ i p.1 (F p) mres h dd n hdd t ht x hx hreal
  have hC := continuous_phase_norm_le_contextSize D b hb j₀ i F mres L p C hcoeff θ hθ hsize
  have hzero : C (0 : AddCircle (1 : ℝ)) = F p dd n t x := by
    change g (0 : ℝ) = _
    dsimp [g]
    simp only [ite_self, ← Pi.zero_def, add_zero]
  rw [← hzero]
  exact (C.norm_coe_le_norm _).trans hC

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open AVRegularity.CycleReference
open scoped Matrix
namespace AVRegularity.Construction.Preservation.Buffer

/-! Integrate the actual weak pullback gradient bound using preservation of cell volume. -/

theorem streamFlow_pullback_gradient_integral_le {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    {L : ℝ} (hX : ∀ x, ‖fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) x‖ ≤ L)
    (i : Fin 2) :
    (∫ y in unitCube,
      (((jacMatrix (fun z => AVRegularity.streamFlow φ hφ t z s) y)ᵀ.mulVec
        (Du (AVRegularity.streamFlow φ hφ t y s))) i) ^ 2) ≤
      2 * L ^ 2 * ∑ j : Fin 2, ∫ y in unitCube, Du y j ^ 2 := by
  have hpull := streamFlow_periodicH1 hφ t s hu
  have hleft := (memLp_two_iff_integrable_sq (hpull.2.2.2.1 i).aestronglyMeasurable).mp
    (hpull.2.2.2.1 i)
  have hJP (j : Fin 2) := streamFlow_cell_memL2 hφ t s
    (hp := fun k x => congrFun (hu.2.1 k x) j) (hu.2.2.2.1 j)
  have hright : Integrable (fun y => ∑ j : Fin 2,
      Du (AVRegularity.streamFlow φ hφ t y s) j ^ 2) (volume.restrict unitCube) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      (memLp_two_iff_integrable_sq (hJP j).aestronglyMeasurable).mp (hJP j))
  have hb := integral_mono_ae hleft (hright.const_mul (2 * L ^ 2))
    (Filter.Eventually.of_forall fun y => pullback_gradient_coordinate_square_le
      (fun z => AVRegularity.streamFlow φ hφ t z s) y
      (Du (AVRegularity.streamFlow φ hφ t y s)) (hX y) i)
  rw [integral_const_mul] at hb
  have hp : IsZ2Periodic (fun y => ∑ j : Fin 2, Du y j ^ 2) := by
    intro k y
    dsimp only
    rw [hu.2.1 k y]
  rw [streamFlow_cell_integral hφ t s _ hp] at hb
  rw [integral_finsetSum _ (fun j _ =>
    (memLp_two_iff_integrable_sq (hu.2.2.2.1 j).aestronglyMeasurable).mp (hu.2.2.2.1 j))] at hb
  exact hb

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
open AVRegularity.CycleReference AVRegularity.EntryScales
namespace AVRegularity.Construction.Preservation.Buffer

/-! A uniform band-chain price compares the finest molecular radius with the enhanced radius. -/

theorem band_preparation_radius_ratio_power {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ c₀ cr : ℝ,
      0 < c₀ → 0 < cr → ∃ A : ℝ, 0 < A ∧ ∀ M : ℕ,
        ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, 2 ≤ m → m ≤ M →
        (c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m))) /
          (cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) ≤
          A * ocEpsilon q Λ (m - 1) ^ (q - (1 + ocC α q)) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Lq, hLq, hqpow⟩ := epsilon_power_asymp_shared_threshold hq.1
  obtain ⟨Kq, hKq, hpower⟩ := hqpow 1
  have hCip : 0 < Ci := lt_of_lt_of_le (by norm_num) hCi
  have hKqp : 0 < Kq := lt_of_lt_of_le (by norm_num) hKq
  refine ⟨max Li Lq, le_trans hLi (le_max_left _ _), ?_⟩
  intro Λ hΛ c₀ cr hc₀ hcr
  let Cr := Real.sqrt (Ci * 2 ^ (26 : ℕ)) * max cr cr⁻¹
  have hCr : 0 < Cr :=
    mul_pos (Real.sqrt_pos.2 (mul_pos hCip (by positivity))) (lt_max_of_lt_left hcr)
  refine ⟨(c₀ * Kq) * Cr, mul_pos (mul_pos hc₀ hKqp) hCr, ?_⟩
  intro M κ hκ m hm hmM
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛq : Lq ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLi.trans hΛi
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hband := hi Λ hΛi M (by omega) κ hκ (m - 1) (by omega) (by omega)
  have htime := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)
  have hrho := rho_asymp hE hCip (by positivity) hcr hband htime
  change ocAsymp Cr (cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m))
    (ocEpsilon q Λ (m - 1) ^ (1 + ocC α q)) at hrho
  have hr : 0 < cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hCr) (Real.rpow_pos_of_pos hE _)) hrho.1
  have heps := (hpower Λ m hΛq hm).2
  simp only [Real.rpow_one, mul_one] at heps
  have hnum : c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m)) ≤
      (c₀ * Kq) * ocEpsilon q Λ (m - 1) ^ q := by
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀.le).trans
      ((mul_le_mul_of_nonneg_left heps hc₀.le).trans_eq (mul_assoc _ _ _).symm)
  exact preparation_radius_ratio_le hE hr (mul_pos hc₀ hKqp).le hCr hnum hrho.1

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.Buffer

/-! Keep the exponential part of the literal context certificate for all fast orders. -/

open CycleComparison.Lift

theorem context_exponential_mode_budget
    (D : OCData) (b : ℝ) (j₀ i : ℕ)
    (F : {p : ℤ // Odd p} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (mres : ℝ) (L : ℕ) (p : {p : ℤ // Odd p}) (c : ℤ → ℂ)
    (hc : ∀ h : ℤ, ‖c h‖ₑ ≤ ctxModeSup D b j₀ i p.1 (F p) mres h)
    (θ : ℝ) (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ) :
    (∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|)) *
      ‖c h‖ₑ) ≤ ENNReal.ofReal θ := by
  apply le_trans _ hsize
  unfold ctxSize
  apply ENNReal.tsum_le_tsum
  intro h
  have hp : 1 ≤ (1 + |(h : ℝ)|) ^ L :=
    one_le_pow₀ (by linarith only [abs_nonneg (h : ℝ)])
  have hw : ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|)) ≤
      ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
        (1 + |(h : ℝ)|) ^ L) := by
    apply ENNReal.ofReal_le_ofReal
    exact (mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le)
  exact (mul_le_mul_right (hc h) _).trans
    ((mul_le_mul_left hw _).trans (mul_le_mul_right
      (le_iSup (fun p : {p : ℤ // Odd p} =>
        ctxModeSup D b j₀ i p.1 (F p) mres h) p) _))

theorem context_profile_regular_and_jet_bound
    (D : OCData) (b : ℝ) (hb : 0 < b) (j₀ i : ℕ)
    (F : {p : ℤ // Odd p} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (mres : ℝ) (L : ℕ) (p : {p : ℤ // Odd p})
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (hc : ∀ h : ℤ, ‖unitProfileFourierCoeff f h‖ₑ ≤
      ctxModeSup D b j₀ i p.1 (F p) mres h)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ)
    (q : ℕ) : ContDiff ℝ q f ∧ ∀ j : ℕ, j ≤ q → ∀ x : ℝ,
      ‖iteratedDeriv j f x‖ ≤
        ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ := by
  apply exponential_profile_regular_and_jet_bound f hf hp (3 * Real.pi * b)
    (by positivity) θ hθ
  exact context_exponential_mode_budget D b j₀ i F mres L p _ hc θ hsize

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! Weak periodic integration by parts controls pairing with a derivative of a periodic primitive. -/

theorem periodic_primitive_pairing_bound {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) (η φ : Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηp : IsZ2Periodic η)
    (i : Fin 2) {ell : ℝ} (hell : 0 < ell)
    (hder : ∀ x, spaceGrad η x i = ell * φ x) :
    |∫ x in unitCube, u x * φ x| ≤
      (Real.sqrt (∫ x in unitCube, (Du x i) ^ 2) *
        Real.sqrt (∫ x in unitCube, η x ^ 2)) / ell := by
  have he := CycleReference.periodicH1_smooth_cell_ibp hu hη hηp i
  have hleft : (∫ x in unitCube, u x * spaceGrad η x i) =
      ell * (∫ x in unitCube, u x * φ x) := by
    simp_rw [hder]
    rw [show (fun x => u x * (ell * φ x)) = (fun x => ell * (u x * φ x)) by
      funext x; ring, integral_const_mul]
  rw [hleft] at he
  have hp : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hDu : MemLp (fun x => Du x i) (ENNReal.ofReal 2) (volume.restrict unitCube) := by
    simpa using hu.2.2.2.1 i
  have hm : MemLp η (ENNReal.ofReal 2) (volume.restrict unitCube) := by
    simpa using AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On hη.continuous
  have hc := integral_mul_norm_le_Lp_mul_Lq hp hDu hm
  have hb : |∫ x in unitCube, Du x i * η x| ≤
      Real.sqrt (∫ x in unitCube, (Du x i) ^ 2) *
        Real.sqrt (∫ x in unitCube, η x ^ 2) := by
    have hn := norm_integral_le_integral_norm (f := fun x => Du x i * η x)
      (μ := volume.restrict unitCube)
    have hcs : (∫ x in unitCube, |Du x i| * |η x|) ≤
        Real.sqrt (∫ x in unitCube, (Du x i) ^ 2) *
          Real.sqrt (∫ x in unitCube, η x ^ 2) := by
      simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hc
    exact (show |∫ x in unitCube, Du x i * η x| ≤
      ∫ x in unitCube, |Du x i| * |η x| by
        simpa only [Real.norm_eq_abs, abs_mul] using hn).trans hcs
  apply (le_div_iff₀ hell).mpr
  have hs : ell * |∫ x in unitCube, u x * φ x| ≤
      Real.sqrt (∫ x in unitCube, (Du x i) ^ 2) *
        Real.sqrt (∫ x in unitCube, η x ^ 2) := by
    rw [← abs_of_pos hell, ← abs_mul, he, abs_neg]
    exact hb
  simpa only [mul_comm] using hs

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual velocity seminorm controls the drift arrays used in the finite energy estimate.
The constants remain explicit, so the molecular radius can be chosen before the jet order. -/

open AVRegularity.Velocity.Port.Section2FlowHigherDerivative

theorem drift_array_norm_le_of_snorm {v : Vec 2 → Vec 2} (j : ℕ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : AVenhance.FaaDiBruno.snorm v j R ≤ ENNReal.ofReal C) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient v) j x‖ ≤
      ((Fintype.card (DerivativeWord2 j) : ℝ) * ‖Weighted.driftCoefficientEmbedding‖) *
        ((2 : ℝ) ^ j * (C * j.factorial * R ^ j / (j + 1 : ℝ) ^ 2)) := by
  have hp : 0 ≤ C * j.factorial * R ^ j / (j + 1 : ℝ) ^ 2 := by positivity
  have hi : ‖iteratedFDeriv ℝ j v x‖ ≤
      (2 : ℝ) ^ j * (C * j.factorial * R ^ j / (j + 1 : ℝ) ^ 2) := by
    apply AVenhance.Infra.Section4.amnr_multilinear_norm_le_two_pow_basis j _ hp
    intro w
    have hw := orderedPartial_pointwise_of_snorm hv hR hC hs w x
    rw [orderedPartial_eq_iteratedFDeriv hv x w] at hw
    exact hw
  exact (Weighted.driftCoefficient_array_norm_le_iterated v j
    (hv.of_le (by simp)) x).trans
      (mul_le_mul_of_nonneg_left hi (by positivity))

theorem drift_array_norm_le_geometric {v : Vec 2 → Vec 2} (j : ℕ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : AVenhance.FaaDiBruno.snorm v j R ≤ ENNReal.ofReal C) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient v) j x‖ ≤
      ‖Weighted.driftCoefficientEmbedding‖ * C * (4 * R) ^ j * j.factorial := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hd : 1 ≤ (j + 1 : ℝ) ^ 2 := by nlinarith only [hj, sq_nonneg (j : ℝ)]
  have hdiv : C * j.factorial * R ^ j / (j + 1 : ℝ) ^ 2 ≤
      C * j.factorial * R ^ j := div_le_self (by positivity) hd
  have hcard : (Fintype.card (DerivativeWord2 j) : ℝ) = (2 : ℝ) ^ j := by
    simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ ((Fintype.card (DerivativeWord2 j) : ℝ) * ‖Weighted.driftCoefficientEmbedding‖) *
        ((2 : ℝ) ^ j * (C * j.factorial * R ^ j / (j + 1 : ℝ) ^ 2)) :=
      drift_array_norm_le_of_snorm j hv hR hC hs x
    _ ≤ ((2 : ℝ) ^ j * ‖Weighted.driftCoefficientEmbedding‖) *
        ((2 : ℝ) ^ j * (C * j.factorial * R ^ j)) := by
      rw [hcard]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv (by positivity))
        (by positivity)
    _ = _ := by
      rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! Reuse bounded coefficient multiplication for the literal L2 material drift source. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def literalDriftSource (v : ℝ → Vec 2 → Vec 2) (hc : ∀ t, Continuous (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t x, ‖v t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) (t : ℝ) : ComponentL2 (volume.restrict unitCube) E :=
  -boundedCoefficientL2 (U := unitCube)
    (driftFiberCoefficient (E := E) (v t)) (driftFiberCoefficient_continuous (E := E) (v t) (hc t))
    (2 * V) (mul_nonneg (by norm_num) hV)
    (driftFiberCoefficient_norm_le (E := E) (v t) hV (hb t))
    (torusH1GradientL2CLM (E := E) (w t))

theorem literalDriftSource_time_memLp (v : ℝ → Vec 2 → Vec 2)
    (hv : Continuous (Function.uncurry v)) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t x, ‖v t x‖ ≤ V) (w : ℝ → TorusHk 1 E) {a b : ℝ}
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (literalDriftSource v
      (fun _t => hv.comp (continuous_const.prodMk continuous_id)) V hV hb w)
      2 (volume.restrict (Set.Icc a b)) := by
  let C : ℝ → Vec 2 → (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] E := fun t => driftFiberCoefficient (E := E) (v t)
  have hC : Measurable (Function.uncurry C) :=
    (driftFiberCoefficient_joint_continuous (E := E) hv).measurable
  have hvslice (t : ℝ) : Continuous (v t) :=
    hv.comp (continuous_const.prodMk continuous_id)
  have hc : ∀ t, Continuous (C t) := fun t =>
    driftFiberCoefficient_continuous (E := E) (v t) (hvslice t)
  have hg :=  (torusH1GradientL2CLM (E := E)).comp_memLp' hw
  have hm :=  boundedCoefficientL2_time_memLp (volume.restrict (Set.Icc a b)) C hC hc
    (2 * V) (mul_nonneg (by norm_num) hV)
    (fun t => driftFiberCoefficient_norm_le (E := E) (v t) hV (hb t))
    (fun t => torusH1GradientL2CLM (E := E) (w t))
    (by simpa only [Function.comp_def] using hg)
  change MemLp (fun t => literalDriftSource v
    (fun _t => hv.comp (continuous_const.prodMk continuous_id)) V hV hb w t)
    2 (volume.restrict (Set.Icc a b))
  simpa only [literalDriftSource, C, Pi.neg_apply] using! hm.neg

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Pointwise control on complex native base labels from the literal context mode budget. -/

theorem native_complex_context_norm_le
    (D : OCData) (b : ℝ) (hb : 0 < b) (j₀ i : ℕ) (p : {p : ℤ // Odd p})
    (hε : 0 < D.eps (i - 1)) (f : GenSort.Sem .ctx)
    (F : {p : ℤ // Odd p} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D b j₀ i p.1 f (F p))
    (ha : ∀ Y : Vec 2, IsAdmissibleChain D b j₀ i p.1 ⟨i - 1, [p.1], Y, []⟩)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p.1)
    (mres : ℝ) (hm : 0 ≤ mres) (hm2 : mres ≤ 2) (L : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ)
    (z : Fin 2 → ℂ) (hreal : ∀ a, (z a).im = 0)
    (hp : ∀ Y : Vec 2, Function.Periodic (fun s : ℝ => F p ⟨i - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun k : Fin 0 => Fin.elim0 k),
        z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) 1)
    (Z : Fin 2 → ℂ)
    (hZ : (∑ a, |(Z a).im|) < (1 + mres / 4) * (1 / 100) * D.eps (i - 1)) :
    ‖F p ⟨i - 1, [p.1]⟩ 0 t (Z, (fun k : Fin 0 => Fin.elim0 k), z)‖ ≤ θ := by
  let R := (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (i - 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRm : (1 + mres / 4) * (1 / 100) * D.eps (i - 1) ≤ R := by
    dsimp [R]
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith only [hm2]
  have hZ' : (∑ a, |(Z a).im|) < R := hZ.trans_le hRm
  let B := fun (W : Fin 2 → ℂ) (s : ℝ) => F p ⟨i - 1, [p.1]⟩ 0 t
    (W, (fun k : Fin 0 => Fin.elim0 k),
      z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
  have hphaseReal (s : ℝ) : ∀ a,
      ((z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) a).im = 0 := by
    intro a
    simp only [Pi.add_apply, Complex.add_im, hreal, zero_add]
    split_ifs <;> simp only [Complex.ofReal_im, Complex.zero_im]
  have hB : ∀ s, DifferentiableOn ℂ (fun W => B W s)
      {W : Fin 2 → ℂ | (∑ a, |(W a).im|) < R} := fun s =>
    native_holomorphic_base_slice D b hb j₀ i p.1 f (F p) hF t ht _ (hphaseReal s)
  have hper := phase_periodic_on_complex_base_of_real_periodic R hR B hB hp Z hZ'
  let x : ChainParamsC 0 := (Z, (fun k : Fin 0 => Fin.elim0 k), z)
  have hx : x ∈ carrierC D b ⟨i - 1, [p.1]⟩ 0 mres := by
    refine ⟨hZ, ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · change |(z (transverseIndex p.1)).im| < (3 + mres / 4) * b
      rw [hreal, abs_zero]
      positivity
  let g : ℝ → ChainParamsC 0 := fun s =>
    (Z, (fun k : Fin 0 => Fin.elim0 k),
      z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
  have hg : Continuous g := by
    have hh : Continuous (fun s : ℝ =>
        z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) := by
      apply continuous_const.add
      apply continuous_pi
      intro a
      by_cases ha : a = transverseIndex p.1
      · simpa only [ite_eq_left ha] using Complex.continuous_ofReal
      · simp only [ite_eq_right ha]
        exact continuous_const
    exact continuous_const.prodMk (continuous_const.prodMk hh)
  have hmaps : MapsTo g univ (carrierC D b ⟨i - 1, [p.1]⟩ 0 2) := by
    intro s _
    refine ⟨hZ', ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · change |((z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
        (transverseIndex p.1)).im| < (3 + (2 : ℝ) / 4) * b
      rw [hphaseReal s, abs_zero]
      positivity
  have hc : Continuous (fun s => F p ⟨i - 1, [p.1]⟩ 0 t (g s)) :=
    continuousOn_univ.mp ((hF.1 ⟨i - 1, [p.1]⟩ 0 t ht).continuousOn.comp hg.continuousOn hmaps)
  exact finalPhase_value_norm_le_contextSize D b hb.le j₀ i F mres L p ⟨i - 1, [p.1]⟩ 0
    ⟨⟨i - 1, [p.1], 0, []⟩, ha 0, rfl, rfl⟩ t ht x hx hreal hc hper θ hθ hsize

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! The bounded-coefficient drift source represents the actual weak carrier gradients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem literalDriftSource_raw_ae (v : ℝ → Vec 2 → Vec 2) (hc : ∀ t, Continuous (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t x, ‖v t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) (t : ℝ) :
    literalDriftSource v hc V hV hb w t =ᵐ[volume.restrict unitCube]
      fun x => -(∑ k : Fin 2, v t x k •
        (w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
  have hC : Continuous (driftFiberCoefficient (E := E) (v t)) := by
    change Continuous (fun x => driftFiberCoefficient (E := E) (v t) x)
    simp only [driftFiberCoefficient_eq_sum]
    apply continuous_finsetSum
    intro k _
    exact ((continuous_apply k).comp (hc t)).smul continuous_const
  let q := boundedCoefficientL2 (driftFiberCoefficient (E := E) (v t)) hC (2 * V)
    (mul_nonneg (by norm_num) hV) (driftFiberCoefficient_norm_le (v t) hV (hb t))
    (torusH1GradientL2CLM (E := E) (w t))
  have hq := boundedCoefficientL2_ae (driftFiberCoefficient (E := E) (v t)) hC (2 * V)
    (mul_nonneg (by norm_num) hV) (driftFiberCoefficient_norm_le (v t) hV (hb t))
    (torusH1GradientL2CLM (E := E) (w t))
  change (-q : ComponentL2 (volume.restrict unitCube) E) =ᵐ[_] _
  filter_upwards [Lp.coeFn_neg q, hq, torusRawTestGradient_ae (w t)] with x hn hx hg
  rw [hn]
  change -q x = _
  change q x = driftFiberCoefficient (E := E) (v t) x
    ((torusH1GradientL2CLM (E := E) (w t)) x) at hx
  rw [hx, ← hg, driftFiberCoefficient_apply]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! A comparison-window velocity bound suffices for the literal time-L2 drift source. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def windowVelocity (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t => v (Set.projIcc a b hab t)

theorem windowVelocity_continuous {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Continuous (Function.uncurry v)) : Continuous (Function.uncurry (windowVelocity a b hab v)) :=
  hv.comp (((continuous_subtype_val.comp (continuous_projIcc (a := a) (b := b) (h := hab))).comp continuous_fst).prodMk continuous_snd)

def windowDriftSource {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Continuous (Function.uncurry v)) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) : ℝ → ComponentL2 (volume.restrict unitCube) E :=
  literalDriftSource (windowVelocity a b hab v)
    (fun _t => (windowVelocity_continuous hab v hv).comp (continuous_const.prodMk continuous_id))
    V hV (fun t => hb _ (Set.projIcc a b hab t).property) w

theorem windowDriftSource_time_memLp {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Continuous (Function.uncurry v)) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (windowDriftSource hab v hv V hV hb w) 2 (volume.restrict (Set.Icc a b)) :=
  literalDriftSource_time_memLp (windowVelocity a b hab v)
    (windowVelocity_continuous hab v hv) V hV _ w hw

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance Filter Topology
open AVRegularity.CycleReference AVRegularity.EntryScales
namespace AVRegularity.Construction.Preservation.Buffer

/-! Both molecular Fourier prices become small uniformly over every admissible band chain. -/

theorem band_preparation_radius_decay {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ c₀ cr : ℝ,
      0 < c₀ → 0 < cr → ∀ η : ℝ, 0 < η → ∃ m₀ : ℕ, 2 ≤ m₀ ∧
        ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
          ∀ m : ℕ, m₀ ≤ m → m ≤ M →
          let ρ := c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m))
          ρ / (cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) ≤ η ∧ ρ ≤ η := by
  obtain ⟨Λ₀, hΛ₀, hratio⟩ := band_preparation_radius_ratio_power hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ c₀ cr hc₀ hcr η hη
  obtain ⟨A, hA, hbound⟩ := hratio Λ hΛ c₀ cr hc₀ hcr
  have h128 := hΛ₀.trans hΛ
  have hp := preparation_radius_gap_pos hα0 hα1 hs0 hs1 hq
  have hpow := (Real.continuousAt_rpow_const 0 (q - (1 + ocC α q))
    (Or.inr hp.le)).tendsto.comp (epsilon_parent_tendsto_zero hq.1 h128)
  rw [Real.zero_rpow hp.ne'] at hpow
  have hlim : Tendsto (fun m : ℕ => A * ocEpsilon q Λ (m - 1) ^
      (q - (1 + ocC α q))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using tendsto_const_nhds.mul hpow
  have hsmall := hlim.eventually (eventually_le_nhds hη)
  have hlimρ : Tendsto (fun m : ℕ => c₀ * ocEpsilon q Λ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (epsilon_tendsto_zero hq.1 h128)
  have hsmallρ := hlimρ.eventually (eventually_le_nhds hη)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hsmall.and hsmallρ)
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  intro M κ hκ m hm hmM
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hmn : n ≤ m := (le_max_right _ _).trans hm
  exact ⟨(hbound M κ hκ m hm2 hmM).trans (hn m hmn).1,
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀.le).trans (hn m hmn).2⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! Literal bounded contour data yield smooth base parameters with uniform finite jets. -/

open CycleComparison.Lift

theorem localized_cauchy_integral_regular_and_jet_bound
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g : ℝ × ℝ → ℂ), Measurable g → ∀ M : ℝ, 0 ≤ M →
        (∀ p, ‖g p‖ ≤ M) →
        ContDiff ℝ (n : ℕ∞) (fun x => ∫ p, g p • localizedCauchyKernel R χ (p, x) ∂μ) ∧
        ∀ j ≤ n, ∀ x : Vec 2,
          ‖iteratedFDeriv ℝ j (fun x => ∫ p, g p • localizedCauchyKernel R χ (p, x) ∂μ) x‖ ≤
            (2 : ℝ) ^ j * (C j * M * μ.real Set.univ) := by
  have hk := localized_cauchy_kernel_contDiff R hR χ hχ hb
  obtain ⟨C, hC⟩ := Classical.axiomOfChoice
    (fun j => localized_cauchy_kernel_exists_global_jet_bound R hR χ hχ hb hzero hout j)
  refine ⟨C, fun j => (hC j).1, ?_⟩
  intro g hg M hM hbound
  let f : (ℝ × ℝ) → Vec 2 → ℂ := fun p x => g p • localizedCauchyKernel R χ (p, x)
  have hks (p : ℝ × ℝ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => localizedCauchyKernel R χ (p, x)) :=
    hk.comp (contDiff_const.prodMk contDiff_id)
  have hs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (f p) :=
    ((hks p).const_smul (g p)).of_le (by simp)
  have hm (x : Vec 2) : Measurable (fun p => f p x) :=
    hg.smul ((hk.continuous.comp (continuous_id.prodMk continuous_const)).measurable)
  have hjets : ∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (f p) x‖ ≤ C j * M := by
    intro j _ p x
    rw [show f p = fun y => g p • localizedCauchyKernel R χ (p, y) from rfl,
      iteratedFDeriv_const_smul_apply' ((hks p).contDiffAt.of_le (by simp)), norm_smul]
    calc
      _ ≤ M * C j := mul_le_mul (hbound p) ((hC j).2 p.1 p.2 x)
        (norm_nonneg _) hM
      _ = C j * M := mul_comm _ _
  refine ⟨parameter_integral_contDiff μ n f hm hs (fun j => C j * M) hjets, ?_⟩
  intro j hj x
  exact parameter_integral_iteratedFDeriv_norm_le μ n f hm hs
    (fun j => C j * M) hjets j hj x

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual transverse profiles on complex native labels retain the exponential fast-jet budget. -/

theorem native_complex_phase_regular_and_jet_bound
    (D : OCData) (b : ℝ) (hb : 0 < b) (j₀ i : ℕ) (p : {p : ℤ // Odd p})
    (hε : 0 < D.eps (i - 1)) (f : GenSort.Sem .ctx)
    (F : {p : ℤ // Odd p} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D b j₀ i p.1 f (F p))
    (ha : ∀ Y : Vec 2, IsAdmissibleChain D b j₀ i p.1 ⟨i - 1, [p.1], Y, []⟩)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p.1)
    (mres : ℝ) (hm : 0 ≤ mres) (hm2 : mres ≤ 2) (L : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ)
    (z : Fin 2 → ℂ) (hreal : ∀ a, (z a).im = 0)
    (hp : ∀ Y : Vec 2, Function.Periodic (fun s : ℝ => F p ⟨i - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun k : Fin 0 => Fin.elim0 k),
        z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) 1)
    (Z : Fin 2 → ℂ)
    (hZ : (∑ a, |(Z a).im|) < (1 + mres / 4) * (1 / 100) * D.eps (i - 1))
    (q : ℕ) :
    ContDiff ℝ q (fun s : ℝ => F p ⟨i - 1, [p.1]⟩ 0 t
      (Z, (fun k : Fin 0 => Fin.elim0 k),
        z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) ∧
      ∀ j ≤ q, ∀ s : ℝ,
        ‖iteratedDeriv j (fun s : ℝ => F p ⟨i - 1, [p.1]⟩ 0 t
          (Z, (fun k : Fin 0 => Fin.elim0 k),
            z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) s‖ ≤
              ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ := by
  let R := (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (i - 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRm : (1 + mres / 4) * (1 / 100) * D.eps (i - 1) ≤ R := by
    dsimp [R]
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith only [hm2]
  have hZ' : (∑ a, |(Z a).im|) < R := hZ.trans_le hRm
  let B := fun (W : Fin 2 → ℂ) (s : ℝ) => F p ⟨i - 1, [p.1]⟩ 0 t
    (W, (fun k : Fin 0 => Fin.elim0 k),
      z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
  have hphaseReal (s : ℝ) : ∀ a,
      ((z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) a).im = 0 := by
    intro a
    simp only [Pi.add_apply, Complex.add_im, hreal, zero_add]
    split_ifs <;> simp only [Complex.ofReal_im, Complex.zero_im]
  have hB : ∀ s, DifferentiableOn ℂ (fun W => B W s)
      {W : Fin 2 → ℂ | (∑ a, |(W a).im|) < R} := fun s =>
    native_holomorphic_base_slice D b hb j₀ i p.1 f (F p) hF t ht _ (hphaseReal s)
  have hper := phase_periodic_on_complex_base_of_real_periodic R hR B hB hp Z hZ'
  let x : ChainParamsC 0 := (Z, (fun k : Fin 0 => Fin.elim0 k), z)
  have hx : x ∈ carrierC D b ⟨i - 1, [p.1]⟩ 0 mres := by
    refine ⟨hZ, ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · change |(z (transverseIndex p.1)).im| < (3 + mres / 4) * b
      rw [hreal, abs_zero]
      positivity
  let g : ℝ → ChainParamsC 0 := fun s =>
    (Z, (fun k : Fin 0 => Fin.elim0 k),
      z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
  have hg : Continuous g := by
    have hh : Continuous (fun s : ℝ =>
        z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) := by
      apply continuous_const.add
      apply continuous_pi
      intro a
      by_cases ha : a = transverseIndex p.1
      · simpa only [ite_eq_left ha] using Complex.continuous_ofReal
      · simp only [ite_eq_right ha]
        exact continuous_const
    exact continuous_const.prodMk (continuous_const.prodMk hh)
  have hmaps : MapsTo g univ (carrierC D b ⟨i - 1, [p.1]⟩ 0 2) := by
    intro s _
    refine ⟨hZ', ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · change |((z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
        (transverseIndex p.1)).im| < (3 + (2 : ℝ) / 4) * b
      rw [hphaseReal s, abs_zero]
      positivity
  have hc : Continuous (fun s => F p ⟨i - 1, [p.1]⟩ 0 t (g s)) :=
    continuousOn_univ.mp ((hF.1 ⟨i - 1, [p.1]⟩ 0 t ht).continuousOn.comp hg.continuousOn hmaps)
  have hcoeff (h : ℤ) :
      ‖CycleComparison.Lift.unitProfileFourierCoeff (fun s => F p ⟨i - 1, [p.1]⟩ 0 t (g s)) h‖ₑ ≤
        ctxModeSup D b j₀ i p.1 (F p) mres h := by
    have he : CycleComparison.Lift.unitProfileFourierCoeff
        (fun s => F p ⟨i - 1, [p.1]⟩ 0 t (g s)) h =
        finalPhaseCoeff (transverseIndex p.1) (F p ⟨i - 1, [p.1]⟩ 0 t) x h :=
      (finalPhaseCoeff_eq_fourierCoeffOn (transverseIndex p.1)
        (F p ⟨i - 1, [p.1]⟩ 0 t) x h).symm
    rw [he]
    exact finalPhaseCoeff_enorm_le_ctxModeSup D b j₀ i p.1 (F p) mres h ⟨i - 1, [p.1]⟩ 0
      ⟨⟨i - 1, [p.1], 0, []⟩, ha 0, rfl, rfl⟩ t ht x hx hreal
  exact context_profile_regular_and_jet_bound D b hb j₀ i F mres L p
    (fun s => F p ⟨i - 1, [p.1]⟩ 0 t (g s)) hc hper hcoeff θ hθ hsize q

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! On the actual comparison window, the extended source is exactly the original drift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem windowDriftSource_raw_ae {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Continuous (Function.uncurry v)) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (w : ℝ → TorusHk 1 E) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    windowDriftSource hab v hv V hV hb w t =ᵐ[volume.restrict unitCube]
      fun x => -(∑ k : Fin 2, v t x k •
        (w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
  have hr := literalDriftSource_raw_ae (windowVelocity a b hab v)
    (fun _t => (windowVelocity_continuous hab v hv).comp (continuous_const.prodMk continuous_id))
    V hV (fun t => hb _ (Set.projIcc a b hab t).property) w t
  change windowDriftSource hab v hv V hV hb w t =ᵐ[_] _ at hr
  simpa only [windowVelocity, Set.projIcc_of_mem hab ht] using hr

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! Slow contour kernels and fast profile jets combine before integration. -/

open CycleComparison.Lift

theorem localized_variable_cauchy_regular_and_jet_bound
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (n : ℕ)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ Q : ℕ → ℝ, (∀ j, 0 ≤ Q j) ∧
      ∀ (f : (ℝ × ℝ) → Vec 2 → ℂ),
        (∀ x, Measurable (fun p => f p x)) →
        (∀ p, ContDiff ℝ (n : ℕ∞) (f p)) → ∀ M : ℝ, 0 ≤ M →
        (∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (f p) x‖ ≤ A j * M) →
        ContDiff ℝ (n : ℕ∞) (fun x => ∫ p, f p x * localizedCauchyKernel R χ (p, x) ∂μ) ∧
        ∀ j ≤ n, ∀ x,
          ‖iteratedFDeriv ℝ j (fun x => ∫ p, f p x * localizedCauchyKernel R χ (p, x) ∂μ) x‖ ≤
            (2 : ℝ) ^ j * (Q j * M * μ.real Set.univ) := by
  choose C hC hCb using fun j =>
    localized_cauchy_kernel_exists_global_jet_bound R hR χ hχ hb hzero hout j
  let Q : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (j + 1),
    (j.choose l : ℝ) * A l * C (j - l)
  have hQ (j : ℕ) : 0 ≤ Q j := by
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (mul_nonneg (by positivity) (hA l)) (hC (j - l))
  refine ⟨Q, hQ, ?_⟩
  intro f hm hs M hM hf
  let g : (ℝ × ℝ) → Vec 2 → ℂ := fun p x => f p x * localizedCauchyKernel R χ (p, x)
  have hk := localized_cauchy_kernel_contDiff R hR χ hχ hb
  have hks (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞)
      (fun x : Vec 2 => localizedCauchyKernel R χ (p, x)) :=
    (hk.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hgs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (g p) := (hs p).mul (hks p)
  have hgm (x : Vec 2) : Measurable (fun p => g p x) :=
    (hm x).mul ((hk.continuous.comp (continuous_id.prodMk continuous_const)).measurable)
  have hgb : ∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (g p) x‖ ≤ Q j * M := by
    intro j hj p x
    apply (norm_iteratedFDeriv_mul_le (hs p) (hks p) x (by exact_mod_cast hj)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) * (A l * M) * C (j - l) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l ≤ n := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hj
        have hAl := hA l
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left (hf l hl' p x) (by positivity))
          (hCb (j - l) p.1 p.2 x) (norm_nonneg _) (by positivity)
      _ = Q j * M := by
        dsimp only [Q]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
  exact ⟨parameter_integral_contDiff μ n g hgm hgs (fun j => Q j * M) hgb,
    fun j hj x => parameter_integral_iteratedFDeriv_norm_le μ n g hgm hgs
      (fun j => Q j * M) hgb j hj x⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Finite native coefficient budgets make kernel Schur bounds monotone in time. -/

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


theorem kernelSchurMatrix_time_restrict {a b c d ρ ν : ℝ} {k D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b ρ ν k D (h := h) (Γ := Γ) (G := G))
    (hsub : Set.Icc c d ⊆ Set.Icc a b) (i j : ι) :
    kernelSchurMatrix ν ρ P.π k D c d P.c P.r P.C P.B i j ≤
      kernelSchurMatrix ν ρ P.π k D a b P.c P.r P.C P.B i j := by
  unfold kernelSchurMatrix
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Finset.sum_le_sum
  intro α _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro q _
  have hq := Finset.mem_Icc.mp q.property
  have hc : 0 ≤ P.c (q.1 - 2) := (P.hS i j α).2.2.1 _ (by omega)
  apply div_le_div_of_nonneg_right _
    (mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr i j α).le _))
  apply mul_le_mul_of_nonneg_right _ hc
  exact ENNReal.toReal_mono (P.hB_fin i j α q)
    (CycleJointProofs.coefficientSeminorm_time_mono ρ k c d a b hsub _)

theorem kernelSchurBound_time_restrict {a b c d ρ ν : ℝ} {k D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b ρ ν k D (h := h) (Γ := Γ) (G := G))
    (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    SchurBound P.θ (kernelSchurMatrix ν ρ P.π k D c d P.c P.r P.C P.B) := by
  constructor
  · intro i
    exact (Finset.sum_le_sum fun j _ => kernelSchurMatrix_time_restrict P hsub i j).trans
      (P.hschur.1 i)
  · intro j
    exact (Finset.sum_le_sum fun i _ => kernelSchurMatrix_time_restrict P hsub i j).trans
      (P.hschur.2 j)

end AVRegularity.Construction.Preservation.Buffer
end
end
