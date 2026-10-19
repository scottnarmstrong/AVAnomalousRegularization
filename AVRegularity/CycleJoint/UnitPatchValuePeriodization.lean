-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneH1Average
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
public import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
public import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Bounded scalar cutoffs converging to one approximate every native plane L2 class strongly. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem planeScalarMultiplier_tendsto_one (c : ℕ → Vec 2 → ℝ)
    (hc : ∀ n, Continuous (c n)) (hb : ∀ n x, 0 ≤ c n x ∧ c n x ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => c n x) atTop (𝓝 1))
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => planeScalarMultiplier (c n) (hc n) (by norm_num : (0 : ℝ) ≤ 1)
      (fun x => by rw [abs_of_nonneg (hb n x).1]; exact (hb n x).2) u) atTop (𝓝 u) := by
  let L := fun n => planeScalarMultiplier (E := E) (c n) (hc n)
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => by rw [abs_of_nonneg (hb n x).1]; exact (hb n x).2)
  have ha n : (L n u : Vec 2 → E) =ᵐ[volume] fun x => c n x • u x :=
    planeScalarMultiplier_ae _ _ _ _ _
  have hf n : MemLp (fun x => c n x • u x) 2 volume := (Lp.memLp (L n u)).ae_eq (ha n)
  have hg := Lp.memLp u
  have ht := planeLp_tendsto_of_dominated_normSq (fun n x => c n x • u x)
    (fun x => u x) hf hg (fun x => ‖u x‖ ^ 2) hg.norm.integrable_sq
    (fun n => Filter.Eventually.of_forall fun x => by
      have hab : |c n x - 1| ≤ 1 := abs_le.mpr ⟨by linarith [(hb n x).1], by linarith [(hb n x).2]⟩
      have he : c n x • u x - u x = (c n x - 1) • u x := by
        rw [sub_smul, one_smul]
      rw [he]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hab)
    (Filter.Eventually.of_forall fun x => by
      simpa only [one_smul] using (hlim x).smul_const (u x))
  have he n : (hf n).toLp (fun x => c n x • u x) = L n u := by
    apply Lp.ext
    exact (hf n).coeFn_toLp.trans (ha n).symm
  simpa only [he, Lp.toLp_coeFn] using ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! The source preparation cutoff and its directional derivative periodize to one and zero. -/

theorem unitPatch_derivative_translate (ζ : ℝ → ℝ) (n : Fin 2 → ℤ) (x v : Vec 2) :
    fderiv ℝ (spatialPatchCutoff ζ 1 0) (x + AVenhance.latticeShift n) v =
      fderiv ℝ (spatialPatchCutoff ζ 1 (-n)) x v := by
  have he : (fun y => spatialPatchCutoff ζ 1 0 (y + AVenhance.latticeShift n)) =
      spatialPatchCutoff ζ 1 (-n) := by
    funext y
    have hn : (fun i => (0 : ℤ) - (1 : ℤ) * n i) = -n := by
      funext i
      simp only [one_mul, zero_sub, Pi.neg_apply]
    exact (spatialPatchCutoff_translate ζ 1 0 n y).trans (congrArg (fun k => spatialPatchCutoff ζ 1 k y) hn)
  have hd := congrArg (fun f : Vec 2 → ℝ => fderiv ℝ f x v) he
  simpa only [fderiv_comp_add_right] using hd

theorem latticePeriodization_unitPatch {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (x : Vec 2) :
    latticePeriodization (spatialPatchCutoff ζ 1 0) x = 1 := by
  have he := (Equiv.neg (Fin 2 → ℤ)).tsum_eq (fun n => spatialPatchCutoff ζ 1 n x)
  calc
    _ = ∑' n : Fin 2 → ℤ, spatialPatchCutoff ζ 1 (-n) x := by
      apply tsum_congr
      intro n
      have hn : (fun i => (0 : ℤ) - (1 : ℤ) * n i) = -n := by
        funext i
        simp only [one_mul, zero_sub, Pi.neg_apply]
      exact (spatialPatchCutoff_translate ζ 1 0 n x).trans (congrArg (fun k => spatialPatchCutoff ζ 1 k x) hn)
    _ = ∑' n : Fin 2 → ℤ, spatialPatchCutoff ζ 1 n x := he
    _ = 1 := spatialPatchCutoff_partition hζ 1 x

theorem latticePeriodization_unitPatch_derivative {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (x v : Vec 2) :
    latticePeriodization (fun y => fderiv ℝ (spatialPatchCutoff ζ 1 0) y v) x = 0 := by
  have he := (Equiv.neg (Fin 2 → ℤ)).tsum_eq
    (fun n => fderiv ℝ (spatialPatchCutoff ζ 1 n) x v)
  calc
    _ = ∑' n : Fin 2 → ℤ, fderiv ℝ (spatialPatchCutoff ζ 1 (-n)) x v :=
      tsum_congr (fun n => unitPatch_derivative_translate ζ n x v)
    _ = ∑' n : Fin 2 → ℤ, fderiv ℝ (spatialPatchCutoff ζ 1 n) x v := he
    _ = 0 := unitPatch_directional_derivative_partition hζ x v

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual native lift superposition gives literal coupled source-row superposition, retaining the complete coefficient array. -/

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
  {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_curve_superposition (μ : Measure ℝ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hadd : ∀ x y i, w (x + y) i =ᵐ[μ] fun t => w x i t + w y i t)
    (hsmul : ∀ (c : ℝ) x i, w (c • x) i =ᵐ[μ] fun t => c • w x i t) :
    (∀ x y i, ∀ᵐ t ∂μ,
      planeRawCouplingFlux K D t A (fun j => w (x + y) j t) i =ᵐ[volume]
        fun z => planeRawCouplingFlux K D t A (fun j => w x j t) i z +
          planeRawCouplingFlux K D t A (fun j => w y j t) i z) ∧
    ∀ (c : ℝ) x i, ∀ᵐ t ∂μ,
      planeRawCouplingFlux K D t A (fun j => w (c • x) j t) i =ᵐ[volume]
        fun z => c • planeRawCouplingFlux K D t A (fun j => w x j t) i z := by
  constructor
  · intro x y i
    have hall : ∀ᵐ t ∂μ, ∀ j, w (x + y) j t = w x j t + w y j t :=
      ae_all_iff.mpr (hadd x y)
    filter_upwards [hall] with t ht
    have heq : (fun j => w (x + y) j t) = (fun j => w x j t) + (fun j => w y j t) :=
      funext ht
    rw [heq]
    exact planeRawCouplingFlux_add_ae K D t A (fun j => w x j t) (fun j => w y j t) i
  · intro c x i
    have hall : ∀ᵐ t ∂μ, ∀ j, w (c • x) j t = c • w x j t :=
      ae_all_iff.mpr (hsmul c x)
    filter_upwards [hall] with t ht
    have heq : (fun j => w (c • x) j t) = (fun j => c • w x j t) := funext ht
    rw [heq]
    exact planeRawCouplingFlux_smul_ae K D c t A (fun j => w x j t) i

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Triangle inequality and the exact order-zero readout of the mass norm `massNormSq`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusMassNorm_triangle (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (f g : ∀ i, TorusHk (K i) (h i)) :
    Real.sqrt (massNormSq ρ π (fun i => (f i + g i).val)) ≤
      Real.sqrt (massNormSq ρ π (fun i => (f i).val)) +
        Real.sqrt (massNormSq ρ π (fun i => (g i).val)) := by
  change Real.sqrt (massNormSq ρ π (fun i => ((f + g) i).val)) ≤ _
  rw [← massWeightedCarrierCLM_norm K ρ π hπ (f + g), map_add,
    ← massWeightedCarrierCLM_norm K ρ π hπ f,
    ← massWeightedCarrierCLM_norm K ρ π hπ g]
  exact norm_add_le _ _

theorem massNormSq_order_zero (ρ : ℝ) (π : ι → ℝ)
    (f : ∀ i, TorusHk 0 (h i)) :
    massNormSq ρ π (fun i => (f i).val) = ∑ i, (π i)⁻¹ * ‖f i‖ ^ 2 := by
  unfold massNormSq
  exact Finset.sum_congr rfl (fun i _ => congrArg ((π i)⁻¹ * ·)
    (factorialNormSq_order_zero_measure _ ρ (f i).val))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Compact periodic testing recovers the torus pairing and cancels cutoff derivative fluxes. -/

theorem latticePeriodization_periodic_mul (g f : Vec 2 → ℝ)
    (hg : AVenhance.IsZ2Periodic g) (x : Vec 2) :
    latticePeriodization (fun y => g y * f y) x = g x * latticePeriodization f x := by
  change (∑' n : Fin 2 → ℤ, g (x + AVenhance.latticeShift n) *
    f (x + AVenhance.latticeShift n)) = _
  calc
    _ = ∑' n : Fin 2 → ℤ, g x * f (x + AVenhance.latticeShift n) :=
      tsum_congr (fun n => congrArg (fun a => a * f (x + AVenhance.latticeShift n)) (hg n x))
    _ = _ := tsum_mul_left

theorem integral_periodic_unitPatch {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (g : Vec 2 → ℝ) (hg : AVenhance.IsZ2Periodic g)
    (hi : Integrable (fun x => g x * spatialPatchCutoff ζ 1 0 x) volume) :
    (∫ x, g x * spatialPatchCutoff ζ 1 0 x ∂volume) =
      ∫ x in AVenhance.unitCube, g x ∂volume := by
  have he := integral_unitCube_periodization (fun x => g x * spatialPatchCutoff ζ 1 0 x) hi
  have hp (x : Vec 2) : latticePeriodization (fun y => g y * spatialPatchCutoff ζ 1 0 y) x = g x := by
    rw [latticePeriodization_periodic_mul g _ hg, latticePeriodization_unitPatch hζ, mul_one]
  simpa only [hp] using he.symm

theorem integral_periodic_unitPatch_derivative {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (g : Vec 2 → ℝ) (hg : AVenhance.IsZ2Periodic g) (v : Vec 2)
    (hi : Integrable (fun x => g x * fderiv ℝ (spatialPatchCutoff ζ 1 0) x v) volume) :
    (∫ x, g x * fderiv ℝ (spatialPatchCutoff ζ 1 0) x v ∂volume) = 0 := by
  have he := integral_unitCube_periodization
    (fun x => g x * fderiv ℝ (spatialPatchCutoff ζ 1 0) x v) hi
  have hp (x : Vec 2) : latticePeriodization
      (fun y => g y * fderiv ℝ (spatialPatchCutoff ζ 1 0) y v) x = 0 := by
    rw [latticePeriodization_periodic_mul g _ hg,
      latticePeriodization_unitPatch_derivative hζ, mul_zero]
  simpa only [hp, integral_zero] using he.symm

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The literal value readout of an affine cell pullback is composition with its spatial chart. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrierAffine_value_ae (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : PlaneHk Set.univ K E) :
    planeValue (planeCarrierAffine e he yc U) =ᵐ[volume]
      fun z => planeValue U (yc + e • z) := by
  have hout : (planeCarrierAffine e he yc U).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      planeValue (planeCarrierAffine e he yc U) := by
    rw [planeValue_eq_stored]
    rfl
  have hin : U.toFunction.jet (valueIndex2 K) =ᵐ[volume] planeValue U := by
    rw [planeValue_eq_stored]
    rfl
  have ha : (planeCarrierAffine e he yc U).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      fun z => U.toFunction.jet (valueIndex2 K) (yc + e • z) := by
    simpa only [valueIndex2, valueIndex, Fin.val_zero, pow_zero, one_smul] using
      planeCarrierAffine_jet_ae e he yc U (valueIndex2 K)
  exact hout.symm.trans (ha.trans ((plane_affine_quasiMeasurePreserving e he yc).ae_eq_comp hin))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Each actual ordered cell jet has its exact nonnegative weighted energy price. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K j : ℕ}

theorem planeJetOrder_affine_ae (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (planeCarrierAffine e he y U) j w =ᵐ[volume]
      fun z => e ^ j • planeJetOrder U j w (y + e • z) := by
  rw [planeJetOrder_eq_stored hj, planeJetOrder_eq_stored hj]
  exact planeCarrierAffine_jet_ae e he y U ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩

theorem planeCarrierAffine_order_energy (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (q : Vec 2 → ℝ) (U : PlaneHk Set.univ K E) (hj : j ≤ K) :
    (∫⁻ z : Vec 2, ENNReal.ofReal (q (y + e • z) *
      ∑ w : DerivativeWord2 j, ‖planeJetOrder (planeCarrierAffine e he y U) j w z‖ ^ 2)) =
      ENNReal.ofReal (‖e ^ j‖ ^ 2 * |(e ^ 2)⁻¹|) *
        ∫⁻ x : Vec 2, ENNReal.ofReal (q x * ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w x‖ ^ 2) := by
  have hall : ∀ᵐ z ∂volume, ∀ w : DerivativeWord2 j,
      planeJetOrder (planeCarrierAffine e he y U) j w z =
        e ^ j • planeJetOrder U j w (y + e • z) :=
    ae_all_iff.mpr (planeJetOrder_affine_ae e he y U hj)
  calc
    _ = ∫⁻ z : Vec 2, ENNReal.ofReal (‖e ^ j‖ ^ 2) *
        ENNReal.ofReal (q (y + e • z) *
          ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w (y + e • z)‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [hall] with z hz
      simp_rw [hz, norm_smul, mul_pow]
      rw [← Finset.mul_sum, mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ENNReal.ofReal (‖e ^ j‖ ^ 2) *
        (∫⁻ z : Vec 2, ENNReal.ofReal (q (y + e • z) *
          ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w (y + e • z)‖ ^ 2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      rw [lintegral_plane_affine e he y (fun x => ENNReal.ofReal
        (q x * ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w x‖ ^ 2)),
        ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Scalar matrix diffusion is linear in the matrix field, independently of the chosen multiplier budgets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeScalarDiffusion_scaling
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (hc : ∀ k j, Continuous (fun x => G x k j))
    (hcs : ∀ k j, Continuous (fun x => (c • G x) k j))
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hb : ∀ k j x, |G x k j| ≤ M) (hbs : ∀ k j x, |(c • G x) k j| ≤ N) :
    planeScalarDiffusion (E := E) (fun x => c • G x) hcs hN hbs =
      c • planeScalarDiffusion G hc hM hb := by
  apply ContinuousLinearMap.ext
  intro du
  apply PiLp.ext
  intro k
  apply Lp.ext
  filter_upwards [planeScalarDiffusion_ae (fun x => c • G x) hcs hN hbs du k,
    Lp.coeFn_smul c (planeScalarDiffusion G hc hM hb du k),
    planeScalarDiffusion_ae G hc hM hb du k] with x hs hm hg
  have he : (∑ j : Fin 2, (c • G x) k j • du j x) =
      c • ∑ j : Fin 2, G x k j • du j x := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  exact hs.trans (he.trans ((congrArg (fun z : E => c • z) hg).symm.trans hm.symm))
end

/-! Native transport is linear in the physical velocity, independently of its chosen bounds. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeScalarTransport_sub_apply
    (v w : Vec 2 → Vec 2)
    (hvc : ∀ k, Continuous (fun x => v x k))
    (hwc : ∀ k, Continuous (fun x => w x k))
    (hsc : ∀ k, Continuous (fun x => (v x - w x) k))
    {Mv Mw Ms : ℝ} (hMv : 0 ≤ Mv) (hMw : 0 ≤ Mw) (hMs : 0 ≤ Ms)
    (hvb : ∀ k x, |v x k| ≤ Mv) (hwb : ∀ k x, |w x k| ≤ Mw)
    (hsb : ∀ k x, |(v x - w x) k| ≤ Ms) (G : PlaneFluxL2 E) :
    planeScalarTransport (fun x => v x - w x) hsc hMs hsb G =
      planeScalarTransport v hvc hMv hvb G - planeScalarTransport w hwc hMw hwb G := by
  apply Lp.ext
  filter_upwards [planeScalarTransport_ae (fun x => v x - w x) hsc hMs hsb G,
    planeScalarTransport_ae v hvc hMv hvb G,
    planeScalarTransport_ae w hwc hMw hwb G,
    Lp.coeFn_sub (planeScalarTransport v hvc hMv hvb G)
      (planeScalarTransport w hwc hMw hwb G)] with x hs hv hw hsub
  rw [hs, hsub]
  change (∑ k : Fin 2, (v x - w x) k • G k x) =
    planeScalarTransport v hvc hMv hvb G x - planeScalarTransport w hwc hMw hwb G x
  rw [hv, hw]
  have he (k : Fin 2) : (v x - w x) k = v x k - w x k := rfl
  simp only [he, sub_smul, Finset.sum_sub_distrib]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Scalar time normalization agrees with the actual drift multiplier operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

/-- Scaling a velocity scales its Hilbert transport operator, independently of its norm budget. -/
theorem planeScalarTransport_smul (c : ℝ) (v : Vec 2 → Vec 2)
    (hc : ∀ k, Continuous (fun x => v x k))
    (hc' : ∀ k, Continuous (fun x => (c • v) x k))
    {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hb : ∀ k x, |v x k| ≤ M) (hb' : ∀ k x, |(c • v) x k| ≤ M') :
    planeScalarTransport (E := E) (c • v) hc' hM' hb' =
      c • planeScalarTransport v hc hM hb := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  have hl := planeScalarTransport_ae (c • v) hc' hM' hb' u
  have hr := Lp.coeFn_smul c (planeScalarTransport v hc hM hb u)
  have hv := planeScalarTransport_ae v hc hM hb u
  filter_upwards [hl, hr, hv] with x hlx hrx hvx
  change _ = (c • planeScalarTransport v hc hM hb u) x
  rw [hlx, hrx]
  simp only [Pi.smul_apply]
  rw [hvx]
  simp only [smul_eq_mul, Finset.smul_sum, smul_smul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The genuine cell pullback is linear and retains every higher-to-lower lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

def planeCarrierAffineLinearMap (K : ℕ) (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    PlaneHk Set.univ K E →ₗ[ℝ] PlaneHk Set.univ K E where
  toFun := planeCarrierAffine e he y
  map_add' := by
    intro U V
    apply Subtype.ext
    apply PiLp.ext
    intro a
    apply Lp.ext
    simp only [Measure.restrict_univ]
    filter_upwards [planeCarrierAffine_jet_ae e he y (U + V) a,
      planeCarrier_jet_add_ae (planeCarrierAffine e he y U) (planeCarrierAffine e he y V) a,
      planeCarrierAffine_jet_ae e he y U a, planeCarrierAffine_jet_ae e he y V a,
      (plane_affine_quasiMeasurePreserving e he y).ae_eq_comp (planeCarrier_jet_add_ae U V a)]
      with z huv hadd hu hv hsum
    change (planeCarrierAffine e he y (U + V)).toFunction.jet a z =
      (planeCarrierAffine e he y U + planeCarrierAffine e he y V).toFunction.jet a z
    simp only [Function.comp_def] at hsum
    rw [huv, hadd, hu, hv, hsum, smul_add]
  map_smul' := by
    intro c U
    apply Subtype.ext
    apply PiLp.ext
    intro a
    apply Lp.ext
    simp only [Measure.restrict_univ]
    filter_upwards [planeCarrierAffine_jet_ae e he y (c • U) a,
      planeCarrier_jet_smul_ae c (planeCarrierAffine e he y U) a,
      planeCarrierAffine_jet_ae e he y U a,
      (plane_affine_quasiMeasurePreserving e he y).ae_eq_comp (planeCarrier_jet_smul_ae c U a)]
      with z hcu hs hu hsmul
    change (planeCarrierAffine e he y (c • U)).toFunction.jet a z =
      (c • planeCarrierAffine e he y U).toFunction.jet a z
    simp only [Function.comp_def] at hsmul
    rw [hcu, hs, hu, hsmul, smul_comm]

theorem planeCarrierAffine_truncate (hKL : K ≤ L) (e : ℝ) (he : e ≠ 0)
    (y : Vec 2) (U : PlaneHk Set.univ L E) :
    planeCarrierAffine e he y (truncatePlaneHk hKL U) =
      truncatePlaneHk hKL (planeCarrierAffine e he y U) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have hleft := planeCarrierAffine_jet_ae e he y (truncatePlaneHk hKL U) a
  have hright := planeCarrierAffine_jet_ae e he y U (truncateJetIndex hKL a)
  exact hleft.trans hright.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Subtracting the chart velocity adds precisely its native transport correction to the weak dual. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakDual_transport_sub_pair
    (v w : Vec 2 → Vec 2)
    (hvc : ∀ k, Continuous (fun x => v x k))
    (hwc : ∀ k, Continuous (fun x => w x k))
    (hsc : ∀ k, Continuous (fun x => (v x - w x) k))
    {Mv Mw Ms : ℝ} (hMv : 0 ≤ Mv) (hMw : 0 ≤ Mw) (hMs : 0 ≤ Ms)
    (hvb : ∀ k x, |v x k| ≤ Mv) (hwb : ∀ k x, |w x k| ≤ Mw)
    (hsb : ∀ k x, |(v x - w x) k| ≤ Ms)
    (A : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u z : PlaneHk univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport (fun x => v x - w x) hsc hMs hsb) A u F) z =
      inner ℝ (planeWeakDualRepresentative (planeScalarTransport v hvc hMv hvb) A u F) z +
      inner ℝ (planeScalarTransport w hwc hMw hwb (planeH1GradientOperator u))
        (planeHkValueOperator 1 z) := by
  rw [planeWeakDualRepresentative_pair, planeWeakDualRepresentative_pair,
    planeScalarTransport_sub_apply v w hvc hwc hsc hMv hMw hMs hvb hwb hsb,
    inner_sub_left]
  ring
end

/-! Compact truncations of smooth native H1 representatives have the exact product readouts. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def compactSmoothHilbertH1Product (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hsχ : HasCompactSupport χ) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    PlaneHk univ 1 E :=
  compactSmoothHilbertH1 (fun x => χ x • f x) (hχ.smul hf) (hsχ.smul_right)

omit [FiniteDimensional ℝ E] in
theorem compactSmoothHilbertH1Product_value
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M)
    (u : PlaneHk univ 1 E) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : (planeHkValueOperator 1 u : Vec 2 → E) =ᵐ[volume] f) :
    planeHkValueOperator 1 (compactSmoothHilbertH1Product χ hχ hsχ f hf) =
      planeScalarMultiplier χ hχ.continuous hM hb (planeHkValueOperator 1 u) := by
  apply Lp.ext
  have ha := compactSmoothHilbertH1_value_ae (fun x => χ x • f x) (hχ.smul hf) (hsχ.smul_right)
  filter_upwards [ha, hu, planeScalarMultiplier_ae χ hχ.continuous hM hb
    (planeHkValueOperator 1 u)] with x hx hux hmx
  exact hx.trans ((congrArg (fun q : E => χ x • q) hux).symm.trans hmx.symm)

theorem compactSmoothHilbertH1Product_gradient
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M)
    (i : Fin 2) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ x, |fderiv ℝ χ x (basisVec i)| ≤ D)
    (u : PlaneHk univ 1 E) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : (planeHkValueOperator 1 u : Vec 2 → E) =ᵐ[volume] f) :
    planeH1GradientOperator (compactSmoothHilbertH1Product χ hχ hsχ f hf) i =
      planeScalarMultiplier (fun x => fderiv ℝ χ x (basisVec i))
        ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const) hD hd
        (planeHkValueOperator 1 u) +
      planeScalarMultiplier χ hχ.continuous hM hb (planeH1GradientOperator u i) := by
  apply Lp.ext
  have ha := compactSmoothHilbertH1_gradient_ae (fun x => χ x • f x)
    (hχ.smul hf) (hsχ.smul_right) i
  have hg := planeH1_smooth_value_gradient_ae u f (hf.of_le (by simp)) hu i
  have hdc : Continuous (fun x => fderiv ℝ χ x (basisVec i)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  filter_upwards [ha, hu, hg,
    planeScalarMultiplier_ae (fun x => fderiv ℝ χ x (basisVec i)) hdc hD hd
      (planeHkValueOperator 1 u),
    planeScalarMultiplier_ae χ hχ.continuous hM hb (planeH1GradientOperator u i),
    Lp.coeFn_add
      (planeScalarMultiplier (fun x => fderiv ℝ χ x (basisVec i)) hdc hD hd (planeHkValueOperator 1 u))
      (planeScalarMultiplier χ hχ.continuous hM hb (planeH1GradientOperator u i))]
    with x hx hux hgx hdx hcx hax
  unfold compactSmoothHilbertH1Product
  rw [hx, hax]
  change fderiv ℝ (fun y => χ y • f y) x (basisVec i) = _
  rw [fderiv_fun_smul (hχ.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  change χ x • fderiv ℝ f x (basisVec i) + fderiv ℝ χ x (basisVec i) • f x =
    planeScalarMultiplier (fun x => fderiv ℝ χ x (basisVec i)) hdc hD hd
      (planeHkValueOperator 1 u) x +
    planeScalarMultiplier χ hχ.continuous hM hb (planeH1GradientOperator u i) x
  rw [hdx, hcx, hux, hgx, add_comm]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Cell coordinate changes compose and invert on the actual rough Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrierAffine_compose (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (y z : Vec 2) (U : PlaneHk Set.univ K E) :
    planeCarrierAffine a ha y (planeCarrierAffine b hb z U) =
      planeCarrierAffine (b * a) (mul_ne_zero hb ha) (z + b • y) U := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  apply Lp.ext
  simp only [Measure.restrict_univ]
  filter_upwards [planeCarrierAffine_jet_ae a ha y (planeCarrierAffine b hb z U) j,
    (plane_affine_quasiMeasurePreserving a ha y).ae_eq_comp
      (planeCarrierAffine_jet_ae b hb z U j),
    planeCarrierAffine_jet_ae (b * a) (mul_ne_zero hb ha) (z + b • y) U j]
      with x ho hi ht
  change (planeCarrierAffine a ha y (planeCarrierAffine b hb z U)).toFunction.jet j x =
    (planeCarrierAffine (b * a) (mul_ne_zero hb ha) (z + b • y) U).toFunction.jet j x
  simp only [Function.comp_def] at hi
  rw [ho, hi, ht, smul_smul, ← mul_pow, mul_comm a b, smul_add, smul_smul, add_assoc]

theorem planeCarrierAffine_one_zero (U : PlaneHk Set.univ K E) :
    planeCarrierAffine 1 one_ne_zero 0 U = U := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  apply Lp.ext
  simp only [Measure.restrict_univ]
  filter_upwards [planeCarrierAffine_jet_ae 1 one_ne_zero 0 U j] with x hx
  change (planeCarrierAffine 1 one_ne_zero 0 U).toFunction.jet j x = U.toFunction.jet j x
  simpa only [one_pow, one_smul, zero_add] using hx

theorem planeCarrierAffine_inverse (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : PlaneHk Set.univ K E) :
    planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) (planeCarrierAffine e he yc U) = U := by
  rw [planeCarrierAffine_compose]
  simpa only [smul_neg, smul_smul, mul_inv_cancel₀ he, one_smul, add_neg_cancel] using
    planeCarrierAffine_one_zero U

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Compact smooth spacetime fields have strong L2 time curves. -/

theorem compactScalar_l2_strong_time
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (a b : ℝ) :
    ∃ z dz : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)),
      (∀ t, z t =ᵐ[volume] fun x => f (t, x)) ∧
      (∀ t, dz t =ᵐ[volume] fun x => fderiv ℝ f (t, x) (1, 0)) ∧
      CycleEvolution.StrongTimeRegularity a b z dz := by
  let S := Prod.snd '' tsupport f
  have hS : IsCompact S := hs.image continuous_snd
  have hg : MemLp (S.indicator (fun _ : Vec 2 => (1 : ℝ))) 2 volume :=
    memLp_indicator_const 2 hS.measurableSet 1 (Or.inr hS.measure_lt_top.ne)
  let g : Lp ℝ 2 (volume : Measure (Vec 2)) := hg.toLp _
  obtain ⟨c, dc, M, Md, hc, hdc, _, _, _, _, hac, hd⟩ :=
    compactScalarMultiplier_time (E := ℝ) f hf hs a b
  let z := fun t => boundedScalarMultiplier (c t) g
  let dz := fun t => boundedScalarMultiplier (dc t) g
  refine ⟨z, dz, ?_, ?_, ?_⟩
  · intro t
    filter_upwards [boundedScalarMultiplier_ae (c t) g, hg.coeFn_toLp] with x hx hgx
    rw [hx, hgx, hc]
    change f (t, x) * S.indicator (fun _ => (1 : ℝ)) x = f (t, x)
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, mul_one]
    · rw [indicator_of_notMem hxS, mul_zero]
      apply (image_eq_zero_of_notMem_tsupport ?_).symm
      intro hp
      exact hxS ⟨(t, x), hp, rfl⟩
  · intro t
    filter_upwards [boundedScalarMultiplier_ae (dc t) g, hg.coeFn_toLp] with x hx hgx
    rw [hx, hgx, hdc]
    change fderiv ℝ f (t, x) (1, 0) * S.indicator (fun _ => (1 : ℝ)) x = _
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, mul_one]
    · rw [indicator_of_notMem hxS, mul_zero]
      have hp : (t, x) ∉ tsupport f := fun hp => hxS ⟨(t, x), hp, rfl⟩
      rw [fderiv_of_notMem_tsupport ℝ hp, zero_apply]
  · let ev := ContinuousLinearMap.apply ℝ (Lp ℝ 2 (volume : Measure (Vec 2))) g
    have hzAC : AbsolutelyContinuousOnInterval z a b := by
      change AbsolutelyContinuousOnInterval
        (ev ∘ (fun t => boundedScalarMultiplier (E := ℝ) (c t))) a b
      exact ev.lipschitzWith.comp_absolutelyContinuousOnInterval hac
    have hzD : ∀ t, HasDerivAt z (dz t) t := by
      intro t
      change HasDerivAt
        (ev ∘ (fun s => boundedScalarMultiplier (E := ℝ) (c s)))
        (ev (boundedScalarMultiplier (E := ℝ) (dc t))) t
      exact ev.hasFDerivAt.comp_hasDerivAt t (hd t)
    exact ⟨hzAC, Filter.Eventually.of_forall hzD⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Periodic compact weak testing yields the literal unit-cell coupled identity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem periodic_cutoff_weakIdentity_transfer {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hup : AVenhance.IsZ2Periodic (fun x => inner ℝ (u x) (φ x)))
    (hfp : AVenhance.IsZ2Periodic (fun x => inner ℝ (f x) (φ x)))
    (hiu : Integrable (fun x => inner ℝ (u x) (φ x)) (volume.restrict AVenhance.unitCube))
    (hif : Integrable (fun x => inner ℝ (f x) (φ x)) (volume.restrict AVenhance.unitCube))
    (hir : ∀ s ∈ Set.Ioc a t, Integrable (weakIdentityRhs ν v φ dφ du flux F g s)
      (volume.restrict AVenhance.unitCube))
    (hrp : ∀ s ∈ Set.Ioc a t, AVenhance.IsZ2Periodic (weakIdentityRhs ν v φ dφ du flux F g s))
    (hcp : ∀ s ∈ Set.Ioc a t, ∀ k, AVenhance.IsZ2Periodic (fun x =>
      ν * inner ℝ (du s k x) (φ x) + inner ℝ (flux s x k + F s x k) (φ x)))
    (hcut : ∀ s ∈ Set.Ioc a t, Integrable (fun x =>
      weakIdentityRhs ν v φ dφ du flux F g s x * spatialPatchCutoff ζ 1 0 x) volume)
    (hcorr : ∀ s ∈ Set.Ioc a t, ∀ k, Integrable (fun x =>
      (ν * inner ℝ (du s k x) (φ x) + inner ℝ (flux s x k + F s x k) (φ x)) *
        fderiv ℝ (spatialPatchCutoff ζ 1 0) x (basisVec k)) volume)
    (hlocal : CoupledWeakIdentity volume ν a t v u f
      (fun x => spatialPatchCutoff ζ 1 0 x • φ x)
      (fun k x => fderiv ℝ (spatialPatchCutoff ζ 1 0) x (basisVec k) • φ x +
        spatialPatchCutoff ζ 1 0 x • dφ k x) du flux F g) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v u f φ dφ du flux F g := by
  let χ := spatialPatchCutoff ζ 1 0
  let ψ := fun x => χ x • φ x
  let dψ := fun k x => fderiv ℝ χ x (basisVec k) • φ x + χ x • dφ k x
  have huχ : (fun x => inner ℝ (u x) (ψ x)) = fun x => inner ℝ (u x) (φ x) * χ x := by
    funext x
    simp only [ψ, inner_smul_right]
    ring
  have hfχ : (fun x => inner ℝ (f x) (ψ x)) = fun x => inner ℝ (f x) (φ x) * χ x := by
    funext x
    simp only [ψ, inner_smul_right]
    ring
  have heu : (∫ x, inner ℝ (u x) (ψ x)) = ∫ x in AVenhance.unitCube, inner ℝ (u x) (φ x) := by
    rw [huχ]
    exact integral_periodic_unitPatch hζ _ hup (huχ ▸ hlocal.1)
  have hef : (∫ x, inner ℝ (f x) (ψ x)) = ∫ x in AVenhance.unitCube, inner ℝ (f x) (φ x) := by
    rw [hfχ]
    exact integral_periodic_unitPatch hζ _ hfp (hfχ ▸ hlocal.2.1)
  have her (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      (∫ x, weakIdentityRhs ν v ψ dψ du flux F g s x) =
        ∫ x in AVenhance.unitCube, weakIdentityRhs ν v φ dφ du flux F g s x := by
    have halg : weakIdentityRhs ν v ψ dψ du flux F g s = fun x =>
        weakIdentityRhs ν v φ dφ du flux F g s x * χ x -
          ∑ k : Fin 2, (ν * inner ℝ (du s k x) (φ x) +
            inner ℝ (flux s x k + F s x k) (φ x)) * fderiv ℝ χ x (basisVec k) := by
      funext x
      change coupledWeakRhs ν (v s x) (χ x • φ x)
        (fun k => fderiv ℝ χ x (basisVec k) • φ x + χ x • dφ k x)
        (fun k => du s k x) (fun k => flux s x k) (fun k => F s x k) (g s x) = _
      rw [coupledWeakRhs_cutoff]
      change χ x * weakIdentityRhs ν v φ dφ du flux F g s x - _ = _
      simp only [Fin.sum_univ_two]
      ring
    rw [halg, integral_sub (hcut s hs) (integrable_finsetSum Finset.univ (fun k _ => hcorr s hs k)),
      integral_finsetSum Finset.univ (fun k _ => hcorr s hs k)]
    simp_rw [integral_periodic_unitPatch_derivative hζ _ (hcp s hs _) _ (hcorr s hs _)]
    simp only [Finset.sum_const_zero, sub_zero]
    exact integral_periodic_unitPatch hζ _ (hrp s hs) (hcut s hs)
  have htime : (fun s => ∫ x, weakIdentityRhs ν v ψ dψ du flux F g s x) =ᵐ[
      volume.restrict (Set.Ioc a t)] (fun s => ∫ x in AVenhance.unitCube,
        weakIdentityRhs ν v φ dφ du flux F g s x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact her s hs
  refine ⟨hiu, hif, hir, hlocal.2.2.2.1.congr htime, ?_⟩
  rw [← heu, ← hef]
  exact hlocal.2.2.2.2.trans (integral_congr_ae htime)

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Returning an arbitrary native carrier and pulling it back is exact. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrierAffine_inverse_right (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : PlaneHk Set.univ K E) :
    planeCarrierAffine e he yc (planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U) = U := by
  rw [planeCarrierAffine_compose]
  simpa only [inv_mul_cancel₀ he, neg_add_cancel] using planeCarrierAffine_one_zero U

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Literal spatial pairing of the viscous weak dual with a prescribed coupling flux. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The identity diffusion operator retains the physical viscosity in the weak pairing. -/
theorem planeViscousDual_pair_eq_integral (ν : ℝ)
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {M : ℝ} (hM : 0 ≤ M) (hvb : ∀ k x, |v x k| ≤ M)
    (u φ : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative (planeScalarTransport v hvc hM hvb)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) u F) φ =
      ∫ x, -(∑ k : Fin 2, v x k * inner ℝ
        (planeH1GradientOperator (E := E) u k x) (planeHkValueOperator (E := E) 1 φ x))
        - ν * ∑ k : Fin 2, inner ℝ (planeH1GradientOperator (E := E) u k x)
          (planeH1GradientOperator (E := E) φ k x)
        - ∑ k : Fin 2, inner ℝ (F k x) (planeH1GradientOperator (E := E) φ k x) := by
  let du := planeH1GradientOperator (E := E) u
  let dφ := planeH1GradientOperator (E := E) φ
  let z := planeHkValueOperator (E := E) 1 φ
  let T := planeScalarTransport v hvc hM hvb du
  have hT : Integrable (fun x => inner ℝ (T x) (z x)) volume :=
    L2.integrable_inner T z
  have hD : Integrable (fun x => ∑ k : Fin 2, inner ℝ (du k x) (dφ k x)) volume :=
    integrable_finsetSum Finset.univ (fun k _ => L2.integrable_inner (du k) (dφ k))
  have hF : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F k x) (dφ k x)) volume :=
    integrable_finsetSum Finset.univ (fun k _ => L2.integrable_inner (F k) (dφ k))
  rw [planeWeakDualRepresentative_pair]
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left]
  rw [sub_add_eq_sub_sub]
  rw [L2.inner_def, planeFlux_inner_eq_integral, planeFlux_inner_eq_integral]
  rw [← integral_neg, ← integral_const_mul]
  change (∫ x, -inner ℝ (T x) (z x)) -
    (∫ x, ν * ∑ k : Fin 2, inner ℝ (du k x) (dφ k x)) -
    (∫ x, ∑ k : Fin 2, inner ℝ (F k x) (dφ k x)) = _
  rw [← integral_sub (f := fun x => -inner ℝ (T x) (z x))
    (g := fun x => ν * ∑ k : Fin 2, inner ℝ (du k x) (dφ k x)) hT.neg (hD.const_mul ν)]
  rw [← integral_sub (f := fun x => -inner ℝ (T x) (z x) -
    ν * ∑ k : Fin 2, inner ℝ (du k x) (dφ k x))
    (g := fun x => ∑ k : Fin 2, inner ℝ (F k x) (dφ k x))
    (hT.neg.sub (hD.const_mul ν)) hF]
  apply integral_congr_ae
  filter_upwards [planeScalarTransport_ae v hvc hM hvb du] with x hx
  change -inner ℝ (T x) (z x) - ν * (∑ k, inner ℝ (du k x) (dφ k x)) -
    (∑ k, inner ℝ (F k x) (dφ k x)) = _
  rw [hx]
  simp only [sum_inner, real_inner_smul_left]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleJointProofs

/-! The compact spacetime time calculus is independent of L2 representatives. -/

theorem compactScalar_native_strong_time
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (a b : ℝ) (z dz : ℝ → Lp ℝ 2 (volume.restrict (univ : Set (Vec 2))))
    (hz : ∀ t, z t =ᵐ[volume.restrict univ] fun x => f (t, x))
    (hdz : ∀ t, dz t =ᵐ[volume.restrict univ]
      fun x => fderiv ℝ f (t, x) (1, 0)) :
    CycleEvolution.StrongTimeRegularity a b z dz := by
  have hex (μ : Measure (Vec 2)) (hμ : μ = volume) :
      ∃ u du : ℝ → Lp ℝ 2 μ,
        (∀ t, u t =ᵐ[μ] fun x => f (t, x)) ∧
        (∀ t, du t =ᵐ[μ] fun x => fderiv ℝ f (t, x) (1, 0)) ∧
        CycleEvolution.StrongTimeRegularity a b u du := by
    subst μ
    exact compactScalar_l2_strong_time f hf hs a b
  obtain ⟨u, du, hu, hdu, ht⟩ := hex (volume.restrict univ) Measure.restrict_univ
  have he : u = z := by
    funext t
    exact Lp.ext ((hu t).trans (hz t).symm)
  have hde : du = dz := by
    funext t
    exact Lp.ext ((hdu t).trans (hdz t).symm)
  rw [he, hde] at ht
  exact ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Finite derivative prices make the actual spatial cell pullback a continuous linear operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def planeCarrierAffineNormBound (K : ℕ) (e : ℝ) : ℝ :=
  Real.sqrt (∑ a : JetIndex2 K, ‖e ^ a.1.val‖ ^ 2 * |(e ^ 2)⁻¹|)

theorem planeCarrierAffine_norm_le (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) :
    ‖planeCarrierAffine e he y U‖ ≤ planeCarrierAffineNormBound K e * ‖U‖ := by
  classical
  let c : ℝ := ∑ a : JetIndex2 K, ‖e ^ a.1.val‖ ^ 2 * |(e ^ 2)⁻¹|
  have hc : 0 ≤ c := Finset.sum_nonneg (fun a _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
  have hca (a : JetIndex2 K) : ‖e ^ a.1.val‖ ^ 2 * |(e ^ 2)⁻¹| ≤ c := by
    change ‖e ^ a.1.val‖ ^ 2 * |(e ^ 2)⁻¹| ≤
      ∑ b : JetIndex2 K, ‖e ^ b.1.val‖ ^ 2 * |(e ^ 2)⁻¹|
    exact Finset.single_le_sum
      (fun b _ => mul_nonneg (sq_nonneg ‖e ^ b.1.val‖) (abs_nonneg ((e ^ 2)⁻¹)))
      (Finset.mem_univ a)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  change ‖planeCarrierAffine e he y U‖ ^ 2 ≤ (Real.sqrt c * ‖U‖) ^ 2
  rw [mul_pow, Real.sq_sqrt hc]
  change ‖(planeCarrierAffine e he y U).val‖ ^ 2 ≤ c * ‖U.val‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [planeCarrierAffine_component_norm_sq]
  exact mul_le_mul_of_nonneg_right (hca a) (sq_nonneg _)

def planeCarrierAffineOperator (K : ℕ) (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    PlaneHk Set.univ K E →L[ℝ] PlaneHk Set.univ K E :=
  (planeCarrierAffineLinearMap K e he y).mkContinuous (planeCarrierAffineNormBound K e)
    (planeCarrierAffine_norm_le e he y)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The explicitly computed metric array is exactly the singleton chain's metric coefficient. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

omit [Fintype ι] in
theorem planeDiagonalGradientCoefficient_self_eq_metricFlux (K : ι → ℕ) (D : ℕ)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ι) (d : admissibleOrders K D v v) (hd : d.1 = 2) (t : ℝ) (z : Vec 2) :
    planeDiagonalGradientCoefficient (h := h) K D G v v d t z =
      metricFlux (h := h) (G v t z) (d.1 - 1) (a := v) rfl (by omega) := by
  rcases d with ⟨d, hde⟩
  change d = 2 at hd
  subst d
  simp [planeDiagonalGradientCoefficient, familyDiagonalIdentity_self, metricFlux]

theorem planeDiagonalGradientCoefficient_eq_scalar_chain (K : ι → ℕ) (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (p p' : Fin 1 × ι)
    (d : admissibleOrders (fun q : Fin 1 × ι => K q.2) D p p') (t : ℝ) (z : Vec 2) :
    planeDiagonalGradientCoefficient (h := h) K D (fun _ r x => G r x - 1) p.2 p'.2 d t z =
      planeChainCoefficient (geometryScalarData D G) (fun _ => K) p p' d t z := by
  by_cases hd : d.1 = 2
  · by_cases hv : p.2 = p'.2
    · have hpp : p = p' := Prod.ext (Subsingleton.elim _ _) hv
      subst p'
      rw [geometryScalarCoefficient_diagonal (h := h) D G (fun _ => K) p d hd t z,
        planeDiagonalGradientCoefficient_self_eq_metricFlux (h := h) K D
          (fun _ r x => G r x - 1) p.2 d hd t z]
    · rw [geometryScalarCoefficient_offDiagonal (h := h) D G (fun _ => K) p p' hv d t z]
      exact planeDiagonalGradientCoefficient_of_component_ne (h := h) K D
        (fun _ r x => G r x - 1) p.2 p'.2 d t z (Ne.symm hv)
  · rw [planeDiagonalGradientCoefficient_of_order_ne (h := h) K D
      (fun _ r x => G r x - 1) p.2 p'.2 d t z hd,
      geometryScalarCoefficient_otherOrder (h := h) D G (fun _ => K) p p' d hd t z]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The exact homogeneous coupled plane system has its full weak equation in diffusion time. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Normalize every stored-order homogeneous weak test, with the actual rescaled coefficients. -/
theorem planeHomogeneous_normalized_weak_test (K : ι → ℕ) (D : ℕ)
    {ν a b : ℝ} (hν : 0 < ν) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b))
    (φ : PlaneHk Set.univ 1 (h i)) :
    CoupledWeakIdentity volume 1 (ν * a) t (timeNormalizedVelocity ν v)
      ((u i (ν⁻¹ * t)).toFunction.jet (valueIndex2 (K i)))
      ((f i).toFunction.jet (valueIndex2 (K i)))
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      (fun r k => (w i (ν⁻¹ * r)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun r => planeRawCouplingFlux K D r
        (fun i i' d s x => ν⁻¹ • A i i' d (ν⁻¹ * s) x)
        (fun j => w j (ν⁻¹ * r)) i) 0 0 := by
  have hmem : ν⁻¹ * t ∈ Set.Icc a b := by
    rw [show ν⁻¹ * t = t / ν by rw [div_eq_mul_inv, mul_comm]]
    exact ⟨(le_div_iff₀ hν).mpr (by simpa only [mul_comm] using ht.1),
      (div_le_iff₀ hν).mpr (by simpa only [mul_comm] using ht.2)⟩
  have hold := planeHomogeneous_weak_test K D ν a b v A f u w hs i (ν⁻¹ * t) hmem φ
  have hn := coupledWeakIdentity_time_normalization volume hν hmem.1 v _ _ _ _ _ _ 0 0 hold
  have hf : (fun r x => planeRawCouplingFlux K D r
      (fun i i' d s y => ν⁻¹ • A i i' d (ν⁻¹ * s) y)
      (fun j => w j (ν⁻¹ * r)) i x) =
      fun r x => ν⁻¹ • planeRawCouplingFlux K D (ν⁻¹ * r)
        A (fun j => w j (ν⁻¹ * r)) i x := by
    funext r x
    simp only [planeRawCouplingFlux, smul_apply, Finset.smul_sum]
  rw [hf]
  simpa only [← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul, Pi.zero_apply,
    smul_zero, Pi.zero_def] using hn

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The native scalar dual splits into its exact drift, diffusion, and forcing-flux integrals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarDual_split_pairing
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ k j, Continuous (fun x => G x k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v hvc hMv hvb) (planeScalarDiffusion G hGc hMG hGb) u F) z =
      -(∫ x, ∑ k : Fin 2, v x k * inner ℝ
        (planeH1GradientOperator u k x) (planeHkValueOperator 1 z x)) -
      (∫ x, ∑ k : Fin 2, inner ℝ
        (hilbertMatrixAction (G x) (fun j => planeH1GradientOperator u j x) k)
        (planeH1GradientOperator z k x)) -
      ∫ x, ∑ k : Fin 2, inner ℝ (F k x) (planeH1GradientOperator z k x) := by
  rw [planeWeakDualRepresentative_pair, inner_add_left, sub_add_eq_sub_sub,
    L2.inner_def, planeFlux_inner_eq_integral, planeFlux_inner_eq_integral]
  congr 2
  · congr 1
    apply integral_congr_ae
    filter_upwards [planeScalarTransport_ae v hvc hMv hvb (planeH1GradientOperator u)]
      with x hx
    rw [hx]
    simp only [sum_inner, real_inner_smul_left]
  · apply integral_congr_ae
    have hd := ae_all_iff.mpr (fun k =>
      planeScalarDiffusion_ae G hGc hMG hGb (planeH1GradientOperator u) k)
    filter_upwards [hd] with x hx
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun q : E => inner ℝ q (planeH1GradientOperator z k x)) (hx k)


theorem planeViscousDual_split_pairing (ν : ℝ)
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative (planeScalarTransport v hvc hMv hvb)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) u F) z =
      -(∫ x, ∑ k : Fin 2, v x k * inner ℝ
        (planeH1GradientOperator u k x) (planeHkValueOperator 1 z x)) -
      ν * (∫ x, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator u k x)
        (planeH1GradientOperator z k x)) -
      ∫ x, ∑ k : Fin 2, inner ℝ (F k x) (planeH1GradientOperator z k x) := by
  rw [planeWeakDualRepresentative_pair]
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left]
  rw [sub_add_eq_sub_sub, L2.inner_def, planeFlux_inner_eq_integral,
    planeFlux_inner_eq_integral]
  congr 2
  congr 1
  apply integral_congr_ae
  filter_upwards [planeScalarTransport_ae v hvc hMv hvb (planeH1GradientOperator u)]
    with x hx
  rw [hx]
  simp only [sum_inner, real_inner_smul_left]

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Integer images of the unit-patch value reconstruct the exact incoming torus datum. -/

/-- The scalar unit-patch images form a summable partition at every point. -/
theorem unitPatch_images_summable {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (x : Vec 2) :
    Summable (fun n : Fin 2 → ℤ => spatialPatchCutoff ζ 1 0 (x + AVenhance.latticeShift n)) := by
  have hs : Summable (fun n : Fin 2 → ℤ => spatialPatchCutoff ζ 1 (-n) x) :=
    (spatialPatchCutoff_summable hζ 1 x).comp_injective (Equiv.neg (Fin 2 → ℤ)).injective
  apply hs.congr
  intro n
  have hn : (fun i => (0 : ℤ) - (1 : ℤ) * n i) = -n := by
    funext i
    simp only [one_mul, zero_sub, Pi.neg_apply]
  exact ((spatialPatchCutoff_translate ζ 1 0 n x).trans
    (congrArg (fun k => spatialPatchCutoff ζ 1 k x) hn)).symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The periodized order-zero unit-patch representative is exactly the original torus class. -/
theorem unitPatchLocalization_periodized_value_ae {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {K : ℕ} (f : TorusHk K E) :
    periodizeRawJet (spatialPatchLocalization hζ 1 (by decide) 0 K f).toFunction.jet
      (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] f.val (valueIndex2 K) := by
  have hr := localizeTorusCarrier_value_ae f (spatialPatchCoefficient (E := E) ζ 1 0)
    (spatialPatchCoefficient_smooth hζ 1 0 K) (spatialPatchCoefficient_compact hζ 1 (by decide) 0)
  have hprod : (spatialPatchLocalization hζ 1 (by decide) 0 K f).toFunction.jet (valueIndex2 K)
      =ᵐ[volume] fun x => spatialPatchCutoff ζ 1 0 x • f.toFunction.jet (valueIndex2 K) x := by
    change (localizeTorusCarrier f (spatialPatchCoefficient (E := E) ζ 1 0)
      (spatialPatchCoefficient_smooth hζ 1 0 K)
      (spatialPatchCoefficient_compact hζ 1 (by decide) 0)).toFunction.jet (valueIndex2 K)
      =ᵐ[volume] _
    simpa only [spatialPatchCoefficient, smul_apply, ContinuousLinearMap.id_apply] using hr
  have hp := f.toFunction.hasPeriodicWeakJet.1 (valueIndex2 K)
  have he (x : Vec 2) : latticePeriodization
      (fun y => spatialPatchCutoff ζ 1 0 y • f.toFunction.jet (valueIndex2 K) y) x =
      f.toFunction.jet (valueIndex2 K) x := by
    unfold latticePeriodization
    have hper (n : Fin 2 → ℤ) : f.toFunction.jet (valueIndex2 K) (x + AVenhance.latticeShift n) =
        f.toFunction.jet (valueIndex2 K) x := hp n x
    simp_rw [hper]
    rw [(unitPatch_images_summable hζ x).tsum_smul_const]
    change latticePeriodization (spatialPatchCutoff ζ 1 0) x • _ = _
    rw [latticePeriodization_unitPatch hζ x, one_smul]
  have hae := (latticePeriodization_congr_ae hprod).trans (Filter.EventuallyEq.of_eq (funext he))
  have hres : periodizeRawJet (spatialPatchLocalization hζ 1 (by decide) 0 K f).toFunction.jet
      (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] f.toFunction.jet (valueIndex2 K) :=
    ae_restrict_of_ae hae
  exact hres.trans (periodicJetRepresentative_ae f.val (valueIndex2 K))

end AVRegularity.CycleJointProofs
end
end
