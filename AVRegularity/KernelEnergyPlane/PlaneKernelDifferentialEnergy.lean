-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergyPlane.PlaneKernelFluxTimeComponent
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionPlane
import AVRegularity.CoupledEnergyPlane.SourceCarrierResidualRhs
import AVRegularity.CoupledEnergyPlane.Variational.SourceWeakSolutionExistence
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The exact mass norm is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeFactorial_cutoff_tendsto (k : ℕ) (ρ : ℝ) (f : PlaneHk Set.univ k E) :
    Tendsto (fun N => factorialNormSq ρ (planeHkCutoff N k f).val)
      atTop (𝓝 (factorialNormSq ρ f.val)) := by
  have ht := ((planeFactorialReadout (E := E) k ρ).continuous.tendsto f).comp
    (tendsto_planeHkCutoff k f)
  simpa only [Function.comp_def, planeFactorialReadout_normSq] using ht.norm.pow 2

theorem planeComponentBand_gradient_tendsto (μ : Measure ℝ) (k : ℕ) (ρ : ℝ)
    (w : ℝ → PlaneHk Set.univ (k + 1) E) (hw : MemLp w 2 μ)
    (q : ℕ → ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hq : ∀ N, q N =ᵐ[μ] fun t => hilbertProjection N (planeHkValueOperator (k + 1) (w t))) :
    Tendsto (fun N => ∫ t, gradFactorialNormSq ρ (hilbertBandHk N (k + 1) (q N t)).val ∂μ)
      atTop (𝓝 (∫ t, gradFactorialNormSq ρ (w t).val ∂μ)) := by
  have ht := bandCurve_gradient_tendsto_of_fields (E := fun _ : Unit => E) μ
    (fun _ => k) ρ (fun _ => 1) (fun _ => w) (fun _ => hw)
    (fun N t => WithLp.toLp 2 (fun _ => q N t)) (fun N _ => hq N)
  simpa only [massGradNormSq, Finset.univ_unique, Finset.sum_singleton,
    inv_one, one_mul, WithLp.ofLp_toLp] using ht

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem carrierFlux_sub
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)) (i : ι) (t : ℝ) :
    P.carrierFlux w i t - P.carrierFlux w' i t =
      P.carrierFlux (fun j s => w j s - w' j s) i t := by
  have he := (P.clampedFluxCLM t).toLinearMap.map_sub (fun j => w j t) (fun j => w' j t)
  exact (congrArg (fun V => V i) he).symm

theorem carrierGradient_mass_integrable
    (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    Integrable (fun t => massGradNormSq ρ P.π (fun i => (w i t).val))
      (volume.restrict (Set.Icc a b)) := by
  have hg (i : ι) : MemLp (fun t => planeGradientTensor (w i t)) 2
      (volume.restrict (Set.Icc a b)) := by
    simpa only [Function.comp_def, planeGradientTensorOperator_apply] using
      (planeGradientTensorOperator (E := h i) k).comp_memLp' (hw i)
  have hs := planeMassNormSq_integrable ρ P.π P.hπ (fun _ => k)
    (fun i t => planeGradientTensor (w i t)) hg
  simpa only [massNormSq, planeGradientTensor_factorialNormSq, massGradNormSq] using hs

theorem carrierFlux_mass_integral_le
    (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    (∫ t in Set.Icc a b, massNormSq ρ P.π (fun i => (P.carrierFlux w i t).val)) ≤
      (ν * P.θ) ^ 2 * (∫ t in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i t).val)) := by
  have hf := planeMassNormSq_integrable ρ P.π P.hπ (fun _ => k) (P.carrierFlux w)
    (fun i => P.carrierFlux_memLp w hw i)
  have hg := P.carrierGradient_mass_integrable w hw
  rw [← integral_const_mul]
  apply integral_mono_ae hf (hg.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he (i : ι) := P.carrierFlux_of_mem w i t ht
  simpa only [he] using P.flux_mass_bound t ht (fun i => w i t)

end PlaneKernelOperator

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def higherInput (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) (t : ℝ) : PlaneHk Set.univ (k + D - 1) (G i j α) :=
  clampedRegularizedInputCLM ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) P.radius_pos P.htime t (w j t)

theorem higherInput_of_mem (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    P.higherInput w i j α t = P.lift t ht (fun j => w j t) i j α := by
  apply PlaneHk.ext_value isOpen_univ
  change (planeRegularizedInput ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) (Set.projIcc a b P.htime t)
    (Set.projIcc a b P.htime t).property (w j t)).val (valueIndex2 (k + D - 1)) = _
  rw [planeRegularizedInput_value, P.lift_value]
  simp only [Set.projIcc_of_mem P.htime ht]

theorem higherInput_memLp (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i j : ι) (α : Γ i j) :
    MemLp (P.higherInput w i j α) 2 (volume.restrict (Set.Icc a b)) :=
  clampedRegularizedInput_memLp ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) P.radius_pos P.htime (w j) (hw j)

theorem higherInput_value_ae (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (P.higherInput w i j α t).val (valueIndex2 (k + D - 1)) =
      P.S i j α t ((P.C i j α).compLp ((w j t).val (valueIndex2 (k + 1)))) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [P.higherInput_of_mem w i j α t ht]
  exact P.lift_value t ht (fun j => w j t) i j α

end PlaneKernelOperator
end

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def kernelRawFlux (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)) (i : ι) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (P.higherInput w i j α t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)

theorem kernelRawFlux_of_mem (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    P.kernelRawFlux w i t = P.rawFlux t ht (fun j => w j t) i := by
  funext x
  unfold kernelRawFlux rawFlux
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro d _
  rw [P.higherInput_of_mem w i j α t ht]

theorem carrierFlux_raw (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (P.carrierFlux w i t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      P.kernelRawFlux w i t := by
  rw [P.carrierFlux_of_mem w i t ht, P.kernelRawFlux_of_mem w i t ht]
  exact P.flux_raw t ht (fun j => w j t) i

end PlaneKernelOperator
end

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem higherInput_unique_ae (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α))
    (hy : ∀ i j α, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (y i j α t).val (valueIndex2 (k + D - 1)) =
        P.S i j α t ((P.C i j α).compLp ((w j t).val (valueIndex2 (k + 1)))))
    (i j : ι) (α : Γ i j) :
    y i j α =ᵐ[volume.restrict (Set.Icc a b)] P.higherInput w i j α := by
  filter_upwards [hy i j α, P.higherInput_value_ae w i j α] with t ht hc
  apply PlaneHk.ext_value isOpen_univ
  exact ht.trans hc.symm

theorem inputRawFlux_eq_kernelRawFlux_ae (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α))
    (hy : ∀ i j α, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (y i j α t).val (valueIndex2 (k + D - 1)) =
        P.S i j α t ((P.C i j α).compLp ((w j t).val (valueIndex2 (k + 1))))) (i : ι) :
    P.inputRawFlux y i =ᵐ[volume.restrict (Set.Icc a b)] P.kernelRawFlux w i := by
  have he : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j, ∀ α : Γ i j,
      y i j α t = P.higherInput w i j α t :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun α => P.higherInput_unique_ae w y hy i j α))
  filter_upwards [he] with t ht
  funext x
  simp only [inputRawFlux, kernelRawFlux, ht]

end PlaneKernelOperator
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem noLocalRawFlux_zero (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i : ι) (t : ℝ) (x : Vec 2) :
    planeRawCouplingFlux (fun _ => k) 0 t noLocalCoefficient (fun i => w i t) i x = 0 := by
  classical
  unfold planeRawCouplingFlux
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro d _
  exact (noLocalOrders (k := k) i j d).elim

theorem totalCarrierFlux_raw_ae
    (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      planeRawCouplingFlux (fun _ => k) 0 t noLocalCoefficient (fun i => w i t) i x +
        (F i t + P.carrierFlux w i t).toFunction.jet (valueIndex2 k) x =
      P.kernelRawFlux w i t x + (F i t).toFunction.jet (valueIndex2 k) x := by
  filter_upwards [planeJet_add_ae (F i t) (P.carrierFlux w i t) (valueIndex2 k),
    P.carrierFlux_raw w i t ht] with x ha hq
  rw [noLocalRawFlux_zero (h := h) (k := k) w i t x, zero_add, ha, hq, add_comm]

theorem kernelWeakSolution_forcedWeakSolution
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (V : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionPlane ν a b v k D P.B P.C P.S f F g u w y) :
    IsCoupledWeakSolutionPlane ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w := by
  refine ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1, ?_⟩
  intro i t ht φ
  have hs : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hf : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      P.inputRawFlux y i r x + (F i r).toFunction.jet (valueIndex2 k) x =
      planeRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i x +
        (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k) x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs
      (P.inputRawFlux_eq_kernelRawFlux_ae w y hsol.2.2.2.2.2.1 i),
      ae_restrict_mem measurableSet_Ioc] with r hr hrI
    rw [hr]
    filter_upwards [P.totalCarrierFlux_raw_ae w F i r (hs hrI)] with x hx
    exact hx.symm
  have hp : ∀ r ∈ Set.Ioc a t,
      Integrable (planeRawSpatialRhs (fun _ => k) 0 ν r v noLocalCoefficient
        (fun j s => F j s + P.carrierFlux w j s) g (fun j => w j r) i φ)
        (volume.restrict (Set.univ : Set (Vec 2))) := by
    intro r hr
    have hi := planeRawSpatialRhs_integrable ρ P.radius_pos (fun _ => k) 0
      a b r ν (hs hr) v (hv r (hs hr)).continuous V (hvb r (hs hr))
      noLocalCoefficient (fun j j' d => (noLocalOrders (k := k) j j' d).elim)
      (fun j j' d => (noLocalOrders (k := k) j j' d).elim)
      (fun j s => F j s + P.carrierFlux w j s) g (fun j => w j r) i φ
    simpa only [Measure.restrict_univ] using hi
  exact weakIdentity_flux_congr_time (volume.restrict (Set.univ : Set (Vec 2))) ν a t v
    ((u i t).toFunction.jet (valueIndex2 k)) ((f i).toFunction.jet (valueIndex2 k))
    (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (P.inputRawFlux y i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => planeRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i)
    (fun r => (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k)) hf hp (hsol.2.2.2.2.2.2 i t ht φ)

end PlaneKernelOperator
end

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem forcedWeakSolution_kernelWeakSolution
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (V : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F F' : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (he : ∀ i, F' i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => F i t + P.carrierFlux w i t)
    (hsol : IsCoupledWeakSolutionPlane ν a b v 0 (fun _ => k) noLocalCoefficient f F' g u w) :
    IsKernelWeakSolutionPlane ν a b v k D P.B P.C P.S f F g u w (P.higherInput w) := by
  refine ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1,
    P.higherInput_memLp w hsol.2.1, P.higherInput_value_ae w, ?_⟩
  intro i t ht φ
  have hs : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hf : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      planeRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i x +
        (F' i r).toFunction.jet (valueIndex2 k) x =
      P.kernelRawFlux w i r x + (F i r).toFunction.jet (valueIndex2 k) x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs (he i),
      ae_restrict_mem measurableSet_Ioc] with r hr hrI
    rw [hr]
    exact P.totalCarrierFlux_raw_ae w F i r (hs hrI)
  have hp : ∀ r ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ q : Fin 2, v r x q * inner ℝ
        ((w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩ x)
        (φ.toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ q : Fin 2, inner ℝ
        ((w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩ x)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ x) -
      ∑ q : Fin 2, inner ℝ
        (P.kernelRawFlux w i r x q + (F i r).toFunction.jet (valueIndex2 k) x q)
        (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ x) +
      inner ℝ ((g i r).toFunction.jet (valueIndex2 k) x)
        (φ.toFunction.jet (valueIndex2 1) x))
      (volume.restrict (Set.univ : Set (Vec 2))) := by
    intro r hr
    have hi := planeRawSpatialRhs_integrable ρ P.radius_pos (fun _ => k) 0
      a b r ν (hs hr) v (hv r (hs hr)).continuous V (hvb r (hs hr))
      noLocalCoefficient (fun j j' d => (noLocalOrders (k := k) j j' d).elim)
      (fun j j' d => (noLocalOrders (k := k) j j' d).elim)
      (fun j s => F j s + P.carrierFlux w j s) g (fun j => w j r) i φ
    have hi' : Integrable (planeRawSpatialRhs (fun _ => k) 0 ν r v noLocalCoefficient
        (fun j s => F j s + P.carrierFlux w j s) g (fun j => w j r) i φ)
        (volume.restrict (Set.univ : Set (Vec 2))) := by
      simpa only [Measure.restrict_univ] using hi
    apply hi'.congr
    filter_upwards [P.totalCarrierFlux_raw_ae w F i r (hs hr)] with x hx
    change _ - (∑ q : Fin 2, inner ℝ
      ((planeRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i x +
        (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k) x) q) _) + _ =
      _ - (∑ q : Fin 2, inner ℝ
      ((P.kernelRawFlux w i r x + (F i r).toFunction.jet (valueIndex2 k) x) q) _) + _
    rw [hx]
  exact weakIdentity_flux_congr_time (volume.restrict (Set.univ : Set (Vec 2))) ν a t v
    ((u i t).toFunction.jet (valueIndex2 k)) ((f i).toFunction.jet (valueIndex2 k))
    (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (fun r => planeRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i)
    (fun r => (F' i r).toFunction.jet (valueIndex2 k))
    (P.kernelRawFlux w i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k)) hf hp (hsol.2.2.2.2 i t ht φ)

end PlaneKernelOperator
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakNativeDifferenceAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakNativeDifferenceTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_fluxDifference_equation {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F F' : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ j, MemLp (F' j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (u' : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w' : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol' : IsCoupledWeakSolutionPlane ν a b v D K A f F' g u' w') :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let W' := planeCarrierHighTime (h := h) K a b w' hsol'.2.1
    let Wd := W - W'
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    let hFd := fun i => (hF i).sub (hF' i)
    let Φd := fun i => ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b))) ((hFd i).toLp (fun t => F i t - F' i t))
    ∀ i, ∀ t : Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 (h i),
      inner ℝ (planeHkValueOperator (E := h i) (K i) (u i t - u' i t))
        (planeHkValueOperator (E := h i) 1 ψ) =
      nativeRawTestValue (E := h i) ν 0 (weakH1CarrierTimeCLM (h := h) K a b i Wd)
        (limitDriftField (h := h) hab Cc hc i Wd) (limitFluxField (h := h) hab Cc hc Wd i (Φd i))
        (fun _ => 0) t ψ := by
  intro W W' Wd Cc hc hFd Φd
  have hn := planeWeakSolution_native_equation (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol
  have hn' := planeWeakSolution_native_equation (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F' hF' g hg f u' w' hsol'
  intro i t ψ
  let Fi := (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))
  let Fi' := (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b)) ((hF' i).toLp (F' i))
  have hf := nativeDifferenceFields (h := h) hab Cc hc W W' i Fi
  have he := nativeRawTestDifference_identity_of_same_source (E := h i) t.property ν
    (planeHkValueOperator (E := h i) (K i) (f i))
    (weakH1CarrierTimeCLM (h := h) K a b i W) (weakH1CarrierTimeCLM (h := h) K a b i W')
    (limitDriftField (h := h) hab Cc hc i W) (limitDriftField (h := h) hab Cc hc i W')
    (limitFluxField (h := h) hab Cc hc W i Fi) (limitFluxField (h := h) hab Cc hc W' i Fi')
    (fun s => planeHkValueOperator (E := h i) (K i) (g i s))
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)) ψ
    (planeHkValueOperator (E := h i) (K i) (u i t))
    (planeHkValueOperator (E := h i) (K i) (u' i t)) (hn i t ψ) (hn' i t ψ)
  let L := (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b))
  have hd : Φd i = Fi - Fi' := by
    change L (((hF i).sub (hF' i)).toLp (fun t => F i t - F' i t)) =
      L ((hF i).toLp (F i)) - L ((hF' i).toLp (F' i))
    exact (congrArg L ((hF i).toLp_sub (hF' i))).trans (L.toLinearMap.map_sub _ _)
  have hflux : limitFluxField (h := h) hab Cc hc Wd i (Φd i) =
      limitFluxField (h := h) hab Cc hc W i Fi - limitFluxField (h := h) hab Cc hc W' i Fi' :=
    (congrArg (limitFluxField (h := h) hab Cc hc Wd i) hd).trans
      (planeFluxDifferenceFields hab Cc hc W W' i Fi Fi')
  have hr := congrArg₂
    (fun (Q : Lp (PlaneHk Set.univ 1 (h i)) 2 (volume.restrict (Set.Icc a b)))
      (S : Lp (Lp (h i) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)) ×
        Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b))) =>
      nativeRawTestValue (E := h i) (a := a) (b := b) ν 0 Q S.1 S.2 (fun _ => 0) t ψ)
    hf.1 (congrArg₂ (fun x y => (x, y)) hf.2.1 hflux)
  have hl := congrArg (fun p : Lp (h i) 2 (volume : Measure (Vec 2)) =>
    inner ℝ p (planeHkValueOperator (E := h i) 1 ψ))
    ((planeHkValueOperator (E := h i) (K i)).toLinearMap.map_sub (u i t) (u' i t))
  exact hl.trans (he.trans hr.symm)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakDifferencePackAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakDifferencePackTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_fluxDifference_isWeakSolution {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F F' : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ j, MemLp (F' j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (u' : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w' : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol' : IsCoupledWeakSolutionPlane ν a b v D K A f F' g u' w') :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let W' := planeCarrierHighTime (h := h) K a b w' hsol'.2.1
    let U := planeWeakDifferenceCurve (h := h) K a b u u' hsol.1 hsol'.1
    IsCoupledWeakSolutionPlane ν a b v D K A (fun _ => 0) (fun i t => F i t - F' i t) (fun _ _ => 0)
      (fun i => extendCurve hab (U i)) (weakHighCarrier (h := h) K a b (W - W')) := by
  intro W W' U
  have hWd := planeHighTime_sub_graph_ae (h := h) K a b W W'
    (planeCarrierHighTime_graph_ae (h := h) K a b w hsol.2.1)
    (planeCarrierHighTime_graph_ae (h := h) K a b w' hsol'.2.1)
  have hFd (i : ι) : MemLp (fun t => F i t - F' i t) 2 (volume.restrict (Set.Icc a b)) :=
    (hF i).sub (hF' i)
  have hg0 (i : ι) : Integrable (fun _ : ℝ => (0 : PlaneHk Set.univ (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := timeIntegrable_zero _
  have hi (i : ι) : U i ⟨a, le_rfl, hab⟩ = 0 :=
    planeWeakDifferenceCurve_initial_zero (h := h) K hab u u' hsol.1 hsol'.1 f hsol.2.2.2.1 hsol'.2.2.2.1 i
  have ha (i : ι) := planeWeakDifferenceCurve_carrier_alignment_ae (h := h) K hab
    u u' hsol.1 hsol'.1 w w' hsol.2.1 hsol'.2.1 hsol.2.2.1 hsol'.2.2.1 i
  apply sourceNativeEquation_pack_weakSolution (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets (W - W') hWd ν (fun i t => F i t - F' i t) hFd
    (fun _ _ => 0) hg0 (fun _ => 0) U hi ha
  intro Cc hc i t ψ
  have he := planeWeakSolution_fluxDifference_equation (h := h) hab ρ hρ v hv V hV hbv
    K D A hAc hAf hvm hAm Kmax hK strain B lam hstrain hB hlam hjets
    ν F F' hF hF' g hg f u w hsol u' w' hsol' i t ψ
  simpa only [U, planeWeakDifferenceCurve_apply, map_zero] using he
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Drift data of a plane kernel and the forced weak solution it admits. -/

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
variable {a b ρ ν : ℝ} {k D : ℕ}

structure PlaneKernelDriftData
    (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) where
  v : ℝ → Vec 2 → Vec 2
  smooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)
  measurable : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2)
  V : ℝ
  V_nonneg : 0 ≤ V
  bounded : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V
  divergence_zero : ∀ t ∈ Set.Icc a b, ∀ x,
    ∑ m : Fin 2, fderiv ℝ (v t) x (basisVec m) m = 0
  strain : ℝ
  B : ℝ
  lam : ℝ
  strain_nonneg : 0 ≤ strain
  B_ge_one : 1 ≤ B
  lam_pos : 0 < lam
  scale_small : B * ρ / lam ≤ 1 / 2
  strain_small : strain * B * ρ ^ 2 ≤ ν / 8
  jets : ∀ t ∈ Set.Icc a b, ∀ l : ℕ, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

def baseCoefficients : ProjectedCoefficients (h := h) (Set.Icc a b) (fun _ => k) 0 :=
  sourceProjectedCoefficients a b ρ P.radius_pos Q.v Q.smooth Q.V Q.V_nonneg Q.bounded
    (fun _ => k) 0 noLocalCoefficient
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)

theorem noLocalSchur : SchurCondition
    (schurMatrix ν ρ P.π (fun _ => k) 0 a b (noLocalCoefficient (h := h))) := by
  have hz (i j : ι) : schurMatrix ν ρ P.π (fun _ => k) 0 a b
      (noLocalCoefficient (h := h)) i j = 0 := by
    let : IsEmpty (admissibleOrders (fun _ : ι => k) 0 i j) := ⟨noLocalOrders i j⟩
    simp only [schurMatrix, Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
  constructor <;> intro i <;> simp only [hz, Finset.sum_const_zero] <;> norm_num

theorem exists_forcedWeakSolution
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ k (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F g u w :=
  exists_sourcePlaneWeakSolution (fun _ => k) k (fun _ => le_rfl)
    ρ Q.strain Q.B Q.lam ν P.radius_pos Q.strain_nonneg Q.B_ge_one Q.lam_pos
    P.diffusivity_pos Q.scale_small Q.strain_small P.π P.hπ a b P.htime Q.v Q.smooth
    Q.V Q.V_nonneg Q.bounded Q.divergence_zero Q.jets 0 noLocalCoefficient
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim) (noLocalSchur (P := P))
    F g hF hg f Q.measurable (fun i j d => (noLocalOrders (k := k) i j d).elim)

end PlaneKernelDriftData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Mass energy bound for the diffusion and drift part of the projected kernel flux. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem diffusionDrift_massEnergy_le (N : ℕ) (u : ProjectedFamily h) (t : Set.Icc a b) :
    (∑ i, (P.π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N k (projectedOperator Q.baseCoefficients N ν t u i)).val
      (hilbertBandHk N k (u i)).val) ≤
      -(3 * ν / 4) * massGradNormSq ρ P.π
        (fun i => (hilbertBandHk N (k + 1) (u i)).val) := by
  let C := Q.baseCoefficients
  let R := massGradNormSq ρ P.π (fun i => (hilbertBandHk N (k + 1) (u i)).val)
  let transport (i : ι) := factorialPairing ρ
    (hilbertBandHk N k (hilbertProjection N
      (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t)
        (bandGradientOperator (E := h i) N (u i))))).val
    (hilbertBandHk N k (u i)).val
  have hd : (∑ i, (P.π i)⁻¹ * |transport i|) ≤ (ν / 4) * R :=
    projectedDrift_massPairing_abs_sum_le (fun _ => k) k (fun _ => le_rfl) N
      (fun i => u i) ρ Q.strain Q.B Q.lam ν P.radius_pos Q.strain_nonneg Q.B_ge_one
      Q.lam_pos P.diffusivity_pos Q.scale_small Q.strain_small P.π P.hπ (Q.v t)
      (Q.smooth t t.property) Q.V Q.V_nonneg (Q.bounded t t.property)
      (Q.divergence_zero t t.property) (Q.jets t t.property)
  have hr : (∑ i, (P.π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N k (projectedOperator C N ν t u i)).val
      (hilbertBandHk N k (u i)).val) =
      (∑ i, (P.π i)⁻¹ * (-transport i)) - ν * R := by
    have he (i j : ι) : (∑ d : admissibleOrders (fun _ : ι => k) 0 i j,
        factorialPairing ρ
          (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
            (planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
              (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)
              (bandTensorOperator (E := h j) N (d.1 - 1) (u j))))).val
          (hilbertBandHk N k (u i)).val) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      exact (noLocalOrders i j d).elim
    have hrow (i : ι) := projectedOperator_row_energy C N ν ρ t u i
    simp_rw [hrow]
    simp_rw [he]
    simp only [Finset.sum_const_zero, add_zero, mul_sub, Finset.sum_sub_distrib]
    congr 1
    dsimp [R, massGradNormSq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hds : (∑ i, (P.π i)⁻¹ * (-transport i)) ≤ ∑ i, (P.π i)⁻¹ * |transport i| := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (neg_le_abs _) (inv_nonneg.mpr (P.hπ i).le)
  change _ ≤ -(3 * ν / 4) * R
  rw [hr]
  linarith [hds.trans hd]

end PlaneKernelDriftData
end

/-! Row energy bound for the diffusion and drift part of the projected kernel flux. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem diffusionDrift_rowEnergy_le (N : ℕ) (u : ProjectedFamily h) (t : Set.Icc a b) (i : ι) :
    factorialPairing ρ
      (hilbertBandHk N k (projectedOperator Q.baseCoefficients N ν t u i)).val
      (hilbertBandHk N k (u i)).val ≤
      -(3 * ν / 4) * gradFactorialNormSq ρ (hilbertBandHk N (k + 1) (u i)).val := by
  let C := Q.baseCoefficients
  have hd := projectedDrift_factorialPairing_abs_le (E := h i) (le_refl k) N (u i)
    ρ Q.strain Q.B Q.lam ν P.radius_pos Q.strain_nonneg Q.B_ge_one
    Q.lam_pos P.diffusivity_pos Q.scale_small Q.strain_small (Q.v t)
    (Q.smooth t t.property) Q.V Q.V_nonneg (Q.bounded t t.property)
    (Q.divergence_zero t t.property) (Q.jets t t.property)
  change |factorialPairing ρ
    (hilbertBandHk N k (hilbertProjection N
      (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t)
        (bandGradientOperator (E := h i) N (u i))))).val
    (hilbertBandHk N k (u i)).val| ≤
      (ν / 4) * gradFactorialNormSq ρ (hilbertBandHk N (k + 1) (u i)).val at hd
  have he (j : ι) : (∑ d : admissibleOrders (fun _ : ι => k) 0 i j,
      factorialPairing ρ
        (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
          (planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
            (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)
            (bandTensorOperator (E := h j) N (d.1 - 1) (u j))))).val
        (hilbertBandHk N k (u i)).val) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    exact (noLocalOrders i j d).elim
  have hr := projectedOperator_row_energy C N ν ρ t u i
  simp_rw [he] at hr
  simp only [Finset.sum_const_zero, add_zero] at hr
  rw [hr]
  linarith [neg_le_abs (factorialPairing ρ
    (hilbertBandHk N k (hilbertProjection N
      (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t)
        (bandGradientOperator (E := h i) N (u i))))).val
    (hilbertBandHk N k (u i)).val)]

end PlaneKernelDriftData
end

/-! Mass energy bound for the projected kernel right-hand side. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem kernelProjectedRhs_massEnergy_le (N : ℕ) (u : ProjectedFamily h) (t : Set.Icc a b)
    (F : ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ k (h i)) :
    (∑ i, (P.π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N k ((projectedOperator Q.baseCoefficients N ν t u +
        projectedSource N (fun i _ => F i + P.flux t t.property
          (fun j => hilbertBandHk N (k + 1) (u j)) i) (fun i _ => g i) t) i)).val
      (hilbertBandHk N k (u i)).val) ≤
      -(ν / 2) * massGradNormSq ρ P.π (fun i => (hilbertBandHk N (k + 1) (u i)).val) +
        Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) *
          Real.sqrt (massNormSq ρ P.π (fun i => (hilbertBandHk N k (u i)).val)) +
        (2 / ν) * massNormSq ρ P.π (fun i => (F i).val) := by
  have ho := Q.diffusionDrift_massEnergy_le N u t
  have hk := P.projectedFlux_massPairing_abs_le N t t.property u
  have hf := AVRegularity.CoupledEnergyPlane.Variational.projectedFlux_massPairing_young_le
    N (fun _ => k) ρ ν P.diffusivity_pos P.π P.hπ F (fun i => u i)
  have hg := projectedSource_massPairing_abs_le N (fun _ => k) ρ P.π P.hπ g (fun i => u i)
  simp only [WithLp.ofLp_add, Pi.add_apply, projectedSource, map_add,
    bandPairing_add, mul_add, Finset.sum_add_distrib]
  have hFk := le_abs_self (∑ i, (P.π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
      (planeHkValueOperator k (P.flux t t.property
        (fun j => hilbertBandHk N (k + 1) (u j)) i)))).val
    (hilbertBandHk N k (u i)).val)
  have hFF := le_abs_self (∑ i, (P.π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
      (planeHkValueOperator k (F i)))).val (hilbertBandHk N k (u i)).val)
  have hgg := le_abs_self (∑ i, (P.π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N k (hilbertProjection N (planeHkValueOperator k (g i)))).val
    (hilbertBandHk N k (u i)).val)
  linarith

end PlaneKernelDriftData
end

/-! Unabsorbed energy bound for the projected kernel right-hand side. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem kernelProjectedRhs_unabsorbed_le (N : ℕ) (u : ProjectedFamily h) (t : Set.Icc a b)
    (F : ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ k (h i)) :
    (∑ i, (P.π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N k ((projectedOperator Q.baseCoefficients N ν t u +
        projectedSource N (fun i _ => F i + P.flux t t.property
          (fun j => hilbertBandHk N (k + 1) (u j)) i) (fun i _ => g i) t) i)).val
      (hilbertBandHk N k (u i)).val) ≤
      -(5 * ν / 8) * massGradNormSq ρ P.π (fun i => (hilbertBandHk N (k + 1) (u i)).val) +
        Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) *
          Real.sqrt (massNormSq ρ P.π (fun i => (hilbertBandHk N k (u i)).val)) +
        Real.sqrt (massNormSq ρ P.π (fun i => (F i).val)) *
          Real.sqrt (massGradNormSq ρ P.π (fun i => (hilbertBandHk N (k + 1) (u i)).val)) := by
  have ho := Q.diffusionDrift_massEnergy_le N u t
  have hk := P.projectedFlux_massPairing_abs_le N t t.property u
  have hf := AVRegularity.CoupledEnergyPlane.Variational.projectedFlux_massPairing_abs_le
    N (fun _ => k) ρ P.π P.hπ F (fun i => u i)
  have hg := projectedSource_massPairing_abs_le N (fun _ => k) ρ P.π P.hπ g (fun i => u i)
  simp only [WithLp.ofLp_add, Pi.add_apply, projectedSource, map_add,
    bandPairing_add, mul_add, Finset.sum_add_distrib]
  have hFk := le_abs_self (∑ i, (P.π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
      (planeHkValueOperator k (P.flux t t.property
        (fun j => hilbertBandHk N (k + 1) (u j)) i)))).val
    (hilbertBandHk N k (u i)).val)
  have hFF := le_abs_self (∑ i, (P.π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
      (planeHkValueOperator k (F i)))).val (hilbertBandHk N k (u i)).val)
  have hgg := le_abs_self (∑ i, (P.π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N k (hilbertProjection N (planeHkValueOperator k (g i)))).val
    (hilbertBandHk N k (u i)).val)
  linarith

end PlaneKernelDriftData
end

/-! Differential energy inequality for the projected kernel solution. -/

section
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
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem kernelProjectedEnergy_deriv_le_of_hasDerivAt
    (N : ℕ) (u : ℝ → ProjectedFamily h) (t : Set.Icc a b)
    (F : ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ k (h i))
    (hu : HasDerivAt u
      (projectedOperator Q.baseCoefficients N ν t (u t) +
        projectedSource N (fun i _ => F i +
          P.flux t t.property (fun j => hilbertBandHk N (k + 1) (u t j)) i)
          (fun i _ => g i) t) t) :
    deriv (fun s => massNormSq ρ P.π
      (fun i => (hilbertBandHk N k (u s i)).val)) t +
      ν * massGradNormSq ρ P.π (fun i => (hilbertBandHk N (k + 1) (u t i)).val) ≤
    2 * Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) *
      Real.sqrt (massNormSq ρ P.π (fun i => (hilbertBandHk N k (u t i)).val)) +
      (4 / ν) * massNormSq ρ P.π (fun i => (F i).val) := by
  rw [(hasDerivAt_massBandEnergy N (fun _ => k) ρ P.π P.hπ hu).deriv]
  have he := Q.kernelProjectedRhs_massEnergy_le N (u t) t F g
  linear_combination 2 * he

end PlaneKernelDriftData
end

end AVRegularity.KernelEnergyPlane
end
