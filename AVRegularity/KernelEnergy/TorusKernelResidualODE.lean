-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSequence
public import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSolutionExistence
public import AVRegularity.CoupledEnergy.Variational.TorusSpatialFluxTimeLp
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-- Head-class cache: the normed group of the periodic Sobolev carrier. -/
local instance residualODETorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
/-- Head-class cache: the inner product space of the periodic Sobolev carrier. -/
local instance residualODETorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
/-- Head-class cache: the normed space of the periodic Sobolev carrier. -/
local instance residualODETorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

end AVRegularity.KernelEnergy
end

attribute [local instance] AVRegularity.KernelEnergy.residualODETorusNormed
  AVRegularity.KernelEnergy.residualODETorusInner
  AVRegularity.KernelEnergy.residualODETorusSpace

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] in
theorem carrierFlux_memLp_of_family (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b)) :=
  P.carrierFlux_memLp (coupledCarrierHighTime (fun _ => k) a b w hw) w
    (coupledCarrierHighTime_ae (fun _ => k) a b w hw) i

omit [DecidableEq ι] in
theorem carrierFlux_tail_square_tendsto (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b,
      ‖P.carrierFlux (fun j s => w j s - galerkinProj N (w j s)) i t‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have htLp (N : ℕ) (j : ι) : MemLp (fun t => w j t - galerkinProj (E := h j) (K := k + 1) N (w j t)) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub _ 2 (w j) (fun t => galerkinProj (E := h j) (K := k + 1) N (w j t)) (hw j)
      ((galerkinProj (E := h j) (K := k + 1) N).comp_memLp' (hw j))
  let Q := carrierFamilyProjection (h := h) (fun _ => k + 1)
  let u0 : ℝ → (∀ j, TorusHk (k + 1) (h j)) := fun t j => w j t
  let R := fun N => P.carrierFlux (fun j t => w j t - galerkinProj (E := h j) (K := k + 1) N (w j t)) i
  have hu0 : MemLp u0 2 (volume.restrict (Set.Icc a b)) := memLp_pi_iff.mpr hw
  apply boundedResidual_integral_square_tendsto (volume.restrict (Set.Icc a b)) Q
    (carrierFamilyProjection_norm_le (h := h) (fun _ => k + 1))
    (carrierFamilyProjection_tendsto (h := h) (fun _ => k + 1)) u0 hu0 R
    (fun N => P.carrierFlux_memLp_of_family _ (htLp N) i) P.fluxBudget
  intro N
  filter_upwards [] with t
  have hn := (norm_le_pi_norm
    (P.flux (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property
      (fun j => w j t - galerkinProj (E := h j) (K := k + 1) N (w j t))) i).trans
    (P.flux_norm_bound _ _ _)
  have he : ‖(fun j => w j t - galerkinProj (E := h j) (K := k + 1) N (w j t))‖ = ‖Q N (u0 t) - u0 t‖ :=
    norm_sub_rev _ _
  exact hn.trans_eq (congrArg (fun z : ℝ => P.fluxBudget * z) he)

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] in
theorem carrierFlux_sub (w z : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) :
    P.carrierFlux (fun j r => w j r - z j r) i t = P.carrierFlux w i t - P.carrierFlux z i t := by
  have he := congrArg (fun V => V i)
    ((P.fluxCLM (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property).map_sub
      (fun j => w j t) (fun j => z j t))
  simpa only [Pi.sub_apply] using! he

theorem finiteFlux_eq_projectedCarrierFlux_ae (N : ℕ)
    (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hy : ∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun j => u j t))
    (htrace : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncateTorusHk (Nat.le_succ k) (w i t) = u i t)
    (i : ι) :
    P.finiteFlux N y i =ᵐ[volume.restrict (Set.Icc a b)]
      P.carrierFlux (fun j t => galerkinProj N (w j t)) i := by
  filter_upwards [ae_all_iff.mpr htrace, ae_restrict_mem measurableSet_Icc] with t ht htI
  have he : (fun j => u j t) = (fun j => truncateTorusHk (Nat.le_succ k) (w j t)) :=
    funext (fun j => (ht j).symm)
  have hs : coefficientSynthesis (h := h) (k := k) N (y t) = (fun j => galerkinProj N (w j t)) := by
    funext j
    change coupledPlainSynthesis N j (k + 1) (y t) = _
    rw [hy t htI, he]
    exact plainInitialCoefficients_higher_synthesis N (fun _ => k) (fun j => w j t) j
  rw [P.finiteFlux_of_mem N y i t htI, hs]
  simp only [carrierFlux, Set.projIcc_of_mem P.htime htI]

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Extract each component of the actual closed-time kernel identity. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
theorem kernelEquation_trace_pairing_eq_ae
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (F : ∀ i, ℝ → TorusHk (k) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (k) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (k) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (P.projectedMatrix (N n) v r))
      (fun r => plainSourceCoefficients (N n) (fun _ => k) (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime (y n)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) (fun _ => k) a b P.htime (y n))) atTop (𝓝 (ell U)))
    (i : ι) (φ : TorusHk 1 (h i)) (u : ℝ → ℝ)
    (hc : ContinuousOn u (Set.Icc a b)) (R : ℝ)
    (hb : ∀ n, ∀ t ∈ Set.Icc a b, ‖torusHkValueCLM (coupledPlainSynthesis (N n) i k
      (AVenhance.Infra.ODE.extendCurve P.htime (y n) t))‖ ≤ R)
    (hid : ∀ t ∈ Set.Icc a b,
      u t - inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
        P.kernelIntegratedRhs t v F g U i φ) :
    u =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      inner ℝ (U t i (valueIndex2 (k + 1))) (torusHkValueCLM φ) := by
  apply plainBochner_trace_pairing_eq_ae (fun _ => k) P.htime N y U hw i φ u
    (hc.aestronglyMeasurable measurableSet_Icc) R hb
  intro t ht
  have hp := P.kernelFiniteTrace_value_pairing_tendsto t ht v hv_bdd hv_meas hv
    F g hF hg f N hN y hy U Q hu hw i φ
  have he : inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) +
      P.kernelIntegratedRhs t v F g U i φ = u t := by
    rw [← hid t ht]
    ring
  rw [he] at hp
  exact hp

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def kernelRawFlux (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (P.higherInput w i j α t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)

omit [DecidableEq ι] in
theorem carrierFlux_of_mem (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    P.carrierFlux w i t = P.flux t ht (fun j => w j t) i := by
  unfold carrierFlux
  simp only [Set.projIcc_of_mem P.htime ht]

omit [DecidableEq ι] in
theorem kernelRawFlux_of_mem (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
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

omit [DecidableEq ι] in
theorem carrierFlux_raw (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (P.carrierFlux w i t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      P.kernelRawFlux w i t := by
  rw [P.carrierFlux_of_mem w i t ht, P.kernelRawFlux_of_mem w i t ht]
  exact P.flux_raw t ht (fun j => w j t) i

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem noLocalRawFlux_zero (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) (x : Vec 2) :
    torusRawCouplingFlux (fun _ => k) 0 t noLocalCoefficient (fun i => w i t) i x = 0 := by
  classical
  unfold torusRawCouplingFlux
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro d _
  exact (noLocalOrders (k := k) i j d).elim

omit [DecidableEq ι] in
theorem totalCarrierFlux_raw_ae
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      torusRawCouplingFlux (fun _ => k) 0 t noLocalCoefficient (fun i => w i t) i x +
        (F i t + P.carrierFlux w i t).toFunction.jet (valueIndex2 k) x =
      P.kernelRawFlux w i t x + (F i t).toFunction.jet (valueIndex2 k) x := by
  filter_upwards [torusJet_add_ae (F i t) (P.carrierFlux w i t) (valueIndex2 k),
    P.carrierFlux_raw w i t ht] with x ha hq
  rw [noLocalRawFlux_zero (h := h) (k := k) w i t x, zero_add, ha, hq, add_comm]

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def inputRawFlux (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (i : ι) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (y i j α t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)

omit [DecidableEq ι] in
theorem higherInput_unique_ae (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hy : ∀ i j α, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (y i j α t).val (valueIndex2 (k + D - 1)) =
        P.S i j α t ((P.C i j α).compLp ((w j t).val (valueIndex2 (k + 1)))))
    (i j : ι) (α : Γ i j) :
    y i j α =ᵐ[volume.restrict (Set.Icc a b)] P.higherInput w i j α := by
  filter_upwards [hy i j α, P.higherInput_value_ae w i j α] with t ht hc
  apply TorusHk.ext_value
  exact ht.trans hc.symm

omit [DecidableEq ι] in
theorem inputRawFlux_eq_kernelRawFlux_ae (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
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

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)


def carrierPair (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) : ℝ :=
  inner ℝ (torusFactorialReadout ρ k (P.carrierFlux w i t))
    (torusFactorialGradientReadout ρ k (w i t))

omit [DecidableEq ι] in
theorem carrierPair_integrable (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    Integrable (P.carrierPair w i) (volume.restrict (Set.Icc a b)) := by
  have hL := (torusFactorialReadout (E := PiLp 2 (fun _ : Fin 2 => h i)) ρ k).comp_memLp'
    (P.carrierFlux_memLp_of_family w hw i)
  have hR := (torusFactorialGradientReadout (E := h i) ρ k).comp_memLp' (hw i)
  have hi := hL.norm.integrable_mul hR.norm
  apply hi.mono' (hL.aestronglyMeasurable.inner hR.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => norm_inner_le_norm _ _)

omit [DecidableEq ι] in
theorem carrierPair_sumAbs_le (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∑ i, (P.π i)⁻¹ * |P.carrierPair w i t|) ≤
      (ν * P.θ) * massGradNormSq ρ P.π (fun i => (w i t).val) := by
  simpa only [carrierPair, carrierFlux_of_mem P w _ t ht,
    torusFactorialReadout_apply, torusFactorialGradientReadout_apply,
    AVRegularity.KernelEnergy.factorialWeightedJet,
    AVRegularity.CoupledEnergy.Variational.factorialWeightedJet] using!
      P.flux_massPairing_sumAbs_le t ht (fun i => w i t)


end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] [Fintype ι] in
theorem carrierGradient_energy_integrable
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    Integrable (fun t => gradFactorialNormSq ρ (w i t).val) (volume.restrict (Set.Icc a b)) := by
  have hm := (torusFactorialGradientReadout (E := h i) ρ k).comp_memLp' (hw i)
  simpa only [Function.comp_def, torusFactorialGradientReadout_normSq] using! hm.norm.integrable_sq

omit [DecidableEq ι] in
theorem carrierPair_sum_integral_bound
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    (∑ i, (P.π i)⁻¹ * ∫ t in Set.Icc a b, |P.carrierPair w i t|) ≤
      (ν * P.θ) * ∫ t in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i t).val) := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    (P.carrierPair_integrable w hw i).abs.const_mul ((P.π i)⁻¹))
  have hg := integrable_finsetSum Finset.univ (fun i _ =>
    (carrierGradient_energy_integrable (ρ := ρ) w hw i).const_mul ((P.π i)⁻¹))
  have hm := integral_mono_ae hi (hg.const_mul (ν * P.θ))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact P.carrierPair_sumAbs_le w t ht)
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (P.carrierPair_integrable w hw i).abs.const_mul ((P.π i)⁻¹))] at hm
  simp only [integral_const_mul] at hm
  exact hm

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)



def weightedFluxCLM (i : ι) (t : ℝ) : (∀ j, TorusHk (k + 1) (h j)) →L[ℝ]
    JetL2 (volume.restrict AVenhance.unitCube) k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  (torusFactorialReadout ρ k).comp ((ContinuousLinearMap.proj i).comp
    (P.fluxCLM (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property))

def weightedGradientFamilyCLM (i : ι) : (∀ j, TorusHk (k + 1) (h j)) →L[ℝ]
    JetL2 (volume.restrict AVenhance.unitCube) k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  (torusFactorialGradientReadout ρ k).comp (ContinuousLinearMap.proj i)

omit [DecidableEq ι] in
theorem weightedPairCLM_apply (w : ∀ j, ℝ → TorusHk (k + 1) (h j)) (i : ι) (t : ℝ) :
    inner ℝ (P.weightedFluxCLM i t (fun j => w j t))
      (weightedGradientFamilyCLM (h := h) (ρ := ρ) (k := k) i (fun j => w j t)) =
      P.carrierPair w i t := rfl

omit [DecidableEq ι] in
theorem weightedFluxCLM_norm_bound (i : ι) (t : ℝ) (x : ∀ j, TorusHk (k + 1) (h j)) :
    ‖P.weightedFluxCLM i t x‖ ≤
      (‖torusFactorialReadout (E := PiLp 2 (fun _ : Fin 2 => h i)) ρ k‖ * P.fluxBudget) * ‖x‖ := by
  let W := torusFactorialReadout (E := PiLp 2 (fun _ : Fin 2 => h i)) ρ k
  have hx := (norm_le_pi_norm (P.flux (Set.projIcc a b P.htime t)
    (Set.projIcc a b P.htime t).property x) i).trans (P.flux_norm_bound _ _ x)
  exact (W.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg W)).trans_eq
    (mul_assoc _ _ _).symm)

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)



omit [DecidableEq ι] in
theorem carrierPair_projected_abs_integral_tendsto
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b,
      |P.carrierPair (fun j s => galerkinProj N (w j s)) i t|)
      Filter.atTop (nhds (∫ t in Set.Icc a b, |P.carrierPair w i t|)) := by
  let W := torusFactorialReadout (E := PiLp 2 (fun _ : Fin 2 => h i)) ρ k
  let u0 : ℝ → (∀ j, TorusHk (k + 1) (h j)) := fun t j => w j t
  let Q := carrierFamilyProjection (h := h) (fun _ => k + 1)
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun t => |inner ℝ (P.weightedFluxCLM i t (Q N (u0 t)))
        (weightedGradientFamilyCLM (h := h) (ρ := ρ) (k := k) i (Q N (u0 t)))|)
      (volume.restrict (Set.Icc a b)) := by
    simpa only [Q, u0, carrierFamilyProjection_apply, weightedPairCLM_apply] using!
      (P.carrierPair_integrable (fun j t => galerkinProj (E := h j) (K := k + 1) N (w j t))
        (fun j => (galerkinProj (E := h j) (K := k + 1) N).comp_memLp' (hw j)) i).abs.aestronglyMeasurable
  have hl := timeBilinear_projection_abs_integral_tendsto (volume.restrict (Set.Icc a b)) Q
    (carrierFamilyProjection_norm_le (h := h) (fun _ => k + 1))
    (carrierFamilyProjection_tendsto (h := h) (fun _ => k + 1)) (P.weightedFluxCLM i)
    (weightedGradientFamilyCLM (h := h) (ρ := ρ) (k := k) i)
    (‖W‖ * P.fluxBudget) (mul_nonneg (norm_nonneg W) P.fluxBudget_nonneg)
    (P.weightedFluxCLM_norm_bound i) u0 (memLp_pi_iff.mpr hw) hm
  simpa only [Q, u0, carrierFamilyProjection_apply, weightedPairCLM_apply] using! hl

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)


theorem higherSynthesis_eq_projected_ae (N : ℕ)
    (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hy : ∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun j => u j t))
    (htrace : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncateTorusHk (Nat.le_succ k) (w i t) = u i t) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      coupledPlainSynthesis N i (k + 1) (y t) = galerkinProj N (w i t) := by
  filter_upwards [ae_all_iff.mpr htrace, ae_restrict_mem measurableSet_Icc] with t ht htI
  intro i
  rw [hy t htI]
  have he : (fun j => u j t) = (fun j => truncateTorusHk (Nat.le_succ k) (w j t)) :=
    funext (fun j => (ht j).symm)
  rw [he]
  exact plainInitialCoefficients_higher_synthesis N (fun _ => k) (fun j => w j t) i

omit [DecidableEq ι] in
theorem carrierPair_congr_time (w z : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ)
    (ht : ∀ j, w j t = z j t) : P.carrierPair w i t = P.carrierPair z i t := by
  have he : (fun j => w j t) = (fun j => z j t) := funext ht
  unfold carrierPair carrierFlux
  rw [he, ht i]

theorem carrierPair_synthesis_projected_ae (N : ℕ)
    (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hy : ∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun j => u j t))
    (htrace : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncateTorusHk (Nat.le_succ k) (w i t) = u i t)
    (i : ι) :
    P.carrierPair (fun j t => coupledPlainSynthesis N j (k + 1) (y t)) i =ᵐ[volume.restrict (Set.Icc a b)]
      P.carrierPair (fun j t => galerkinProj N (w j t)) i := by
  filter_upwards [higherSynthesis_eq_projected_ae N y u w hy htrace] with t ht
  exact P.carrierPair_congr_time _ _ i t ht

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Continuous closed-time primitives of the actual limit kernel flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelNativeTrace_continuousOn (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (α B lam : ℝ)
    (hj : ∀ t ∈ Set.Icc a b, ∀ (_i : ι) l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i, ℝ → TorusHk (k) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (k) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout (fun _ => k) j (U t)).val = U t j)
    (u : ∀ i, ℝ → TorusHk (k) (h i)) (f : ∀ i, TorusHk (k) (h i))
    (hid : ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          P.kernelIntegratedRhs t v F g U i φ)
    (hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b))
    (R : ℝ) (hub : ∀ i, ∀ t ∈ Set.Icc a b, ‖u i t‖ ≤ R)
    (huw : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (k)) (coupledHighGraphReadout (fun _ => k) i (U t))) :
    ∀ i, ContinuousOn (u i) (Set.Icc a b) := by
  let Q : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
    fun i t => P.clampedAmbientFluxCLM i t (U t)
  have hQ (i : ι) : MemLp (Q i) 2 (volume.restrict (Set.Icc a b)) := P.limitFlux_memLp U i
  have hforce (i : ι) : MemLp (fun t => F i t + Q i t) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add (volume.restrict (Set.Icc a b)) 2 (F i) (Q i) (hF i) (hQ i)
  have heq (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
      inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
      coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
        (fun i r => F i r + Q i r) g U i φ := by
    rw [P.integratedRhs_add_flux t ht v F Q g U i φ (hF i) (hQ i)]
    exact hid i t ht φ
  apply plainNativeTrace_continuousOn (fun _ => k) 0 P.htime ν ρ P.radius_pos
    v hv hc hp V hV hb α B lam hj noLocalCoefficient
  · intro i j d
    exact (noLocalOrders (k := k) i j d).elim
  · intro i j d
    exact (noLocalOrders (k := k) i j d).elim
  · intro t ht i j d
    exact (noLocalOrders (k := k) i j d).elim
  · intro t ht i j d
    exact (noLocalOrders (k := k) i j d).elim
  · exact hforce
  · exact hg
  · exact hU
  · exact heq
  · exact hcont
  · exact hub
  · exact huw

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Hilbert weak compactness and closed Sobolev graph readout. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelFourier_energy_closedTrace_subsequence
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ y : (N : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) N),
      ∃ (U : CoupledHighTime (h := h) (fun _ => k) a b) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ N, AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime (y N)) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve P.htime (y N)) a b ∧
    (∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (AVenhance.Infra.ODE.extendCurve P.htime (y N) t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (AVenhance.Infra.ODE.extendCurve P.htime (y N) s)).val)) ≤
      2 * massNormSq ρ P.π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2) ∧
      ‖plainHigherBochner N (fun _ => k) a b P.htime (y N)‖ ^ 2 ≤
        ((∑ i, P.π i) * (b - a) + (∑ i, P.π i / factorialWeightMin ρ k) * (2 / ν)) *
          (2 * massNormSq ρ P.π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2)) ∧
      (∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
        Filter.Tendsto (fun n => ell (plainHigherBochner (φ n) (fun _ => k) a b P.htime (y (φ n))))
          Filter.atTop (𝓝 (ell U))) ∧
      (∀ i, MemLp (fun t => coupledHighGraphReadout (fun _ => k) i (U t)) 2
        (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        (coupledHighGraphReadout (fun _ => k) i (U t)).val = U t i) ∧
      (∀ t ∈ Set.Icc a b, ∃ (V : CoupledLowHilbert (h := h) (fun _ => k)) (ψ : ℕ → ℕ), StrictMono ψ ∧
        (∀ ell : CoupledLowHilbert (h := h) (fun _ => k) →L[ℝ] ℝ,
          Filter.Tendsto (fun n => ell (plainLowerSynthesisCLM (φ (ψ n)) (fun _ => k)
            (AVenhance.Infra.ODE.extendCurve P.htime (y (φ (ψ n))) t)))
            Filter.atTop (𝓝 (ell V))) ∧
        (∀ i, V i ∈ torusHkGraph (E := h i) (k)) ∧
        (t = a → V = WithLp.toLp 2 (fun i => (f i).val)) ∧
        (‖V‖ ≤ Real.sqrt ((∑ i, P.π i / factorialWeightMin ρ (k)) *
          (2 * massNormSq ρ P.π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2))) ∧
        (∀ i, ∀ ζ : TorusHk 1 (h i),
          inner ℝ (coupledLowValueCLM (h := h) (fun _ => k) i V) (torusHkValueCLM ζ) -
            inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM ζ) =
            P.kernelIntegratedRhs t v F g U i ζ)) := by
  classical
  choose y hy using (fun N => P.kernelFourierODE_exists_bochner_bound N v hv hvp F g αv B lam
    hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f hF hg)
  let M : ℝ := ((∑ i, P.π i) * (b - a) + (∑ i, P.π i / factorialWeightMin ρ (k)) * (2 / ν)) *
          (2 * massNormSq ρ P.π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2)
  have hnorm (N : ℕ) : ‖plainHigherBochner N (fun _ => k) a b P.htime (y N)‖ ≤ Real.sqrt M := by
    have hs := (hy N).2.2.2
    change _ ≤ M at hs
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hs
  obtain ⟨U, φ, hφ, hclm⟩ := exists_strictMono_tendsto_highTime_clm (fun _ => k) a b (Real.sqrt M)
    (fun N => plainHigherBochner N (fun _ => k) a b P.htime (y N)) hnorm
  refine ⟨y, U, φ, hφ, hy, hclm, fun i => highTimeGraphReadout_memLp (fun _ => k) a b U i, ?_⟩
  constructor
  · apply highTimeGraphReadout_val_ae (fun _ => k) a b hclm
    intro n
    exact plainHigherBochner_graph_ae (φ n) (fun _ => k) a b P.htime (y (φ n))
  · intro t ht
    let C : ℝ := 2 * massNormSq ρ P.π (fun i => (f i).val) +
      (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
      10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2
    have he (n : ℕ) : massNormSq ρ P.π (fun i => (coupledPlainSynthesis (φ n) i (k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (φ n)) t)).val) ≤ C := by
      have he := (hy (φ n)).2.2.1 t ht
      have hdiss : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis (φ n) i (k + 1)
            (AVenhance.Infra.ODE.extendCurve P.htime (y (φ n)) s)).val)) :=
        mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
          (integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _))
      change _ ≤ C at he
      linarith
    obtain ⟨V, ψ, hψ, hw, hgraph, hnormV⟩ := plainLower_mass_subsequence (fun _ => k) ρ P.radius_pos P.π P.hπ φ
      (fun n => AVenhance.Infra.ODE.extendCurve P.htime (y (φ n)) t) C he
    refine ⟨V, ψ, hψ, hw, hgraph, ?_, hnormV, ?_⟩
    · intro hta
      subst t
      have hinitial (N : ℕ) : AVenhance.Infra.ODE.extendCurve P.htime (y N) a =
          plainInitialCoefficients N (fun _ => k) f := by
        simpa only [intervalIntegral.integral_same, add_zero] using (hy N).1 a ⟨le_rfl, P.htime⟩
      apply plainInitialLower_subsubsequence_eq (fun _ => k) f φ ψ hφ hψ V
      intro ell
      simpa only [hinitial] using hw ell
    · intro i ζ
      let Qlo : ℝ := ∑ j, P.π j / factorialWeightMin ρ (k)
      have hQlo : 0 ≤ Qlo := Finset.sum_nonneg (fun j _ =>
        div_nonneg (P.hπ j).le (factorialWeightMin_pos ρ P.radius_pos (K := k)).le)
      have hl (n : ℕ) : ‖plainLowerSynthesisCLM (φ (ψ n)) (fun _ => k)
          (AVenhance.Infra.ODE.extendCurve P.htime (y (φ (ψ n))) t)‖ ≤ Real.sqrt (Qlo * C) := by
        have hsq := (plainLowerSynthesis_normSq_le_mass (φ (ψ n)) (fun _ => k) ρ P.radius_pos P.π P.hπ
          (AVenhance.Infra.ODE.extendCurve P.htime (y (φ (ψ n))) t)).trans
          (mul_le_mul_of_nonneg_left (he (ψ n)) hQlo)
        simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq
      exact P.kernelClosedTrace_component_identity t ht v hv_bdd hv_meas
        (fun r hr => (hv r hr).continuous) F g hF hg f
        (φ ∘ ψ) (hφ.comp hψ) (fun n => y (φ (ψ n))) (fun n => (hy (φ (ψ n))).1)
        U (Real.sqrt M) (fun n => hnorm (φ (ψ n)))
        (fun ell => (hclm ell).comp hψ.tendsto_atTop)
        V (Real.sqrt (Qlo * C)) hl hw i ζ

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! Energy absorption with the actual kernel flux bound. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)


theorem kernelRhs_component_perturbed_le (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (c : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk k (h i)) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M ε : ℝ) (hε : 0 < ε)
    (hM : Real.sqrt (massNormSq ρ P.π (fun j => (coupledPlainSynthesis N j k c).val)) ≤ M)
    (i : ι) :
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i k
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k c).val) +
      (3 * ν / 4 - ε / 2) * gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) c).val ≤
    |P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) c) i t| +
      P.π i * M * Real.sqrt (massNormSq ρ P.π (fun j => (g j).val)) +
      (P.π i / (2 * ε)) * massNormSq ρ P.π (fun j => (F j).val) := by
  let U := fun j => (coupledPlainSynthesis N j k c).val
  let R := gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) c).val
  have hR : 0 ≤ R := by
    change 0 ≤ gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) c).val
    rw [← coupledPlainGradientHk_factorialNormSq]
    exact factorialNormSq_nonneg ρ _
  have hG := componentFactorialPairing_abs_le_mass ρ P.π P.hπ (fun j => (g j).val) U i
  have hGb := mul_le_mul_of_nonneg_left hM
    (mul_nonneg (P.hπ i).le (Real.sqrt_nonneg (massNormSq ρ P.π (fun j => (g j).val))))
  have hV := coupledPlainDriftHk_energy_abs_le (le_refl k) N c i ρ αv B lam ν
    P.radius_pos hα hB hlam P.diffusivity_pos hsmall hstrain (v t) hv hvp hd hjets
  rw [← factorialWeightedJet_inner] at hV
  have hF := factorialPairing_abs_le ρ (F i).val (coupledPlainGradientHk N c i k).val
  rw [← factorialWeightedJet_inner, coupledPlainGradientHk_factorialNormSq] at hF
  have hy := coupledFluxYoung (show 0 < 4 * ε by positivity)
    (Real.sqrt (factorialNormSq ρ (F i).val)) (Real.sqrt R)
  rw [Real.sq_sqrt (factorialNormSq_nonneg ρ _), Real.sq_sqrt hR] at hy
  have hf := componentFactorial_le_mass ρ P.π P.hπ (fun j => (F j).val) i
  have hcoef : 2 / (4 * ε) = 1 / (2 * ε) := by field_simp; ring
  rw [hcoef] at hy
  have hf' := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 1 / (2 * ε))
  have hfc : (1 / (2 * ε)) * (P.π i * massNormSq ρ P.π (fun j => (F j).val)) =
      (P.π i / (2 * ε)) * massNormSq ρ P.π (fun j => (F j).val) := by ring
  rw [hfc] at hf'
  have hcp : P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) c) i t =
      inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
        (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i k).val) := by
    simp only [carrierPair, carrierFlux_of_mem P _ i t ht, torusFactorialReadout_apply,
      torusFactorialGradientReadout_apply, coefficientSynthesis,
      coupledPlainGradientHk_eq_gradientTensor]
    rfl
  rw [P.kernelRhs_factorial_energy_identity N v t ht hv hvp c F g i, hcp]
  change _ + (3 * ν / 4 - ε / 2) * R ≤ _
  have hGpos := le_abs_self (inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)))
  have hVneg := neg_le_abs (inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i k (v t) hv hvp).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)))
  have hCneg := neg_le_abs (P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) c) i t)
  rw [hcp] at hCneg
  have hFneg := neg_le_abs (inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i k).val))
  dsimp only [U, R] at *
  linarith

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! The solved kernel coefficient ODE has the native differential mass estimate. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
theorem noLocalSeminorm (i j : ι) (d : admissibleOrders (fun _ => k) 0 i j) :
    coefficientSeminorm ρ k a b (noLocalCoefficient (h := h) i j d) ≠ ⊤ :=
  (noLocalOrders (k := k) i j d).elim

omit [DecidableEq ι] [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
theorem noLocalSmoothOnInterval (t : ℝ) (_ht : t ∈ Set.Icc a b) (i j : ι)
    (d : admissibleOrders (fun _ => k) 0 i j) :
    ContDiff ℝ (k : ℕ) (noLocalCoefficient (h := h) i j d t) :=
  (noLocalOrders (k := k) i j d).elim

omit [DecidableEq ι] [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
theorem noLocalPeriodicOnInterval (t : ℝ) (_ht : t ∈ Set.Icc a b) (i j : ι)
    (d : admissibleOrders (fun _ => k) 0 i j) :
    AVenhance.IsZ2Periodic (noLocalCoefficient (h := h) i j d t) :=
  (noLocalOrders (k := k) i j d).elim

omit [DecidableEq ι] [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
theorem noLocalMeasurable (i j : ι) (d : admissibleOrders (fun _ => k) 0 i j) :
    Measurable (fun p : Set.Icc a b × Vec 2 => noLocalCoefficient (h := h) i j d p.1 p.2) :=
  (noLocalOrders (k := k) i j d).elim

def diffusionResidual (z : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (i : ι) (t : ℝ) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  torusSpatialFluxPath (fun _ => k) 0 a b ν ρ P.radius_pos noLocalCoefficient
    noLocalSeminorm noLocalSmoothOnInterval noLocalPeriodicOnInterval z i t

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end

section
/-! The solved kernel coefficient ODE has the native differential mass estimate. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))

include hv hvp in
theorem kernelForcedWeakSolution_residualODE
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f F g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∃ y : ℝ → CoupledPlainCoefficients (h := h) N,
      Continuous y ∧ (∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun i => u i t)) ∧
      (∀ i, MemLp (fun t => RF i t - P.finiteFlux N y i t) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ i, Integrable (Rg i) (volume.restrict (Set.Icc a b))) ∧
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k)
          (fun i => RF i t - P.finiteFlux N y i t) (fun i => Rg i t))
        (plainInitialCoefficients N (fun _ => k) f) a b y ∧
      IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k)
          (fun i => RF i t - P.finiteFlux N y i t) (fun i => Rg i t)) y) volume a b := by
  dsimp only
  let z := fun i t => w i t - galerkinProj (E := h i) (K := k + 1) N (w i t)
  let hA := noLocalSeminorm (h := h) (ρ := ρ) (a := a) (b := b) (k := k)
  let hc := noLocalSmoothOnInterval (h := h) (a := a) (b := b) (k := k)
  let hp := noLocalPeriodicOnInterval (h := h) (a := a) (b := b) (k := k)
  let RF := fun i t => F i t + P.diffusionResidual z i t
  let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
  have hz (i : ι) : MemLp (z i) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub (volume.restrict (Set.Icc a b)) 2 (w i)
      (fun t => galerkinProj (E := h i) (K := k + 1) N (w i t)) (hsol.2.1 i)
      ((galerkinProj (E := h i) (K := k + 1) N).comp_memLp' (hsol.2.1 i))
  have hRF (i : ι) : MemLp (RF i) 2 (volume.restrict (Set.Icc a b)) :=
    torusForcedSpatialFluxPath_memLp (fun _ => k) 0 a b ν ρ P.radius_pos
      noLocalCoefficient hA hc hp P.htime
      (fun i j d => (noLocalOrders (k := k) i j d).elim) z hz F hF i
  have hRg (i : ι) : Integrable (Rg i) (volume.restrict (Set.Icc a b)) := by
    have ht := plainTransportCarrierPath_memLp (fun _ => k) a b v hv hvp T hT P.htime
      ρ P.radius_pos hv_meas V hV hvb z hz i
    exact timeIntegrable_pointwise_sub _ (g i) _ (hg i) (ht.integrable (by norm_num))
  obtain ⟨y, hycont, hy, hint, hode⟩ := plainWeakSolution_residualODE_exists N (fun _ => k) 0 ν ρ
    P.radius_pos a b P.htime v hv_meas hv hvp V hV hvb T hT noLocalCoefficient hA
    (fun i j d => (noLocalOrders (k := k) i j d).elim) hc hp F g w u f hF hg hsol
  have hRFnew (i : ι) : MemLp (fun t => RF i t - P.finiteFlux N y i t) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub _ 2 (RF i) (P.finiteFlux N y i) (hRF i) (P.finiteFlux_memLp N y hycont i)
  have hkODE := P.kernelODE_from_forced_diffusionDrift N v RF Rg y _ hode
  have hkint := P.kernelLinearRhs_sub_flux_intervalIntegrable N v RF Rg y hint
  exact ⟨y, hycont, hy, hRFnew, hRg, hkODE, hkint⟩

end TorusKernelOperator
end AVRegularity.KernelEnergy
end
end
