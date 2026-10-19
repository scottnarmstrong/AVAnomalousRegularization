-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.PlaneCoefficientRows
import AVRegularity.CoupledEnergyPlane.Transport.CarrierTransport
public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The empty stored word recovers exactly the original value, flux and H1 slice. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetFluxOperator_order_zero (K : ℕ)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    planeJetFluxOperator K (valueIndex2 K) S = planeFluxValueOperator K S := by
  apply PiLp.ext
  intro k
  apply Lp.ext
  exact (planeJetFluxOperator_ae (valueIndex2 K) S k).trans
    (planeFluxValueOperator_ae K S k).symm

theorem planeWordH1Slice_order_zero (K : ℕ) (W : PlaneHk Set.univ (K + 1) E) :
    planeWordH1SliceOperator K (valueIndex2 K) W = truncatePlaneHk (by omega) W := by
  apply PlaneHk.ext_value isOpen_univ
  have h := planeWordH1Slice_value K (valueIndex2 K) W
  apply univToPlane.injective
  exact h

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Literal scalar plane multipliers are self-adjoint and compose by multiplying coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Real scalar multiplication is self-adjoint on plane `L²`. -/
theorem planeScalarMultiplier_inner
    (c : Vec 2 → ℝ) (hc : Continuous c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M)
    (u z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeScalarMultiplier c hc hM hb u) z =
      inner ℝ u (planeScalarMultiplier c hc hM hb z) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarMultiplier_ae c hc hM hb u,
    planeScalarMultiplier_ae c hc hM hb z] with x hu hz
  rw [hu, hz, real_inner_smul_left, real_inner_smul_right]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The continuous Hilbert adjoint is the same actual scalar multiplier. -/
theorem planeScalarMultiplier_adjoint
    (c : Vec 2 → ℝ) (hc : Continuous c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M) :
    (planeScalarMultiplier (E := E) c hc hM hb).adjoint =
      planeScalarMultiplier (E := E) c hc hM hb := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (planeScalarMultiplier_inner c hc hM hb u z).symm

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Squaring the multiplier squares its literal scalar coefficient almost everywhere. -/
theorem planeScalarMultiplier_square_ae
    (c : Vec 2 → ℝ) (hc : Continuous c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeScalarMultiplier c hc hM hb (planeScalarMultiplier c hc hM hb u) =ᵐ[volume]
      fun x => c x ^ 2 • u x := by
  filter_upwards [planeScalarMultiplier_ae c hc hM hb (planeScalarMultiplier c hc hM hb u),
    planeScalarMultiplier_ae c hc hM hb u] with x hout hin
  rw [hout, hin, smul_smul, pow_two]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The multiplier norm is exactly the weighted `L²` energy of its representative. -/
theorem planeScalarMultiplier_normSq
    (c : Vec 2 → ℝ) (hc : Continuous c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    ‖planeScalarMultiplier c hc hM hb u‖ ^ 2 = ∫ x, c x ^ 2 * ‖u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarMultiplier_ae c hc hM hb u] with x hx
  rw [hx, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! Continuous dependence of the literal plane multiplier on a bounded scalar field. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

def boundedScalarMultiplier (c : BoundedContinuousFunction (Vec 2) ℝ) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  planeScalarMultiplier c c.continuous (norm_nonneg c)
    (fun x => by simpa only [Real.norm_eq_abs] using c.norm_coe_le_norm x)

theorem boundedScalarMultiplier_ae (c : BoundedContinuousFunction (Vec 2) ℝ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    boundedScalarMultiplier c u =ᵐ[volume] fun x => c x • u x :=
  planeScalarMultiplier_ae _ _ _ _ _

theorem boundedScalarMultiplier_add (c d : BoundedContinuousFunction (Vec 2) ℝ) :
    boundedScalarMultiplier (E := E) (c + d) =
      boundedScalarMultiplier c + boundedScalarMultiplier d := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedScalarMultiplier_ae (c + d) u,
    boundedScalarMultiplier_ae c u, boundedScalarMultiplier_ae d u,
    Lp.coeFn_add (boundedScalarMultiplier c u) (boundedScalarMultiplier d u)]
    with x hcd hc hd hs
  change boundedScalarMultiplier (c + d) u x =
    (boundedScalarMultiplier c u + boundedScalarMultiplier d u) x
  rw [hs, hcd]
  simp only [Pi.add_apply]
  rw [hc, hd]
  exact add_smul _ _ _

theorem boundedScalarMultiplier_smul (r : ℝ) (c : BoundedContinuousFunction (Vec 2) ℝ) :
    boundedScalarMultiplier (E := E) (r • c) = r • boundedScalarMultiplier c := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedScalarMultiplier_ae (r • c) u,
    boundedScalarMultiplier_ae c u, Lp.coeFn_smul r (boundedScalarMultiplier c u)]
    with x hr hc hs
  change boundedScalarMultiplier (r • c) u x = (r • boundedScalarMultiplier c u) x
  rw [hs, hr]
  simp only [Pi.smul_apply]
  rw [hc]
  change (r * c x) • u x = r • (c x • u x)
  exact (smul_smul r (c x) (u x)).symm

theorem boundedScalarMultiplier_norm_le (c : BoundedContinuousFunction (Vec 2) ℝ) :
    ‖boundedScalarMultiplier (E := E) c‖ ≤ 1 * ‖c‖ := by
  simpa only [one_mul, boundedScalarMultiplier] using
    planeScalarMultiplier_norm_le (E := E) c c.continuous (norm_nonneg c)
      (fun x => by simpa only [Real.norm_eq_abs] using c.norm_coe_le_norm x)

def boundedScalarMultiplierLinearMap : BoundedContinuousFunction (Vec 2) ℝ →ₗ[ℝ]
    (Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2))) where
  toFun := boundedScalarMultiplier (E := E)
  map_add' := boundedScalarMultiplier_add
  map_smul' := boundedScalarMultiplier_smul

def boundedScalarMultiplierMap : BoundedContinuousFunction (Vec 2) ℝ →L[ℝ]
    (Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2))) :=
  @LinearMap.mkContinuous ℝ ℝ
    (BoundedContinuousFunction (Vec 2) ℝ)
    (Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    _ _ _ _ _ _ (RingHom.id ℝ) (boundedScalarMultiplierLinearMap (E := E)) 1
    (boundedScalarMultiplier_norm_le (E := E))

theorem boundedScalarMultiplier_normSq (c : BoundedContinuousFunction (Vec 2) ℝ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    ‖boundedScalarMultiplier c u‖ ^ 2 = ∫ x, c x ^ 2 * ‖u x‖ ^ 2 :=
  planeScalarMultiplier_normSq _ _ _ _ _

theorem boundedScalarMultiplier_inner_same (c d : BoundedContinuousFunction (Vec 2) ℝ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (boundedScalarMultiplier c u) (boundedScalarMultiplier d u) =
      ∫ x, c x * d x * ‖u x‖ ^ 2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedScalarMultiplier_ae c u, boundedScalarMultiplier_ae d u]
    with x hc hd
  rw [hc, hd, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Actual measurable drift and metric operators for the scalar plane equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The actual transport operator applies the velocity components to the weak gradient. -/
def planeScalarTransport (v : Vec 2 → Vec 2)
    (hc : ∀ k, Continuous (fun z => v z k)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k z, |v z k| ≤ M) :
    PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  planeTransportRow fun k => planeScalarMultiplier (fun z => v z k) (hc k) hM (hb k)

/-- The actual diffusion operator applies the metric matrix to the weak gradient. -/
def planeScalarDiffusion (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ k j, Continuous (fun z => G z k j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k j z, |G z k j| ≤ M) : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  planeDiffusionRows fun k j => planeScalarMultiplier (fun z => G z k j) (hc k j) hM (hb k j)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarTransport_norm_le (v : Vec 2 → Vec 2)
    (hc : ∀ k, Continuous (fun z => v z k)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k z, |v z k| ≤ M) : ‖planeScalarTransport (E := E) v hc hM hb‖ ≤ 2 * M :=
  planeTransportRow_norm_le _ hM (fun _k => planeScalarMultiplier_norm_le _ _ _ _)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarDiffusion_norm_le (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ k j, Continuous (fun z => G z k j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k j z, |G z k j| ≤ M) : ‖planeScalarDiffusion (E := E) G hc hM hb‖ ≤ 4 * M :=
  planeDiffusionRows_norm_le _ hM (fun _k _j => planeScalarMultiplier_norm_le _ _ _ _)

omit [BorelSpace E] [CompleteSpace E] in
theorem planeScalarTransport_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (v : T → Vec 2 → Vec 2) (hc : ∀ t k, Continuous (fun z => v t z k))
    (hj : ∀ k, Measurable (fun p : T × Vec 2 => v p.1 p.2 k))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t k z, |v t z k| ≤ M) (u : PlaneFluxL2 E) :
    StronglyMeasurable (fun t => planeScalarTransport (v t) (hc t) hM (hb t) u) :=
  planeTransportRow_stronglyMeasurable _
    (fun k z => planeScalarMultiplier_stronglyMeasurable _ (fun t => hc t k)
      (hj k) hM (fun t => hb t k) z) u

omit [BorelSpace E] [CompleteSpace E] in
theorem planeScalarDiffusion_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ t k j, Continuous (fun z => G t z k j))
    (hj : ∀ k j, Measurable (fun p : T × Vec 2 => G p.1 p.2 k j))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t k j z, |G t z k j| ≤ M) (u : PlaneFluxL2 E) :
    StronglyMeasurable (fun t => planeScalarDiffusion (G t) (hc t) hM (hb t) u) :=
  planeDiffusionRows_stronglyMeasurable _
    (fun k j z => planeScalarMultiplier_stronglyMeasurable _ (fun t => hc t k j)
      (hj k j) hM (fun t => hb t k j) z) u

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The transport row has the literal pointwise drift action almost everywhere. -/
theorem planeScalarTransport_ae (v : Vec 2 → Vec 2)
    (hc : ∀ k, Continuous (fun z => v z k)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k z, |v z k| ≤ M) (u : PlaneFluxL2 E) :
    planeScalarTransport v hc hM hb u =ᵐ[volume]
      fun z => ∑ k : Fin 2, v z k • u k z := by
  let L (k : Fin 2) := planeScalarMultiplier (E := E) (fun z => v z k) (hc k) hM (hb k)
  change (planeTransportRow L) u =ᵐ[volume] _
  rw [planeTransportRow_apply]
  have hm : ∀ᵐ z ∂volume, ∀ k : Fin 2, L k (u k) z = v z k • u k z :=
    ae_all_iff.mpr (fun k => planeScalarMultiplier_ae _ _ _ _ _)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => L k (u k)), hm] with z hz hmz
  simp only [Finset.sum_apply] at hz
  exact hz.trans (Finset.sum_congr rfl (fun k _ => hmz k))

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Every diffusion component is the literal metric action almost everywhere. -/
theorem planeScalarDiffusion_ae (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ k j, Continuous (fun z => G z k j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k j z, |G z k j| ≤ M) (u : PlaneFluxL2 E) (k : Fin 2) :
    planeScalarDiffusion G hc hM hb u k =ᵐ[volume]
      fun z => ∑ j : Fin 2, G z k j • u j z := by
  let L (j : Fin 2) := planeScalarMultiplier (E := E) (fun z => G z k j) (hc k j) hM (hb k j)
  change (planeDiffusionRows (fun k j =>
    planeScalarMultiplier (E := E) (fun z => G z k j) (hc k j) hM (hb k j)) u) k =ᵐ[volume] _
  rw [planeDiffusionRows_apply]
  have hm : ∀ᵐ z ∂volume, ∀ j : Fin 2, L j (u j) z = G z k j • u j z :=
    ae_all_iff.mpr (fun j => planeScalarMultiplier_ae _ _ _ _ _)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => L j (u j)), hm] with z hz hmz
  simp only [Finset.sum_apply] at hz
  exact hz.trans (Finset.sum_congr rfl (fun j _ => hmz j))

/-- The actual measurable drift and metric give an `L²` time Riesz dual. -/
theorem planeScalarDual_memLp {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (v : T → Vec 2 → Vec 2) (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hvc : ∀ t k, Continuous (fun z => v t z k))
    (hGc : ∀ t k j, Continuous (fun z => G t z k j))
    (hvm : ∀ k, Measurable (fun p : T × Vec 2 => v p.1 p.2 k))
    (hGm : ∀ k j, Measurable (fun p : T × Vec 2 => G p.1 p.2 k j))
    {Mv MG : ℝ} (hMv : 0 ≤ Mv) (hMG : 0 ≤ MG)
    (hvb : ∀ t k z, |v t z k| ≤ Mv) (hGb : ∀ t k j z, |G t z k j| ≤ MG)
    (u : T → PlaneHk Set.univ 1 E) (F : T → PlaneFluxL2 E)
    (hu : MemLp u 2 μ) (hF : MemLp F 2 μ) :
    MemLp (fun t => planeWeakDualRepresentative
      (planeScalarTransport (v t) (hvc t) hMv (hvb t))
      (planeScalarDiffusion (G t) (hGc t) hMG (hGb t)) (u t) (F t)) 2 μ :=
  planeWeakDualRepresentative_memLp_of_operator_bounds _ _
    (planeScalarTransport_stronglyMeasurable v hvc hvm hMv hvb)
    (planeScalarDiffusion_stronglyMeasurable G hGc hGm hMG hGb)
    (by positivity) (by positivity)
    (fun t => planeScalarTransport_norm_le _ _ _ _)
    (fun t => planeScalarDiffusion_norm_le _ _ _ _) u F hu hF

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Actual principal transport and diffusion actions preserve the time energy class separately. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarActions_memLp {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (v : T → Vec 2 → Vec 2) (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hvc : ∀ t k, Continuous (fun z => v t z k))
    (hGc : ∀ t k j, Continuous (fun z => G t z k j))
    (hvm : ∀ k, Measurable (fun p : T × Vec 2 => v p.1 p.2 k))
    (hGm : ∀ k j, Measurable (fun p : T × Vec 2 => G p.1 p.2 k j))
    {Mv MG : ℝ} (hMv : 0 ≤ Mv) (hMG : 0 ≤ MG)
    (hvb : ∀ t k z, |v t z k| ≤ Mv) (hGb : ∀ t k j z, |G t z k j| ≤ MG)
    (u : T → PlaneHk Set.univ 1 E) (hu : MemLp u 2 μ) :
    MemLp (fun t => planeScalarTransport (v t) (hvc t) hMv (hvb t)
      (planeH1GradientOperator (u t))) 2 μ ∧
    MemLp (fun t => planeScalarDiffusion (G t) (hGc t) hMG (hGb t)
      (planeH1GradientOperator (u t))) 2 μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  let : SecondCountableTopology (PlaneFluxL2 E) := PiLp.secondCountableTopology 2 _
  borelize (PlaneFluxL2 E)
  have hgrad := (planeH1GradientOperator (E := E)).comp_memLp' hu
  let LT : T → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
    fun t => planeScalarTransport (v t) (hvc t) hMv (hvb t)
  let LD : T → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
    fun t => planeScalarDiffusion (G t) (hGc t) hMG (hGb t)
  have htm : ∀ z, StronglyMeasurable (fun t => LT t z) :=
    planeScalarTransport_stronglyMeasurable (E := E) v hvc hvm hMv hvb
  have hdm : ∀ z, StronglyMeasurable (fun t => LD t z) :=
    planeScalarDiffusion_stronglyMeasurable (E := E) G hGc hGm hMG hGb
  have htb : ∀ t, ‖LT t‖ ≤ 2 * Mv :=
    fun t => planeScalarTransport_norm_le (E := E) (v t) (hvc t) hMv (hvb t)
  have hdb : ∀ t, ‖LD t‖ ≤ 4 * MG :=
    fun t => planeScalarDiffusion_norm_le (E := E) (G t) (hGc t) hMG (hGb t)
  constructor
  · exact memLp_operator_action LT htm hgrad (mul_nonneg (by norm_num) hMv) htb
  · exact memLp_operator_action LD hdm hgrad (mul_nonneg (by norm_num) hMG) hdb

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Literal spatial integrals represented by the bounded scalar weak operators. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Finite component flux pairings are their actual plane spatial integrals. -/
theorem planeFlux_inner_eq_integral (u z : PlaneFluxL2 E) :
    inner ℝ u z = ∫ x, ∑ k : Fin 2, inner ℝ (u k x) (z k x) := by
  rw [PiLp.inner_apply]
  simp only [L2.inner_def]
  exact (integral_finsetSum Finset.univ (fun k _ => L2.integrable_inner (u k) (z k))).symm

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The transport Hilbert pairing has the literal drift integrand. -/
theorem planeScalarTransport_inner_eq_integral (v : Vec 2 → Vec 2)
    (hc : ∀ k, Continuous (fun z => v z k)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k z, |v z k| ≤ M)
    (u : PlaneFluxL2 E) (z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeScalarTransport v hc hM hb u) z =
      ∫ x, ∑ k : Fin 2, v x k * inner ℝ (u k x) (z x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarTransport_ae v hc hM hb u] with x hx
  rw [hx]
  simp only [sum_inner, real_inner_smul_left]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The diffusion Hilbert pairing has the literal metric integrand. -/
theorem planeScalarDiffusion_inner_eq_integral (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ k j, Continuous (fun x => G x k j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k j x, |G x k j| ≤ M) (u z : PlaneFluxL2 E) :
    inner ℝ (planeScalarDiffusion G hc hM hb u) z =
      ∫ x, ∑ k : Fin 2, ∑ j : Fin 2, G x k j * inner ℝ (u j x) (z k x) := by
  rw [planeFlux_inner_eq_integral]
  have hm : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeScalarDiffusion G hc hM hb u k x = ∑ j : Fin 2, G x k j • u j x :=
    ae_all_iff.mpr (fun k => planeScalarDiffusion_ae G hc hM hb u k)
  apply integral_congr_ae
  filter_upwards [hm] with x hx
  apply Finset.sum_congr rfl
  intro k _
  rw [hx k]
  simp only [sum_inner, real_inner_smul_left]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.Weighted

/-! Actual compact scalar multipliers have the time regularity required by the weak energy test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

set_option backward.isDefEq.respectTransparency false in
theorem compactScalarMultiplier_time
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (a b : ℝ) :
    ∃ (c dc : ℝ → BoundedContinuousFunction (Vec 2) ℝ) (M Md : ℝ),
      (∀ t x, c t x = f (t, x)) ∧
      (∀ t x, dc t x = fderiv ℝ f (t, x) (1, 0)) ∧
      0 ≤ M ∧ 0 ≤ Md ∧ (∀ t, ‖boundedScalarMultiplier (E := E) (c t)‖ ≤ M) ∧
      (∀ t, ‖boundedScalarMultiplier (E := E) (dc t)‖ ≤ Md) ∧
      AbsolutelyContinuousOnInterval (fun t => boundedScalarMultiplier (E := E) (c t)) a b ∧
      (∀ t, HasDerivAt (fun s => boundedScalarMultiplier (E := E) (c s))
        (boundedScalarMultiplier (E := E) (dc t)) t) := by
  obtain ⟨c, dc, hc, hdc, hd⟩ := compactScalarFamily_differentiable f hf hs
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hs
  have hD : Continuous (fun p : ℝ × Vec 2 => fderiv ℝ f p (1, 0)) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨Md, hMd⟩ := hD.bounded_above_of_compact_support (hs.fderiv_apply ℝ (1, 0))
  have hcb t : ‖c t‖ ≤ max 0 M := by
    apply (BoundedContinuousFunction.norm_le (le_max_left 0 M)).2
    intro x
    rw [hc]
    exact (hM (t, x)).trans (le_max_right 0 M)
  have hdcb t : ‖dc t‖ ≤ max 0 Md := by
    apply (BoundedContinuousFunction.norm_le (le_max_left 0 Md)).2
    intro x
    rw [hdc]
    exact (hMd (t, x)).trans (le_max_right 0 Md)
  have hder t : HasDerivAt (fun s => boundedScalarMultiplier (E := E) (c s))
      (boundedScalarMultiplier (E := E) (dc t)) t := by
    have hh := HasFDerivAt.comp_hasDerivAt
      (F := BoundedContinuousFunction (Vec 2) ℝ)
      (E := Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
      t (boundedScalarMultiplierMap (E := E)).hasFDerivAt (hd t)
    convert hh using 1 <;> rfl
  have hAb t : ‖boundedScalarMultiplier (E := E) (c t)‖ ≤ max 0 M :=
    (boundedScalarMultiplier_norm_le (E := E) (c t)).trans (by simpa only [one_mul] using hcb t)
  have hdAb t : ‖boundedScalarMultiplier (E := E) (dc t)‖ ≤ max 0 Md :=
    (boundedScalarMultiplier_norm_le (E := E) (dc t)).trans (by simpa only [one_mul] using hdcb t)
  have hAC := bounded_derivative_absolutelyContinuous
    (fun t => boundedScalarMultiplier (E := E) (c t))
    (fun t => boundedScalarMultiplier (E := E) (dc t)) hder (le_max_left 0 Md) hdAb a b
  exact ⟨c, dc, max 0 M, max 0 Md, hc, hdc, le_max_left 0 M, le_max_left 0 Md,
    hAb, hdAb, hAC, hder⟩

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Integration by parts of squared Hilbert-valued weak functions against compact fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem weak_hilbert_gradient_mul_compact
    {u : Vec 2 → E} {g : Fin 2 → Vec 2 → E}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i e, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (u x)) (fun x => inner ℝ e (g i x)))
    (c : Fin 2 → Vec 2 → ℝ) (hc : ∀ i, ContDiff ℝ 1 (c i))
    (hs : ∀ i, HasCompactSupport (c i)) :
    2 * (∫ x, inner ℝ (∑ i : Fin 2, c i x • g i x) (u x)) =
      -(∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) * ‖u x‖ ^ 2) := by
  let b := stdOrthonormalBasis ℝ E
  let U := fun (k : Fin (Module.finrank ℝ E)) x => inner ℝ (b k) (u x)
  let G := fun (k : Fin (Module.finrank ℝ E)) i x => inner ℝ (b k) (g i x)
  let dc := fun x => ∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)
  have hU k : MemLp (U k) 2 volume := (InnerProductSpace.toDual ℝ E (b k)).comp_memLp' hu
  have hG k i : MemLp (G k i) 2 volume := (InnerProductSpace.toDual ℝ E (b k)).comp_memLp' (hg i)
  have hcm i : MemLp (c i) ⊤ volume :=
    (hc i).continuous.memLp_top_of_hasCompactSupport (hs i) volume
  have hdcm : MemLp dc ⊤ volume := by
    apply memLp_finsetSum
    intro i _
    exact (((hc i).continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      ((hs i).fderiv_apply ℝ (basisVec i)) volume
  have hI k : Integrable (fun x => (∑ i : Fin 2, c i x * G k i x) * U k x) volume := by
    have hm : MemLp (fun x => ∑ i : Fin 2, c i x * G k i x) 2 volume :=
      memLp_finsetSum _ (fun i _ => (hcm i).fun_mul (hG k i))
    exact memLp_one_iff_integrable.mp (hm.fun_mul (hU k))
  have hJ k : Integrable (fun x => dc x * U k x ^ 2) volume := by
    have hdu : MemLp (fun x => dc x * U k x) 2 volume := hdcm.fun_mul (hU k)
    have hm := memLp_one_iff_integrable.mp
      (hdu.fun_mul (hU k) : MemLp _ 1 volume)
    simpa only [pow_two, mul_assoc] using hm
  have he x : inner ℝ (∑ i : Fin 2, c i x • g i x) (u x) =
      ∑ k : Fin (Module.finrank ℝ E), (∑ i : Fin 2, c i x * G k i x) * U k x := by
    rw [← b.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (b k) (∑ i : Fin 2, c i x • g i x)]
    simp only [inner_sum, real_inner_smul_right, U, G]
  have hnorm x : dc x * ‖u x‖ ^ 2 = ∑ k : Fin (Module.finrank ℝ E), dc x * U k x ^ 2 := by
    rw [← b.sum_sq_inner_right, Finset.mul_sum]
  change 2 * (∫ x, inner ℝ (∑ i : Fin 2, c i x • g i x) (u x)) =
    -(∫ x, dc x * ‖u x‖ ^ 2)
  simp_rw [he, hnorm]
  rw [integral_finsetSum _ (fun k _ => hI k), integral_finsetSum _ (fun k _ => hJ k),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact AVRegularity.CoupledEnergyPlane.Transport.weak_gradient_mul_compact
    (hU k) (hG k) (fun i => hw i (b k)) hc hs

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The scalar Riesz dual represents one literal, integrable spatial weak RHS. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- The scalar dual pairing is the spatial integral of its actual drift and total flux representatives. -/
theorem planeScalarDual_pair_eq_integral
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ k j, Continuous (fun x => G x k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (u φ : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v hvc hMv hvb) (planeScalarDiffusion G hGc hMG hGb) u F) φ =
      ∫ x, -(∑ k : Fin 2, v x k * inner ℝ
        (planeH1GradientOperator (E := E) u k x) (planeHkValueOperator (E := E) 1 φ x))
        - ∑ k : Fin 2, inner ℝ
          ((∑ j : Fin 2, G x k j • planeH1GradientOperator (E := E) u j x) + F k x)
          (planeH1GradientOperator (E := E) φ k x) := by
  let T := planeScalarTransport v hvc hMv hvb (planeH1GradientOperator (E := E) u)
  let Q := planeScalarDiffusion G hGc hMG hGb (planeH1GradientOperator (E := E) u) + F
  let z := planeHkValueOperator (E := E) 1 φ
  let dz := planeH1GradientOperator (E := E) φ
  have hQ : Integrable (fun x => ∑ k : Fin 2, inner ℝ (Q k x) (dz k x)) volume :=
    integrable_finsetSum _ (fun k _ => L2.integrable_inner (Q k) (dz k))
  rw [planeWeakDualRepresentative_pair, L2.inner_def, planeFlux_inner_eq_integral,
    ← integral_neg]
  change (∫ x, -inner ℝ (T x) (z x)) -
    (∫ x, ∑ k : Fin 2, inner ℝ (Q k x) (dz k x)) = _
  rw [← integral_sub (f := fun x => -inner ℝ (T x) (z x))
    (g := fun x => ∑ k : Fin 2, inner ℝ (Q k x) (dz k x))
    (L2.integrable_inner T z).neg hQ]
  have ht := planeScalarTransport_ae v hvc hMv hvb (planeH1GradientOperator (E := E) u)
  have hd : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      Q k x = (∑ j : Fin 2, G x k j • planeH1GradientOperator (E := E) u j x) + F k x := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_add
      (planeScalarDiffusion G hGc hMG hGb (planeH1GradientOperator (E := E) u) k) (F k),
      planeScalarDiffusion_ae G hGc hMG hGb (planeH1GradientOperator (E := E) u) k]
      with x ha hm
    exact ha.trans (congrArg (fun q => q + F k x) hm)
  apply integral_congr_ae
  filter_upwards [ht, hd] with x htx hdx
  change -inner ℝ (T x) (z x) - (∑ k : Fin 2, inner ℝ (Q k x) (dz k x)) = _
  rw [htx]
  simp only [sum_inner, real_inner_smul_left]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun q => inner ℝ q (dz k x)) (hdx k))

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.Weighted

/-! Every stored weak jet is invariant under permutation of derivative positions. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandWordReal_permutation (N : ℕ) {m : ℕ}
    (w z : DerivativeWord2 m) (e : Fin m ≃ Fin m) (he : ∀ k, w k = z (e k))
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N w f = bandWordReal N z f := by
  have hs : bandWordSymbol N w = bandWordSymbol N z := by
    funext ξ
    unfold bandWordSymbol
    apply congrArg (fun g => (angularBand N).indicator g ξ)
    funext η
    exact Fintype.prod_equiv e _ _ (fun k => by rw [he k])
  simp only [bandWordReal, bandWordComplex, hs]

theorem planeHk_jet_permutation {K m : ℕ} (hm : m ≤ K)
    (U : PlaneHk Set.univ K E) (w z : DerivativeWord2 m)
    (e : Fin m ≃ Fin m) (he : ∀ k, w k = z (e k)) :
    U.val ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ =
      U.val ⟨⟨m, Nat.lt_succ_of_le hm⟩, z⟩ := by
  let a : JetIndex2 K := ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩
  let b : JetIndex2 K := ⟨⟨m, Nat.lt_succ_of_le hm⟩, z⟩
  have heN N : (hilbertBandHk N K (univToPlane (U.val (valueIndex2 K)))).val a =
      (hilbertBandHk N K (univToPlane (U.val (valueIndex2 K)))).val b := by
    rw [hilbertBandHk_component, hilbertBandHk_component]
    apply congrArg (planeToUniv (E := E))
    apply fiberCoordinate_ext
    intro k
    rw [hilbertLift_coordinate, hilbertLift_coordinate,
      bandWordRealOperator_apply, bandWordRealOperator_apply]
    exact bandWordReal_permutation N w z e he _
  exact tendsto_nhds_unique (tendsto_hilbertBandHk_component K U a)
    ((tendsto_hilbertBandHk_component K U b).congr (fun N => (heN N).symm))

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Weighted

/-! A leading gradient direction can be moved to the end of a stored weak word. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_jet_cons_eq_snoc {K m : ℕ} (hm : m + 1 ≤ K)
    (U : PlaneHk Set.univ K E) (w : DerivativeWord2 m) (i : Fin 2) :
    U.val ⟨⟨m + 1, Nat.lt_succ_of_le hm⟩, Fin.cons i w⟩ =
      U.val ⟨⟨m + 1, Nat.lt_succ_of_le hm⟩, Fin.snoc w i⟩ := by
  apply planeHk_jet_permutation hm U _ _ (finRotate (m + 1)).symm
  intro k
  have hrot := congrFun (Fin.snoc_eq_cons_rotate w i) ((finRotate (m + 1)).symm k)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hrot.symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Arbitrary ordered cutoff derivatives have the exact signed adjoint pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hilbertWord_zero (N : ℕ) (w : Fin 0 → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w u = hilbertProjection N u := by
  apply fiberCoordinate_ext
  intro k
  rw [hilbertWordOperator_coordinate, hilbertProjection_coordinate,
    bandWordRealOperator_apply, bandWordReal_zero]

theorem hilbertWord_ordered_inner (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (hilbertWordOperator N w u) z =
      (-1 : ℝ) ^ m * inner ℝ u (hilbertWordOperator N w z) := by
  induction m generalizing u z with
  | zero =>
    rw [hilbertWord_zero, hilbertWord_zero, hilbertProjection_inner]
    simp
  | succ m ih =>
    rw [← Fin.snoc_init_self w, ← hilbertWord_single_comp,
      hilbertWord_single_inner, ih, hilbertWord_comm_single,
      hilbertWord_single_comp, pow_succ]
    ring

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Recover a finite factorial norm after reducing its radius. -/

theorem factorial_radius_weight_le (r L : ℝ) (hL : 1 ≤ L)
    {j K : ℕ} (hj : j ≤ K) :
    r ^ (2 * j) / (j.factorial : ℝ) ^ 2 ≤
      L ^ (2 * K) * ((r / L) ^ (2 * j) / (j.factorial : ℝ) ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have he : r ^ (2 * j) / (j.factorial : ℝ) ^ 2 =
      L ^ (2 * j) * ((r / L) ^ (2 * j) / (j.factorial : ℝ) ^ 2) := by
    rw [div_pow]
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 hj))
  apply div_nonneg _ (sq_nonneg _)
  rw [Nat.mul_comm 2 j, pow_mul]
  exact sq_nonneg _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedFactorialNormSq_radius_reserve {K' : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r L : ℝ) (hL : 1 ≤ L)
    (K : ℕ) (U : PlaneHk Set.univ K' E) :
    weightedFactorialNormSq n ϖ zc r K U ≤
      ENNReal.ofReal (L ^ (2 * K)) * weightedFactorialNormSq n ϖ zc (r / L) K U := by
  unfold weightedFactorialNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ (2 * K))]
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (factorial_radius_weight_le r L hL
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

theorem weightedGradFactorialNormSq_radius_reserve {K' : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r L : ℝ) (hL : 1 ≤ L)
    (K : ℕ) (U : PlaneHk Set.univ K' E) :
    weightedGradFactorialNormSq n ϖ zc r K U ≤
      ENNReal.ofReal (L ^ (2 * K)) * weightedGradFactorialNormSq n ϖ zc (r / L) K U := by
  unfold weightedGradFactorialNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ (2 * K))]
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (factorial_radius_weight_le r L hL
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Weighted

/-! Resolve each vector flux component into a fixed Hilbert map. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fluxCoordinateInjection (k : Fin 2) (T : E →L[ℝ] F) :
    E →L[ℝ] PiLp 2 (fun _ : Fin 2 => F) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => if j = k then T else 0)

@[simp] theorem fluxCoordinateInjection_apply (k j : Fin 2) (T : E →L[ℝ] F) (e : E) :
    fluxCoordinateInjection k T e j = if j = k then T e else 0 := by
  simp only [fluxCoordinateInjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply]
  change (if j = k then T else 0) e = _
  split <;> rfl

@[simp] theorem fluxCoordinateInjection_zero (k : Fin 2) :
    fluxCoordinateInjection k (0 : E →L[ℝ] F) = 0 := by
  ext e j
  simp only [fluxCoordinateInjection_apply, zero_apply, PiLp.zero_apply, ite_self]

theorem slowEvalCoefficient_value_expansion {d : ℕ}
    (ev : (Vec 2 → ℝ) → Vec 2 → ℝ) (edge : List (Constituent d E F))
    (t : ℝ) (z : Vec 2) (g : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => E)) :
    slowEvalCoefficient ev edge t z g =
      (edge.map fun γ => ∑ w : DerivativeWord2 (d - 1), ∑ k : Fin 2,
        ev (fun X => γ.coeff w t X z k) z • fluxCoordinateInjection k γ.map (g w)).sum := by
  induction edge with
  | nil => simp [slowEvalCoefficient]
  | cons γ edge ih =>
    simp only [slowEvalCoefficient, List.map_cons, List.sum_cons] at ih ⊢
    rw [add_apply, ih]
    congr 1
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [ContinuousLinearMap.comp_apply, PiLp.continuousLinearEquiv_symm_apply,
      fluxCoordinateInjection_apply, Finset.sum_apply]

end AVRegularity.Weighted
end
