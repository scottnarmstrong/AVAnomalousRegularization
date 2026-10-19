-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PointwiseMolecularMaterialSampleBudget
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVRegularity.CoupledEnergyPlane.Variational.MassDriftEnergy
public import AVRegularity.Weighted.BoundedWeightRoot
public import AVRegularity.CycleJoint.CellDriftWindowMeasurable
public import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The genuine unit-diffusion homogeneous equation transfers to spatial and temporal cell coordinates. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_cell_solution (K : ι → ℕ) (D : ℕ) (a b e : ℝ)
    (he : e ≠ 0) (y : Vec 2) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * a) ((e⁻¹) ^ 2 * b)
      (fun t z => e • v (e ^ 2 * t) (y + e • z)) D K
      (fun i i' d t z => (e * (e ^ (d.1 - 1))⁻¹) • A i i' d (e ^ 2 * t) (y + e • z))
      (fun i => planeCarrierAffine e he y (f i)) (fun _ _ => 0) (fun _ _ => 0)
      (fun i t => planeCarrierAffine e he y (u i (e ^ 2 * t)))
      (fun i t => planeCarrierAffine e he y (w i (e ^ 2 * t))) := by
  have hzF (i : ι) : planeCarrierAffine e he y
      (0 : PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) = 0 :=
    (planeCarrierAffineLinearMap (K i) e he y).map_zero
  have hzg (i : ι) : planeCarrierAffine e he y (0 : PlaneHk Set.univ (K i) (h i)) = 0 :=
    (planeCarrierAffineLinearMap (K i) e he y).map_zero
  have hsp := planeWeakSolution_affine K D 1 a b e he y v A f
    (fun _ _ => 0) (fun _ _ => 0) u w hs
  simp only [one_mul, hzF, hzg, smul_zero] at hsp
  have hp : 0 < (e⁻¹) ^ 2 := sq_pos_of_ne_zero (inv_ne_zero he)
  have hn := planeHomogeneous_diffusion_time_solution K D hp
    (fun t z => e⁻¹ • v t (y + e • z))
    (fun i i' d t z => (e⁻¹ * (e ^ (d.1 - 1))⁻¹) • A i i' d t (y + e • z))
    (fun i => planeCarrierAffine e he y (f i))
    (fun i t => planeCarrierAffine e he y (u i t))
    (fun i t => planeCarrierAffine e he y (w i t)) hsp
  have hprice : e ^ 2 * e⁻¹ = e := by
    field_simp
  have hvcell : timeNormalizedVelocity ((e⁻¹) ^ 2) (fun t z => e⁻¹ • v t (y + e • z)) =
      fun t z => e • v (e ^ 2 * t) (y + e • z) := by
    funext t z
    change ((e⁻¹) ^ 2)⁻¹ • (e⁻¹ • v (((e⁻¹) ^ 2)⁻¹ * t) (y + e • z)) = _
    rw [inv_pow, inv_inv, smul_smul, hprice]
  rw [hvcell] at hn
  simpa only [inv_pow, inv_inv, smul_smul, ← mul_assoc, hprice] using hn

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! A genuine native viscous Hilbert curve satisfies the literal integrated weak identity with all required integrability clauses. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeWeakCurve_rawIdentity {a b : ℝ} (hab : a ≤ b)
    (ν : ℝ) (K : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hvc : ∀ r ∈ Icc a b, Continuous (v r)) (M : ℝ)
    (hvb : ∀ r ∈ Icc a b, ∀ x, ‖v r x‖ ≤ M)
    (u : ℝ → PlaneHk univ K E) (w : ℝ → PlaneHk univ (K + 1) E)
    (f : PlaneHk univ K E) (hinitial : u a = f)
    (F : ℝ → PlaneFluxL2 E) (Q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hQ : ∀ r ∈ Icc a b, ∀ k, F r k =ᵐ[volume] fun x => Q r x k)
    (h : PlaneWeakHilbertCurve a b (fun r => planeHkValueOperator K (u r))
      (fun r => truncatePlaneHk (by omega) (w r))
      (fun r => planeWeakDualRepresentative
        (planeIntervalTransport a b hab v hvc M hvb r)
        (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E))
        (truncatePlaneHk (by omega) (w r)) (F r)))
    (t : ℝ) (ht : t ∈ Icc a b) (φ : PlaneHk univ 1 E) :
    CoupledWeakIdentity volume ν a t v
      ((u t).toFunction.jet (valueIndex2 K)) (f.toFunction.jet (valueIndex2 K))
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r k => (w r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      Q (fun _ _ => 0) (fun _ _ => 0) := by
  let dual (r : ℝ) := planeWeakDualRepresentative
    (planeIntervalTransport a b hab v hvc M hvb r)
    (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E))
    (truncatePlaneHk (by omega) (w r)) (F r)
  let rhs (r : ℝ) (x : Vec 2) := planeWeakSpatialRhs ν v
    (φ.toFunction.jet (valueIndex2 1))
    (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r k => (w r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    Q (fun _ _ => 0) (fun _ _ => 0) r x
  have hp (r : ℝ) (hr : r ∈ Icc a b) :
      inner ℝ (dual r) φ = ∫ x, rhs r x := by
    have he := planeViscousDual_pair_eq_raw ν K
      (planeIntervalCoefficient a b hab v r)
      (planeIntervalVelocity_continuous a b hab v hvc r) (le_max_right M 0)
      (planeIntervalVelocity_bound a b hab v M hvb r) (w r) φ (F r) (Q r) (hQ r hr)
    simpa only [dual, planeIntervalTransport, rhs, planeWeakSpatialRhs,
      planeIntervalCoefficient_of_mem a b hab v r hr] using he
  have hi (r : ℝ) (hr : r ∈ Icc a b) : Integrable (rhs r) volume := by
    have he := planeViscous_rawSpatial_integrable ν K
      (planeIntervalCoefficient a b hab v r)
      (planeIntervalVelocity_continuous a b hab v hvc r) (le_max_right M 0)
      (planeIntervalVelocity_bound a b hab v M hvb r) (w r) φ (F r) (Q r) (hQ r hr)
    simpa only [rhs, planeWeakSpatialRhs,
      planeIntervalCoefficient_of_mem a b hab v r hr] using he
  have htime : IntegrableOn (fun r => inner ℝ (dual r) φ) (Ioc a t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp
      (planeWeakPair_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 dual h.dual_mem φ)
  have htime' : IntegrableOn (fun r => ∫ x, rhs r x) (Ioc a t) := by
    apply htime.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hp r ⟨hr.1.le, hr.2.trans ht.2⟩
  change Integrable _ volume ∧ Integrable _ volume ∧
    (∀ r ∈ Ioc a t, Integrable (rhs r) volume) ∧
    IntegrableOn (fun r => ∫ x, rhs r x) (Ioc a t) ∧ _
  refine ⟨planeHk_rawValuePairing_integrable (u t) φ,
    planeHk_rawValuePairing_integrable f φ,
    (fun r hr => hi r ⟨hr.1.le, hr.2.trans ht.2⟩), htime', ?_⟩
  have he := h.increment a ⟨le_rfl, hab⟩ t ht ht.1 φ
  rw [hinitial, planeHk_rawValuePairing, planeHk_rawValuePairing] at he
  refine he.trans ?_
  rw [intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hp r ⟨hr.1.le, hr.2.trans ht.2⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVenhance Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The molecular envelope bounds the actual dimensional diagonal sample before chart transport. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_flow_sample_uniform_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hn : K v ≤ Jchart + 1) (s τ : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)) :
    let Cflow := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ t : ℝ, (∀ Y : Vec 2, (τ, Y) ∈ dom p c) →
      t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
      |s - t| ≤ 2 * Cage * ocTauPP α q Λ m → ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => F.dimFlux ν e (ocEpsilon q Λ (m - 1))
        p c v u γ d I τ (streamFlow φ hφ s y t)
          (e⁻¹ • streamFlow φ hφ s y t)) x‖ ≤
        (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
          ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal)) := by
  dsimp only
  intro t hdom htime hage j hj x
  have hh := pointwise_molecular_flow_sample_raw_budget F π hπ K Kmax hK dom ν e ρ
    hν he hE hρE ha hρ C J b henv v u γ hγ d hd I p c hc hn s τ hs
    t hdom htime hage j hj x
  exact hh.trans (material_sample_constant_monotone (K v) Kmax (hK v) _ _
    (one_le_jetConst _ _) (by positivity))
end

/-! The molecular envelope bounds the actual dimensional diagonal sample before chart transport. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_material_sample_uniform_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hn : K v ≤ Jchart + 1) (s : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)) :
    let Cflow := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
      |s - t| ≤ 2 * Cage * ocTauPP α q Λ m → ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => F.dimFlux ν e (ocEpsilon q Λ (m - 1))
        p c v u γ d I t (streamFlow φ hφ s y t)
          (e⁻¹ • streamFlow φ hφ s y t)) x‖ ≤
        (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
          ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal)) := by
  dsimp only
  intro t hdom htime hage j hj x
  have hh := pointwise_molecular_material_sample_raw_budget F π hπ K Kmax hK dom ν e ρ
    hν he hE hρE ha hρ C J b henv v u γ hγ d hd I p c hc hn s hs
    t hdom htime hage j hj x
  exact hh.trans (material_sample_constant_monotone (K v) Kmax (hK v) _ _
    (one_le_jetConst _ _) (by positivity))
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The independent smooth envelope supplies continuous original and transported scalar rows at every active output time. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem active_piece_native_scalar_rows_continuous (F : ChartedFamily ι h D P Ctx)
    (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (p : (F.locally_finite t t).toFinset)
    (c : Ctx p) (v u : ι) (γ : F.Γ v u) (J : ℕ) :
    (∀ k (j : JetIndex2 J), Continuous (nativeSourceScalarJetCoefficient
      (F.identity v u γ).maxOrder
      (pieceDimensionalNativeJetArray F ν e E p c v u γ t) k j)) ∧
    (∀ k (j : JetIndex2 J), Continuous
      (pieceTransportedNativeScalarJetCoefficient F ν e E p c v u γ t J k j)) := by
  have hB (r : ℕ) (I : DerivativeWord2 r) : ContDiff ℝ (0 : ℕ)
      (pieceDimensionalNativeJetArray F ν e E p c v u γ t r I) :=
    (active_pieceDimensionalNativeJetArray_smooth F ν e E a b n hs t ht p c v u γ r I).of_le
      (by simp)
  constructor
  · intro k j
    exact (nativeSourceScalarJetCoefficient_smooth (F.identity v u γ).maxOrder 0
      (pieceDimensionalNativeJetArray F ν e E p c v u γ t) hB k j).continuous
  · intro k j
    exact (transportedNativeScalarJetCoefficient_smooth ((F.piece p).material t)
      ((F.piece p).material_smooth t) ((F.piece p).material_symm_smooth t)
      (F.identity v u γ).maxOrder 0
      (pieceDimensionalNativeJetArray F ν e E p c v u γ t) hB k j).continuous

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Time integrability of a literal coupling flux with the interval coefficient extension. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- A time-L² source gives a time-L² coupling flux without coefficient assumptions outside
its physical time interval. -/
theorem planeCoupledFluxTerm_memLp {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (w : ℝ → PlaneHk Set.univ (K i' + 1) (h i'))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeCoupledFluxTerm ρ hρ K D a b i i' d A hA
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hc _ (clampPoint a b hab t).property) (w t))
      2 (volume.restrict (Set.Icc a b)) := by
  let U := hw.toLp w
  let V := planeCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm U
  have hv := planeCoupledFluxTimeCLM_ae hab ρ hρ K D i i' d A hA hc hAm U
  apply MemLp.ae_eq (hf_Lp := MeasureTheory.Lp.memLp V)
  filter_upwards [hv, hw.coeFn_toLp] with t ht hw'
  exact ht.trans (congrArg (fun z => planeCoupledFluxTerm ρ hρ K D a b i i' d A hA
    (clampPoint a b hab t) (clampPoint a b hab t).property
    (hc _ (clampPoint a b hab t).property) z) hw')

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.ChartTransport AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Certified natural cell charts preserve polynomial remainder weights under the full native Piola transport. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_cell_transported_polynomial_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1))
    (s t : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |t - s| ≤ 2 * Cage * ocTauPP α q Λ m)
    (N Dγ n r : ℕ) (hN : N ≤ Jchart) (hn : n + Dγ ≤ N)
    (e ρ : ℝ) (he : 0 < e) (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1) / e)
    (yc : Vec 2)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (ϖ : ℝ) (p : ℕ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤ MB d I * polynomialMomentRoot ϖ y ^ p)
    (A : DerivativeWord2 r) (a : Fin 2) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let C := compConst Cflow N * Cflow
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y =>
      transportedCoeff (fun z => naturalPreparationJacobian hφ s t (yc + e • z)) Dγ
        (fun d I => B d I y) r A y a) x‖ ≤
      (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
          ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) *
            (ocEpsilon q Λ (m - 1) / e)⁻¹ ^ (d - 1 - r))) * polynomialMomentRoot ϖ x ^ p := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  have hCf : 1 ≤ Cflow := one_le_jetConst _ _
  have hK i j : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => naturalPreparationJacobian hφ s t (yc + e • z) i j) :=
    ((naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)).comp
        (contDiff_const.add (contDiff_id.const_smul e))
  apply transportedCoeff_polynomial_jet_bound _ hK N Dγ n r _ _ ρ
    (by dsimp [compConst]; positivity) (div_pos hE he) hρ hρE hn
    (fun a b j hj z => naturalPreparation_cell_jacobian_scaled_jet_bound hc ha hE s t hs ht hage
      N hN a b e (ocEpsilon q Λ (m - 1)) he hE.le le_rfl yc z j hj)
    B hB MB ϖ p hBj A a x

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The literal constituent flux is the finite weighted sum of its transported native scalar jet rows. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem constituentPhysical_flux_jet_row
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (a b t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (γ : F.Γ v u) (x : Vec 2) (k : Fin 2)
    (J : ℕ) (hJ : (F.identity v u γ).maxOrder ≤ J + 1)
    (g : ∀ r : ℕ, DerivativeWord2 r → h u) :
    (∑ d : admissibleOrders K D v u,
      constituentPhysical F ν e E actual v u γ d t x
        (WithLp.toLp 2 (g (d.1 - 1)))) k =
      ∑ p ∈ (F.locally_finite a b).toFinset, F.weight p t •
        (∑ j : JetIndex2 J,
          transportedNativeScalarJetCoefficient ((F.piece p).material t)
            (F.identity v u γ).maxOrder
            (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k j x •
              (F.identity v u γ).map (g j.1.val j.2)) := by
  classical
  rw [constituentPhysical_flux_window_sum F K hdesc ν e E actual a b t ht v u γ x
    (fun d => WithLp.toLp 2 (g (d - 1)))]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp_rw [pieceDimensionalNativeJetArray_transported]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    transportedArrayAssembly_jet_row ((F.piece p).material t)
    (F.identity v u γ).maxOrder hJ
    (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t)
    (F.identity v u γ).map g x k

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The finite Sobolev coupling row for a plane solution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

/-- The literal finite coupling sum, extended in time by clamping only its coefficients. -/
def planeCouplingFluxRow (i : ι) (t : ℝ) :
    PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ i', ∑ d : admissibleOrders K D i i',
    planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hc i i' d _ (clampPoint a b hab t).property) (w i' t)

/-- The finite coupling row has the Sobolev time integrability of the source lifts. -/
theorem planeCouplingFluxRow_memLp
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (planeCouplingFluxRow hab ρ hρ K D A hA hc w i)
      2 (volume.restrict (Set.Icc a b)) := by
  let term (i' : ι) (d : admissibleOrders K D i i') (t : ℝ) :=
    planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hc i i' d _ (clampPoint a b hab t).property) (w i' t)
  have hterm (i' : ι) (d : admissibleOrders K D i i') :
      MemLp (term i' d) 2 (volume.restrict (Set.Icc a b)) :=
    planeCoupledFluxTerm_memLp hab ρ hρ K D i i' d (A i i' d)
      (hA i i' d) (hc i i' d) (hAm i i' d) (w i') (hw i')
  change MemLp (fun t => ∑ i', ∑ d : admissibleOrders K D i i', term i' d t)
    2 (volume.restrict (Set.Icc a b))
  clear_value term
  have hrow (i' : ι) : MemLp (fun t => ∑ d : admissibleOrders K D i i', term i' d t)
      2 (volume.restrict (Set.Icc a b)) := by
    exact memLp_fintype_sum (J := admissibleOrders K D i i') (α := ℝ)
      (E := PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (p := 2) (μ := volume.restrict (Set.Icc a b)) (term i') (hterm i')
  exact memLp_fintype_sum (fun i' t => ∑ d : admissibleOrders K D i i', term i' d t) hrow

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! A material chart pulls genuine native plane H1 carriers back with their exact gradient. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeH1ChartPull {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (u : PlaneHk univ 1 E) : PlaneHk univ 1 E :=
  planeH1OfWeakGradient
    (fun y => planeHkValueOperator 1 u (AVRegularity.streamFlow φ hφ t y s))
    (hilbertChartGradient hφ t s (fun i => (planeH1GradientOperator u i : Vec 2 → E)))
    (((Lp.memLp (planeHkValueOperator 1 u)).comp_measurePreserving
      (streamFlow_measurePreserving hφ t s)).mono_measure Measure.restrict_le_self)
    (fun i => (hilbertChartGradient_memLp hφ t s _
      (fun j => Lp.memLp (planeH1GradientOperator u j)) i).mono_measure Measure.restrict_le_self)
    (hilbertChartGradient_weak hφ t s _ _ (Lp.memLp (planeHkValueOperator 1 u))
      (fun i => Lp.memLp (planeH1GradientOperator u i))
      (fun i e => planeH1_value_gradient_weakPartial u i e))

theorem planeH1ChartPull_value_ae {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (u : PlaneHk univ 1 E) :
    (planeHkValueOperator 1 (planeH1ChartPull hφ t s u) : Vec 2 → E) =ᵐ[volume]
      fun y => planeHkValueOperator 1 u (AVRegularity.streamFlow φ hφ t y s) := by
  rw [planeHkValueOperator_apply]
  apply (univToPlane_ae _).trans
  have hp := planeH1OfWeakGradient_value_ae
    (fun y => planeHkValueOperator 1 u (AVRegularity.streamFlow φ hφ t y s))
    (hilbertChartGradient hφ t s (fun i => (planeH1GradientOperator u i : Vec 2 → E)))
    (((Lp.memLp (planeHkValueOperator 1 u)).comp_measurePreserving
      (streamFlow_measurePreserving hφ t s)).mono_measure Measure.restrict_le_self)
    (fun i => (hilbertChartGradient_memLp hφ t s _
      (fun j => Lp.memLp (planeH1GradientOperator u j)) i).mono_measure Measure.restrict_le_self)
    (hilbertChartGradient_weak hφ t s _ _ (Lp.memLp (planeHkValueOperator 1 u))
      (fun i => Lp.memLp (planeH1GradientOperator u i))
      (fun i e => planeH1_value_gradient_weakPartial u i e))
  change ((planeH1ChartPull hφ t s u).val (valueIndex2 1) : Vec 2 → E)
    =ᵐ[volume.restrict univ]
      (fun y => planeHkValueOperator 1 u (AVRegularity.streamFlow φ hφ t y s)) at hp
  simpa only [Measure.restrict_univ] using hp

theorem planeH1ChartPull_gradient_ae {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (u : PlaneHk univ 1 E) (j : Fin 2) :
    (planeH1GradientOperator (planeH1ChartPull hφ t s u) j : Vec 2 → E) =ᵐ[volume]
      hilbertChartGradient hφ t s (fun i => (planeH1GradientOperator u i : Vec 2 → E)) j := by
  rw [planeH1GradientOperator_apply]
  apply (univToPlane_ae _).trans
  have hp := planeH1OfWeakGradient_gradient_ae
    (fun y => planeHkValueOperator 1 u (AVRegularity.streamFlow φ hφ t y s))
    (hilbertChartGradient hφ t s (fun i => (planeH1GradientOperator u i : Vec 2 → E)))
    (((Lp.memLp (planeHkValueOperator 1 u)).comp_measurePreserving
      (streamFlow_measurePreserving hφ t s)).mono_measure Measure.restrict_le_self)
    (fun i => (hilbertChartGradient_memLp hφ t s _
      (fun k => Lp.memLp (planeH1GradientOperator u k)) i).mono_measure Measure.restrict_le_self)
    (hilbertChartGradient_weak hφ t s _ _ (Lp.memLp (planeHkValueOperator 1 u))
      (fun i => Lp.memLp (planeH1GradientOperator u i))
      (fun i e => planeH1_value_gradient_weakPartial u i e)) (fun _ => j)
  change ((planeH1ChartPull hφ t s u).val ⟨⟨1, by omega⟩, fun _ => j⟩ : Vec 2 → E)
    =ᵐ[volume.restrict univ]
      hilbertChartGradient hφ t s (fun i => (planeH1GradientOperator u i : Vec 2 → E)) j at hp
  simpa only [Measure.restrict_univ] using hp
end

/-! Native chart pullback is linear and preserves exactly the L2 value norm. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_eq_of_value {u z : PlaneHk univ 1 E}
    (h : planeHkValueOperator 1 u = planeHkValueOperator 1 z) : u = z := by
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  exact h

omit [FiniteDimensional ℝ E] in
 theorem planeH1ChartPull_value_eq {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (u : PlaneHk univ 1 E) :
    planeHkValueOperator 1 (planeH1ChartPull hφ t s u) =
      Lp.compMeasurePreservingₗᵢ ℝ (fun y => AVRegularity.streamFlow φ hφ t y s)
        (streamFlow_measurePreserving hφ t s) (planeHkValueOperator 1 u) := by
  apply Lp.ext
  exact (planeH1ChartPull_value_ae hφ t s u).trans
    (Lp.coeFn_compMeasurePreserving _ _).symm
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.ChartTransport AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Certified Piola transport constructs actual native maps for polynomial remainder arrays. -/

variable  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparationTransportedPolynomial_coefficient_jet_budget
    (K r : ℕ)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1))
    (s t : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |t - s| ≤ 2 * Cage * ocTauPP α q Λ m)
    (N Dγ : ℕ) (hN : N ≤ Jchart) (hKN : K + Dγ ≤ N)
    (e ρ ϖ : ℝ) (he : 0 < e) (hρ : 0 < ρ)
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1) / e) (yc : Vec 2)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2)
    (hBs : ∀ d I i τ, ContDiff ℝ (K : ℕ) (fun z => B d I τ z i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hMB : ∀ d I, 0 ≤ MB d I) (p : ℕ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i τ j, j ≤ K → ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I τ x i) z‖ ≤ MB d I * polynomialMomentRoot ϖ z ^ p)
    (τ : ℝ) (j : ℕ) (hj : j ≤ K) (A : DerivativeWord2 r) (a : Fin 2) (z : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let C := compConst Cflow N * Cflow
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun y =>
      transportedCoeff (fun x => naturalPreparationJacobian hφ s t (yc + e • x))
        Dγ (fun d I => B d I τ y) r A y a) z‖ ≤
      transportedPolynomialJetPrice N Dγ r K C (ocEpsilon q Λ (m - 1) / e) MB *
        polynomialMomentRoot ϖ z ^ p := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let C := compConst Cflow N * Cflow
  let R := ocEpsilon q Λ (m - 1) / e
  have hCf : 1 ≤ Cflow := one_le_jetConst _ _
  have hC : 0 ≤ C := mul_nonneg (compConst_nonneg hCf N) (zero_le_one.trans hCf)
  have hR : 0 < R := div_pos hE he
  have hh := preparation_cell_transported_polynomial_jet_bound hc ha hE s t hs ht hage
    N Dγ j r hN (by omega) e ρ he hρ.le hρE yc (fun d I z => B d I τ z)
    (fun d I i => (hBs d I i τ).of_le (by exact_mod_cast hj)) MB ϖ p
    (fun d hd I i l hl y => hBj d hd I i τ l (hl.trans hj) y) A a z
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (transportedPolynomialJetPrice_mono N Dγ r hj C R hC hR.le MB hMB)
    (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) p)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A bound on the support of an actual L2 readout controls its chart energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem chartScalarEnergy_supported_bound (q : Vec 2 → ℝ)
    (U : Lp E 2 (volume : Measure (Vec 2))) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂volume, U x ≠ 0 → q x ≤ C) :
    chartScalarEnergy q U ≤ ENNReal.ofReal C * ENNReal.ofReal (‖U‖ ^ 2) := by
  have he : (∫ x, ‖U x‖ ^ 2 ∂volume) = ‖U‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => (real_inner_self_eq_norm_sq (U x)).symm)
  have ht : chartScalarEnergy q U ≤
      ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (‖U x‖ ^ 2) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [hb] with x hx
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : U x = 0
    · simp only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hx hz) (sq_nonneg _)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (Lp.memLp U).norm.integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)), he] at ht
  exact ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Scalar-weighted Hilbert tensor energy is the sum of its component energies. -/

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- An actual tensor L² readout has the sum of its scalar-weighted component energies. -/
theorem chartScalarEnergy_tensor_readout (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : J → Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PiLp 2 (fun _ : J => E)) 2 (volume : Measure (Vec 2)))
    (hQ : Q =ᵐ[volume] fun x => WithLp.toLp 2 (fun j => U j x)) :
    chartScalarEnergy (fun x => q x ^ 2) Q =
      ∑ j : J, chartScalarEnergy (fun x => q x ^ 2) (U j) := by
  unfold chartScalarEnergy
  calc
    _ = ∫⁻ x, ∑ j : J, ENNReal.ofReal (q x ^ 2 * ‖U j x‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [hQ] with x hx
      rw [hx, PiLp.norm_sq_eq_of_L2, Finset.mul_sum,
        ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ = _ := by
      rw [lintegral_finsetSum']
      intro j _
      exact ((hq.measurable.pow_const 2).aemeasurable.mul
        ((Lp.aestronglyMeasurable (U j)).norm.aemeasurable.pow_const 2)).ennreal_ofReal

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Physical polynomial moment weights have the exact cell centre and inverse patch-radius scaling. -/

theorem planeMomentPolynomial_affine (n : ℕ) (ϖ e : ℝ) (he : e ≠ 0)
    (y zc z : Vec 2) :
    planeMomentPolynomial n (ϖ * e) (e⁻¹ • (zc - y)) z =
      planeMomentPolynomial n ϖ zc (y + e • z) := by
  have hc (k : Fin 2) : e * (z k - (e⁻¹ • (zc - y)) k) = (y + e • z) k - zc k := by
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  unfold planeMomentPolynomial
  congr 2
  calc
    (ϖ * e) ^ 2 * ((z 0 - (e⁻¹ • (zc - y)) 0) ^ 2 + (z 1 - (e⁻¹ • (zc - y)) 1) ^ 2) =
        ϖ ^ 2 * ((e * (z 0 - (e⁻¹ • (zc - y)) 0)) ^ 2 +
          (e * (z 1 - (e⁻¹ • (zc - y)) 1)) ^ 2) := by ring
    _ = ϖ ^ 2 * (((y + e • z) 0 - zc 0) ^ 2 + ((y + e • z) 1 - zc 1) ^ 2) := by
      rw [hc, hc]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Finite coordinate bounds control the true plane polynomial moment. -/

theorem planeMomentPolynomial_le_coordinate_bound (n : ℕ) (ϖ R : ℝ) (hR : 0 ≤ R)
    (z x : Vec 2) (h : ∀ i, |ϖ * (x i - z i)| ≤ R) :
    planeMomentPolynomial n ϖ z x ≤ (1 + 2 * R ^ 2) ^ n := by
  have h0 : (ϖ * (x 0 - z 0)) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (h 0)
  have h1 : (ϖ * (x 1 - z 1)) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (h 1)
  unfold planeMomentPolynomial
  apply pow_le_pow_left₀ (by positivity) _ n
  nlinarith only [h0, h1]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Compact smooth Hilbert tests are finite sums of compact scalar-direction tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem compactSmoothHilbertH1_basis_decomposition (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    let b := stdOrthonormalBasis ℝ E
    let q := fun k x => inner ℝ (b k) (f x)
    let hq := fun k => (innerSL ℝ (b k)).contDiff.comp hf
    let hsq := fun k => hs.comp_left (inner_zero_right (b k))
    compactSmoothHilbertH1 f hf hs =
      ∑ k : Fin (Module.finrank ℝ E), compactSmoothHilbertH1 (fun x => q k x • b k)
        ((hq k).smul contDiff_const) ((hsq k).smul_right) := by
  let b := stdOrthonormalBasis ℝ E
  let q := fun k x => inner ℝ (b k) (f x)
  have hq k : ContDiff ℝ (⊤ : ℕ∞) (q k) := (innerSL ℝ (b k)).contDiff.comp hf
  have hsq k : HasCompactSupport (q k) := hs.comp_left (inner_zero_right (b k))
  let Z := fun k => compactSmoothHilbertH1 (fun x => q k x • b k)
    ((hq k).smul contDiff_const) ((hsq k).smul_right)
  change compactSmoothHilbertH1 f hf hs = ∑ k, Z k
  apply planeH1_eq_of_value
  rw [map_sum]
  apply Lp.ext
  have hz : ∀ᵐ x ∂volume, ∀ k, planeHkValueOperator 1 (Z k) x = q k x • b k :=
    ae_all_iff.mpr fun k => compactSmoothHilbertH1_value_ae _ _ _
  filter_upwards [compactSmoothHilbertH1_value_ae f hf hs,
    Lp.coeFn_finsetSum Finset.univ (fun k => planeHkValueOperator 1 (Z k)), hz]
    with x hx hsum hzx
  rw [hx, hsum]
  rw [Finset.sum_apply]
  simp_rw [hzx]
  exact (b.sum_repr' (f x)).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Continuous periodic native scalar coefficients define actual bounded Sobolev row operators. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def periodicScalarRowOperator {K : ℕ} (c : JetIndex2 K → Vec 2 → ℝ)
    (hc : ∀ j, Continuous (c j)) (hp : ∀ j, AVenhance.IsZ2Periodic (c j)) :
    PlaneHk Set.univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  let hb := periodicScalarRow_exists_budget c hc hp
  planeScalarJetRow c hc hb.choose hb.choose_spec.1 hb.choose_spec.2

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The native material trace and H1 test have exactly the physical L2 pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeChart_value_pairing {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (u : Lp E 2 (volume : Measure (Vec 2))) (z : PlaneHk univ 1 E) :
    inner ℝ (planeL2FlowPull hφ t s u)
      (planeHkValueOperator 1 (planeH1ChartPull hφ t s z)) =
      inner ℝ u (planeHkValueOperator 1 z) := by
  rw [planeH1ChartPull_value_eq]
  exact (planeL2FlowPull hφ t s).inner_map_map u (planeHkValueOperator 1 z)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual periodic row operator reads ordinary derivatives on every smooth representative of its native carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem periodicScalarRowOperator_smooth_ae {K : ℕ} (c : JetIndex2 K → Vec 2 → ℝ)
    (hc : ∀ j, Continuous (c j)) (hp : ∀ j, IsZ2Periodic (c j))
    (U : PlaneHk Set.univ K E) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f) :
    (periodicScalarRowOperator c hc hp U : Vec 2 → E) =ᵐ[volume]
      fun x => ∑ j : JetIndex2 K, c j x • orderedDerivative j.2 f x := by
  exact planeScalarJetRow_smooth_ae c hc _ _ _ U f hf hu

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Bochner L2 fluxes have joint L2 components preserving every spatial class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [CompleteSpace E]

theorem planeFlux_exists_joint_fields {a b : ℝ} (F : ℝ → PlaneFluxL2 E)
    (hF : MemLp F 2 (volume.restrict (Icc a b))) :
    ∃ Q : Fin 2 → ℝ × Vec 2 → E,
      (∀ i, MemLp (Q i) 2 ((volume.restrict (Icc a b)).prod volume)) ∧
      ∀ t i, (F t i : Vec 2 → E) =ᵐ[volume] fun x => Q i (t, x) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) :=
    Lp.SecondCountableTopology
  have hex i := exists_bochner_joint_trace_realization
    (volume.restrict (Icc a b)) volume (fun t => F t i)
      (ContinuousLinearMap.comp_memLp'
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) i) hF)
  choose Q hQ heQ using hex
  exact ⟨Q, hQ, fun t i => heQ i t⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Window-local coefficient bounds pay the absolute time price of every image pairing. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem windowed_coefficient_pairing_time_integrable_summable (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (hS : MeasurableSet S) (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t ∈ S, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t ∈ S, ∀ x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    (∀ n : Fin 2 → ℤ, Integrable (fun t => ∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)) μ) ∧
    Summable (fun n : Fin 2 → ℤ => ∫ t, ‖∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)‖ ∂μ) := by
  let Cw := windowedPhysicalCoefficient S C
  have hcW : ∀ t, Continuous (Cw t) := windowedPhysicalCoefficient_continuous S C hc
  have hjW : Measurable (Function.uncurry Cw) :=
    windowedPhysicalCoefficient_joint_measurable S hS C hj
  have hbW : ∀ t x, ‖Cw t x‖ ≤ MC := windowedPhysicalCoefficient_norm_le S C MC hMC hC
  have he (n : Fin 2 → ℤ) : (fun t => ∫ x, inner ℝ
      (Cw t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)) =ᵐ[μ]
      (fun t => ∫ x, inner ℝ
        (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
        (φ.toFunction.jet β x)) := by
    filter_upwards [hSae] with t ht
    rw [show Cw t = C t from windowedPhysicalCoefficient_eq S C t ht]
  constructor
  · intro n
    exact (translated_coefficient_pairing_time_integrable μ Cw hcW hjW MC hMC hbW
      f hf (AVenhance.latticeShift n) α φ β).congr (he n)
  · have hs := translated_coefficient_pairing_time_summable μ U R hR hU Cw hcW hjW
      MC hMC hbW f hf z α φ β hφ M hM hw hb
    exact hs.congr (fun n => integral_congr_ae ((he n).mono (fun _ hx => congrArg norm hx)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual material drift has its continuous bounded velocity in positive diffusion time. -/

variable {φ : ℝ → Vec 2 → ℝ}

def normalizedMaterialVelocity (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  timeNormalizedVelocity ν (chartVector hφ s (fun t x => v t x - streamVel φ t x))

theorem normalizedMaterialVelocity_continuous (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2)) (t : ℝ) :
    Continuous (normalizedMaterialVelocity hφ s ν v t) :=
  (materialChartDrift_continuous_slice hφ s v hv (ν⁻¹ * t)).const_smul ν⁻¹

def normalizedMaterialVelocityBudget (hφ : IsAdmissibleStream φ) (s ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) : ℝ :=
  ν⁻¹ * (materialChartDrift_bound hφ s a b v hv hp).choose

theorem normalizedMaterialVelocity_norm_le (hφ : IsAdmissibleStream φ) (s : ℝ)
    {ν : ℝ} (hν : 0 < ν) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b)) (x : Vec 2) :
    ‖normalizedMaterialVelocity hφ s ν v t x‖ ≤ normalizedMaterialVelocityBudget hφ s ν a b v hv hp :=
  timeNormalizedVelocity_norm_le hν _ t
    ((materialChartDrift_bound hφ s a b v hv hp).choose_spec.2 _
      (positiveTimeNormalization_mem_Icc hν ht)) x

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Joint measurability of the literal edge coefficients used by the plane equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem edgeCoefficient_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (v u : ι) (d : admissibleOrders K D v u) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      edgeCoefficient F ν e E actual K v u d z.1 z.2) :=
  physicalCoefficient_joint_measurable F hc ν e E n hs hmeas hwmeas actual v u d.1

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Native higher traces and exact actual L2 flux readouts assemble their genuine rowwise Hilbert curves into the homogeneous coupled plane solution class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCoupledSolution_of_rawFlux_hilbertCurves {a b : ℝ} (hab : a ≤ b)
    (ν : ℝ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hu : ∀ i, ContinuousOn (u i) (Icc a b))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Icc a b)))
    (hwu : ∀ i, ∀ᵐ t ∂volume.restrict (Icc a b),
      truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t)
    (hf : ∀ i, u i a = f i)
    (Flux : ∀ i, ℝ → PlaneFluxL2 (h i))
    (hFlux : ∀ i t, t ∈ Icc a b → ∀ k, (Flux i t k : Vec 2 → h i) =ᵐ[volume]
      fun x => planeRawCouplingFlux K D t A (fun j => w j t) i x k)
    (hcurve : ∀ i, PlaneWeakHilbertCurve a b (fun t => planeHkValueOperator (K i) (u i t))
      (fun t => truncatePlaneHk (by omega) (w i t))
      (fun t => planeWeakDualRepresentative
        (planeIntervalTransport a b hab v hvc M hvb t)
        (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
        (truncatePlaneHk (by omega) (w i t))
        (Flux i t))) :
    IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w := by
  refine ⟨hu, hw, hwu, hf, ?_⟩
  intro i t ht φ
  have he := planeWeakCurve_rawIdentity hab ν (K i) v hvc M hvb (u i) (w i) (f i) (hf i)
    (Flux i) (fun r => planeRawCouplingFlux K D r A (fun j => w j r) i)
    (hFlux i) (hcurve i) t ht φ
  simp only [Measure.restrict_univ]
  exact coupledWeakIdentity_zeroCarrier_forcing (K i) ν a t v _ _ _ _ _ _ he

end AVRegularity.CycleJointProofs
end
end
