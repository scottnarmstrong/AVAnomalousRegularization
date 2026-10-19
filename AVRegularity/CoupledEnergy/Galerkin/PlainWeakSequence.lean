-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
public import AVRegularity.CoupledEnergy.Variational.TorusSpatialFluxTimeLp
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Construct the genuine time L² total flux and time L¹ total value source
representing every native Fourier RHS row of the common weak graph limit. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainPhysicalForcing_exists (K : ι → ℕ) (D : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ν ρ : ℝ) (hρ : 0 < ρ) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (α B lam : ℝ)
    (hj : ∀ t ∈ Set.Icc a b, ∀ i l, 1 ≤ l → l ≤ K i → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j) :
    ∃ S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)),
    ∃ H : ∀ i, ℝ → TorusHk (K i) (h i),
      (∀ i, MemLp (S i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ i, Integrable (H i) (volume.restrict (Set.Icc a b))) ∧
      (∀ N, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ z : CoupledFourierModeIndex (h := h) N,
        coupledTimeRhs K D ν t v A F g (U t) z.1 (coupledModeHk N z z.1 1) =
          plainSourceCoefficients N K (fun i => S i t) (fun i => H i t) z) := by
  obtain ⟨T, hTLp, hTval⟩ := plainTransport_exists_memLp K hab ρ hρ v hv hc hp V hV hb
    α B lam hj U hU
  obtain ⟨C, hCLp, hCval⟩ := torusCoupledFlux_family_exists_memLp K D hab ρ hρ A hA hAm hAc hAp U hU
  let G : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun i t => torusGradientTensor (coupledHighGraphReadout K i (U t))
  have hGLp (i : ι) := torusGradientTensor_memLp K hab ρ hρ U hU i
  have hGval := torusGradientTensor_family_value_ae K a b U hU
  let S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun i t => ν • G i t + (∑ i', ∑ d, C i i' d t) + F i t
  let H : ∀ i, ℝ → TorusHk (K i) (h i) := fun i t => g i t - T i t
  refine ⟨S, H, ?_, ?_, ?_⟩
  · exact torusCoupledTotalFlux_memLp K D a b ν G F C hGLp hF hCLp
  · intro i
    exact (hg i).sub ((hTLp i).integrable (by norm_num))
  · intro N
    filter_upwards [hTval, hGval, hCval, ae_restrict_mem measurableSet_Icc] with t ht hg' hc' htI
    intro z
    exact plainTimeRhs_eq_sourceCoefficient N K D ν t v (hc t htI).continuous V hV (hb t htI)
      A F g (U t) (fun i => T i t) (fun i => G i t) (fun i i' d => C i i' d t) ht hg' hc' z

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual integrated finite spatial equation against the Fourier cutoff
of an arbitrary periodic H¹ test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainFourier_projected_component_equation (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hv_bdd : ∃ V : ℝ, ∀ s ∈ Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (hv_meas : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hv : ∀ s ∈ Icc a b, Continuous (v s))
    (hA : ∀ s ∈ Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (f : ∀ i, TorusHk (K i) (h i)) (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b)))
    (y : C(Icc a b, CoupledPlainCoefficients (h := h) N))
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N K f) a b (extendCurve hab y))
    (i : ι) (φ : TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Icc a b) :
    inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (extendCurve hab y t)))
      (torusHkValueCLM (galerkinProj N φ)) -
      inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N φ)) =
      coupledIntegratedRhs K D ν a t v A F g (plainHigherBochner N K a b hab y) i
        (galerkinProj N φ) := by
  refine finiteComponent_identity
    (fun j ψ => inner ℝ (torusHkValueCLM (coupledPlainSynthesis N j (K j) (extendCurve hab y t)))
      (torusHkValueCLM (galerkinProj N ψ)) -
      inner ℝ (torusHkValueCLM (f j)) (torusHkValueCLM (galerkinProj N ψ)))
    (fun j ψ => coupledIntegratedRhs K D ν a t v A F g (plainHigherBochner N K a b hab y) j
      (galerkinProj N ψ)) ?_ ?_ ?_ i φ
  · intro j
    simp only [map_zero, inner_zero_right, sub_self]
  · intro j
    rw [map_zero]
    exact coupledIntegratedRhs_zero K D ν a t v A F g _ j
  · intro ψ
    simpa only [Finset.sum_sub_distrib] using
      plainFourier_projected_integrated_equation N D ν ρ hρ K hab v A hv_bdd hv_meas
        hA_meas hA_bdd hv hA F g f hF hg y hy ψ t ht

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Constructed finite Fourier solutions with uniform energy and exact initial data. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (hC : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk (K i) (h i))

include hρ hA hv hvp hC hp in
/-- M2 and M3 combined: actual coefficient solutions with the paper energy constants. -/
theorem plainCoupledFourierODE_exists_energy (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (hab : a ≤ b)
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
        (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N K f) a b (AVenhance.Infra.ODE.extendCurve hab y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b ∧
      ∀ t ∈ Set.Icc a b,
        massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (AVenhance.Infra.ODE.extendCurve hab y t)).val) +
          (ν / 2) * (∫ s in Set.Icc a b,
            massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (AVenhance.Infra.ODE.extendCurve hab y s)).val)) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2 := by
  obtain ⟨y, ⟨hy, hyac⟩, _⟩ := plainCoupledFourierODE_existsUnique N D ν ρ hρ K a b hab v
    hv_bdd hv_meas A hA_meas hA f F g hF hg
  obtain ⟨C, hC0, hbound⟩ := plainIntervalMatrix_bounded N D ν ρ hρ K a b hab v hv_bdd A hA
  have hm : ∀ r c, AEStronglyMeasurable
      (fun t => plainIntervalMatrix N D ν K a b hab v A t r c) volume := fun r c => (plainIntervalMatrix_stronglyMeasurable N D ν K a b hab v hv_meas A hA_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (plainSourceCoefficients_integrable N K a b F g hF hg)
  have hint := plainMatrixODE_rhs_intervalIntegrable hab (plainIntervalMatrix N D ν K a b hab v A)
    _ (plainInitialCoefficients N K f) C hC0 hm hbound hf y
  have hy' := plainIntervalSolution_unclamp N D ν K a b hab v A _ _ _ hy
  have hint' := plainIntervalRhs_intervalIntegrable N D ν K a b hab v A _ _ hint
  have henergy := plainODE_uniform_mass_energy N D ν ρ hρ K a b v A hA hv hvp hC hp F g
    hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab
    (AVenhance.Infra.ODE.extendCurve hab y) (plainInitialCoefficients N K f) hy'
    (AVenhance.Infra.ODE.continuous_extendCurve hab y) hF hg hint'
  have hinit : AVenhance.Infra.ODE.extendCurve hab y a = plainInitialCoefficients N K f := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, hab⟩
  rw [hinit] at henergy
  refine ⟨y, hy', hyac, ?_⟩
  intro t ht
  have hproj := plainInitialCoefficients_mass_le N K ρ π hπ f
  linarith [henergy t ht]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify the genuine lower-order weak trace of the same finite sequence
by the integrated equation of its common spacetime weak limit. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The actual finite solutions identify every closed-time weak trace against all H¹ tests. -/
theorem plainClosedTrace_component_identity (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (K i) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (plainFourierMatrix (N n) D ν K v A r))
      (fun r => plainSourceCoefficients (N n) K (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) K f) a b (AVenhance.Infra.ODE.extendCurve hab (y n)))
    (U : CoupledHighTime (h := h) K a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) K a b hab (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) K a b hab (y n))) atTop (𝓝 (ell U)))
    (V : CoupledLowHilbert (h := h) K) (R : ℝ)
    (hlow : ∀ n, ‖plainLowerSynthesisCLM (N n) K (AVenhance.Infra.ODE.extendCurve hab (y n) t)‖ ≤ R)
    (htrace : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainLowerSynthesisCLM (N n) K (AVenhance.Infra.ODE.extendCurve hab (y n) t)))
        atTop (𝓝 (ell V))) (i : ι) (φ : TorusHk 1 (h i)) :
    inner ℝ (coupledLowValueCLM (h := h) K i V) (torusHkValueCLM φ) -
      inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
      coupledIntegratedRhs K D ν a t v A F g U i φ := by
  refine finiteComponent_identity
    (fun j ψ => inner ℝ (coupledLowValueCLM (h := h) K j V) (torusHkValueCLM ψ) -
      inner ℝ (torusHkValueCLM (f j)) (torusHkValueCLM ψ))
    (fun j ψ => coupledIntegratedRhs K D ν a t v A F g U j ψ) ?_ ?_ ?_ i φ
  · intro j
    simp only [map_zero, inner_zero_right, sub_self]
  · intro j
    exact coupledIntegratedRhs_zero K D ν a t v A F g U j
  · intro ψ
    simpa only [Finset.sum_sub_distrib] using
      plainClosedTrace_integrated_identity D ν ρ hρ K hab ht v hv_bdd hv_meas hv A hA_bdd
        hA_meas hA F g hF hg f N hN y hy U Q hu hw V R hlow htrace ψ
end

/-! Identify the genuine lower-order weak trace of the same finite sequence
by the integrated equation of its common spacetime weak limit. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainFiniteTrace_value_pairing_tendsto (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (K i) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (plainFourierMatrix (N n) D ν K v A r))
      (fun r => plainSourceCoefficients (N n) K (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) K f) a b (AVenhance.Infra.ODE.extendCurve hab (y n)))
    (U : CoupledHighTime (h := h) K a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) K a b hab (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) K a b hab (y n))) atTop (𝓝 (ell U)))
    (i : ι) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => inner ℝ
      (torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y n) t))) (torusHkValueCLM φ)) atTop
      (𝓝 (inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) +
        coupledIntegratedRhs K D ν a t v A F g U i φ)) := by
  have hinitial : Tendsto (fun n => inner ℝ (torusHkValueCLM (f i))
      (torusHkValueCLM (galerkinProj (N n) φ))) atTop
      (𝓝 (inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ))) :=
    ((innerSL ℝ (torusHkValueCLM (f i))).continuous.continuousAt.tendsto).comp
      ((torusHkValueCLM (E := h i) (K := 1)).continuous.continuousAt.tendsto.comp
        ((galerkinProj_tendsto φ).comp hN.tendsto_atTop))
  obtain ⟨B, hB⟩ := hv_bdd
  have hrhs := coupledIntegratedRhs_projected_weak_limit K D ν ρ hρ hab ht v hv_meas hv B hB
    A hA_bdd hA_meas hA F g hF hg
      (fun n => plainHigherBochner (N n) K a b hab (y n)) U Q hu hw N hN i φ
  apply (hinitial.add hrhs).congr'
  filter_upwards [] with n
  have heq := plainFourier_projected_component_equation (N n) D ν ρ hρ K hab v A
    ⟨B, hB⟩ hv_meas hA_meas hA_bdd hv hA F g f hF hg (y n) (hy n) i φ t ht
  rw [galerkinProj_fixed_value_pairing (K i) 1 (N n) _ φ
    (plainSynthesis_galerkin_fixed (N n) K _ i)] at heq
  exact (add_comm _ _).trans (eq_add_of_sub_eq heq).symm
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Uniform higher-order spacetime bounds derived from the actual finite energy estimate. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (hC : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk (K i) (h i))

include hρ hA hv hvp hC hp in
/-- Actual finite solutions have a uniform higher-order Bochner norm bound. -/
theorem plainODE_uniform_highTime_integral (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (hab : a ≤ b) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) y) volume a b) :
    (∫ t in Set.Icc a b, ‖plainHigherSynthesisCLM N K (y t)‖ ^ 2) ≤
      ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
        (2 * massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y a)).val) +
          (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) := by
  let P := ∑ i, π i
  let Q := ∑ i, π i / factorialWeightMin ρ (K i)
  let C := 2 * massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y a)).val) +
    (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
    10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => (hπ i).le)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ).le)
  have henergy := plainODE_uniform_mass_energy N D ν ρ hρ K a b v A hA hv hvp hC hp F g
    hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab y initial hy hycont hF hg hint
  have hn : 0 ≤ ∫ s in Set.Icc a b,
      massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (y s)).val) :=
    MeasureTheory.integral_nonneg (fun s => massGradNormSq_nonneg ρ π hπ _)
  have hEbound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y t)).val) ≤ C := by
    have hc := henergy t ht
    change _ ≤ C at hc
    nlinarith
  have hRbound : (ν / 2) * (∫ s in Set.Icc a b,
      massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (y s)).val)) ≤ C := by
    have hc := henergy a ⟨le_rfl, hab⟩
    change _ ≤ C at hc
    linarith [massNormSq_nonneg ρ π hπ (fun i => (coupledPlainSynthesis N i (K i) (y a)).val)]
  have hr := (plainSynthesis_massGrad_continuous N K ρ π hycont).intervalIntegrable (μ := volume) a b
  have hh := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (plainHigherSynthesis_memLp N K a b hycont).norm.integrable_sq
  have hconst : IntervalIntegrable (fun _ : ℝ => P * C) volume a b := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hab hh (hconst.add (hr.const_mul Q)) (fun t ht => by
    have hc := plainHigherSynthesis_normSq_le N K ρ hρ π hπ (y t)
    change _ ≤ P * massNormSq ρ π (fun j => (coupledPlainSynthesis N j (K j) (y t)).val) +
      Q * massGradNormSq ρ π (fun j => (coupledPlainSynthesis N j (K j + 1) (y t)).val) at hc
    exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left (hEbound t ht) hP) le_rfl))
  rw [intervalIntegral.integral_add hconst (hr.const_mul Q), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul] at hm
  simp only [smul_eq_mul] at hm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hRbound
  have hrle : (∫ s in a..b, massGradNormSq ρ π
      (fun i => (coupledPlainSynthesis N i (K i + 1) (y s)).val)) ≤ 2 * C / ν := by
    apply (le_div_iff₀ hν).mpr
    linarith
  have hqle := mul_le_mul_of_nonneg_left hrle hQ
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  change _ ≤ (P * (b - a) + Q * (2 / ν)) * C
  have halg : (P * (b - a) + Q * (2 / ν)) * C = (b - a) * (P * C) + Q * (2 * C / ν) := by ring
  rw [halg]
  linarith

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Constructed finite Fourier trajectories uniformly bounded in the fixed spacetime Hilbert space. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (hC : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk (K i) (h i))

include hρ hA hv hvp hC hp in
/-- Constructed finite solutions have one higher-order Bochner radius independent of N. -/
theorem plainCoupledFourierODE_exists_bochner_bound (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (hab : a ≤ b)
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
        (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N K f) a b (AVenhance.Infra.ODE.extendCurve hab y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b ∧
      (∀ t ∈ Set.Icc a b,
        massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (AVenhance.Infra.ODE.extendCurve hab y t)).val) +
          (ν / 2) * (∫ s in Set.Icc a b,
            massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (AVenhance.Infra.ODE.extendCurve hab y s)).val)) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) ∧
      ‖plainHigherBochner N K a b hab y‖ ^ 2 ≤
        ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) := by
  obtain ⟨y, hy, hyac, henergy⟩ := plainCoupledFourierODE_exists_energy N D ν ρ hρ K a b v A hA
    hv hvp hC hp F g hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur
    hab hv_bdd hv_meas hA_meas f hF hg
  obtain ⟨C, hC0, hbound⟩ := plainIntervalMatrix_bounded N D ν ρ hρ K a b hab v hv_bdd A hA
  have hm : ∀ r c, AEStronglyMeasurable
      (fun t => plainIntervalMatrix N D ν K a b hab v A t r c) volume := fun r c =>
    (plainIntervalMatrix_stronglyMeasurable N D ν K a b hab v hv_meas A hA_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (plainSourceCoefficients_integrable N K a b F g hF hg)
  have hint := plainMatrixODE_rhs_intervalIntegrable hab (plainIntervalMatrix N D ν K a b hab v A)
    _ (plainInitialCoefficients N K f) C hC0 hm hbound hf y
  have hint' := plainIntervalRhs_intervalIntegrable N D ν K a b hab v A _ _ hint
  have hh := plainODE_uniform_highTime_integral N D ν ρ hρ K a b v A hA hv hvp hC hp F g
    hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab
    (AVenhance.Infra.ODE.extendCurve hab y) (plainInitialCoefficients N K f) hy
    (AVenhance.Infra.ODE.continuous_extendCurve hab y) hF hg hint'
  have hinit : AVenhance.Infra.ODE.extendCurve hab y a = plainInitialCoefficients N K f := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, hab⟩
  rw [hinit] at hh
  refine ⟨y, hy, hyac, henergy, ?_⟩
  rw [plainHigherBochner_normSq]
  have hproj := plainInitialCoefficients_mass_le N K ρ π hπ f
  have hfactor : 0 ≤ (∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν) :=
    add_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => (hπ i).le)) (sub_nonneg.mpr hab))
      (mul_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ).le))
        (div_nonneg (by norm_num) hν.le))
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hfactor
  linarith

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify the genuine lower-order weak trace of the same finite sequence
by the integrated equation of its common spacetime weak limit. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainEquation_trace_pairing_eq_ae (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (K i) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (plainFourierMatrix (N n) D ν K v A r))
      (fun r => plainSourceCoefficients (N n) K (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) K f) a b (AVenhance.Infra.ODE.extendCurve hab (y n)))
    (U : CoupledHighTime (h := h) K a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) K a b hab (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) K a b hab (y n))) atTop (𝓝 (ell U)))
    (i : ι) (φ : TorusHk 1 (h i)) (u : ℝ → ℝ)
    (hc : ContinuousOn u (Set.Icc a b)) (R : ℝ)
    (hb : ∀ n, ∀ t ∈ Set.Icc a b, ‖torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
      (AVenhance.Infra.ODE.extendCurve hab (y n) t))‖ ≤ R)
    (hid : ∀ t ∈ Set.Icc a b,
      u t - inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
        coupledIntegratedRhs K D ν a t v A F g U i φ) :
    u =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      inner ℝ (U t i (valueIndex2 (K i + 1))) (torusHkValueCLM φ) := by
  apply plainBochner_trace_pairing_eq_ae K hab N y U hw i φ u
    (hc.aestronglyMeasurable measurableSet_Icc) R hb
  intro t ht
  have hp := plainFiniteTrace_value_pairing_tendsto D ν ρ hρ K hab ht v hv_bdd hv_meas
    hv A hA_bdd hA_meas hA F g hF hg f N hN y hy U Q hu hw i φ
  have he : inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) +
      coupledIntegratedRhs K D ν a t v A F g U i φ = u t := by
    rw [← hid t ht]
    ring
  rw [he] at hp
  exact hp

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The native Fourier RHS of arbitrary weak carriers is their actual
transport and spatial-flux source vector. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainCarrierRhs_eq_source (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ i l x, ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (r : CoupledFourierModeIndex (h := h) N) :
    coupledTimeRhs K D ν t v A F g (coupledCarrierHighJets K w) r.1 (coupledModeHk N r r.1 1) =
      plainSourceCoefficients N K
        (fun i => torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp w i + F i t)
        (fun i => g i t - torusTransportCarrier (v t) hv hvp (C i) (hC i) (w i)) r := by
  let U := coupledCarrierHighJets K w
  let T := fun i => torusTransportCarrier (v t) hv hvp (C i) (hC i) (w i)
  let G := fun i => torusGradientTensor (w i)
  let B := fun i i' (d : admissibleOrders K D i i') =>
    torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d) t ht
      (hc i i' d) (hp i i' d) (w i')
  have hT (i : ι) : (T i).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ k : Fin 2, v t x k • (U i
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) :=
    torusTransportCarrier_value_ae (v t) hv hvp (C i) (hC i) (w i)
  have hG (i : ι) : (G i).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      coupledHighGradientCLM (h := h) K i U := by
    exact (torusGradientTensor_value_ae (w i)).trans (coupledHighGradientCLM_ae K i U).symm
  have hB (i i' : ι) (d : admissibleOrders K D i i') :
      (B i i' d).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => A i i' d t x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
          (admissibleOrders_high_readout_bound K D i i' d) U x) := by
    have hm := torusCoupledFluxTerm_value_ae ρ hρ K D a b i i' d (A i i' d)
      (hA i i' d) t ht (hc i i' d) (hp i i' d) (w i')
    have hx := coupledHighTensorCLM_ae K i' (d.1 - 1)
      (admissibleOrders_high_readout_bound K D i i' d) U
    filter_upwards [hm, hx] with x hmx hxx
    exact hmx.trans (congrArg (A i i' d t x) hxx.symm)
  exact plainTimeRhs_eq_sourceCoefficient N K D ν t v hv.continuous V hV hvb A F g U T G B hT hG hB r

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The exact mass budget of the flux projection residual tends to the
original flux budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainResidualFlux_mass_limit (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (π : ι → ℝ) :
    let z := fun N i t => w i t - galerkinProj N (w i t)
    Tendsto (fun N => ∫ t in Set.Icc a b, massNormSq ρ π
      (fun i => (F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp (z N) i t).val))
      atTop (𝓝 (∫ t in Set.Icc a b, massNormSq ρ π (fun i => (F i t).val))) := by
  dsimp only
  let z : ℕ → ∀ i, ℝ → TorusHk (K i + 1) (h i) := fun N i t => w i t - galerkinProj N (w i t)
  have hz (N : ℕ) (i : ι) : MemLp (z N i) 2 (volume.restrict (Set.Icc a b)) := by
    simpa only [z, Pi.sub_apply, Function.comp_def] using!
      (hw i).sub ((galerkinProj N).comp_memLp' (hw i))
  exact torusMassNormSq_perturbed_integral_tendsto (volume.restrict (Set.Icc a b)) K ρ π F hF
    (fun N => torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp (z N))
    (fun N i => torusSpatialFluxPath_memLp K D a b ν ρ hρ A hA hc hp hab hmA (z N) (hz N) i)
    (fun i => torusSpatialFluxPath_tail_square_tendsto K D a b ν ρ hρ A hA hc hp hab hmA w hw i)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The Fourier coordinates of arbitrary weak carriers satisfy the actual
matrix equation with their exact projection residual as forcing. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainCarrierRhs_eq_matrix_residual (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ i l x, ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, TorusHk (K i + 1) (h i))
    (c : CoupledPlainCoefficients (h := h) N) (r : CoupledFourierModeIndex (h := h) N) :
    let z := fun i => w i - coupledPlainSynthesis N i (K i + 1) c
    coupledTimeRhs K D ν t v A F g (coupledCarrierHighJets K w) r.1 (coupledModeHk N r r.1 1) =
      plainMatrixCLM (plainFourierMatrix N D ν K v A t) c r +
        plainSourceCoefficients N K
          (fun i => F i t + torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp z i)
          (fun i => g i t - torusTransportCarrier (v t) hv hvp (C i) (hC i) (z i)) r := by
  dsimp only
  rw [plainCarrierRhs_eq_source N K D ν ρ hρ a b t ht v hv hvp V hV hvb C hC A hA hc hp F g w r]
  let z := fun i => w i - coupledPlainSynthesis N i (K i + 1) c
  let RF := fun i => F i t + torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp z i
  let Rg := fun i => g i t - torusTransportCarrier (v t) hv hvp (C i) (hC i) (z i)
  change _ = (plainMatrixCLM (plainFourierMatrix N D ν K v A t) c +
    plainSourceCoefficients N K RF Rg) r
  rw [plainFourierRhs_eq_totalSource N D ν ρ hρ K a b v A hA t ht hv hvp hc hp c RF Rg]
  have hs : (fun i => plainSpatialFlux N D ν ρ hρ K a b A hA t ht hc hp c i + RF i) =
      (fun i => torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp w i + F i t) := by
    funext i
    dsimp only [RF, z]
    rw [torusSpatialFluxCarrier_sub, torusSpatialFluxCarrier_synthesis]
    abel
  have hg : (fun i => -coupledPlainDriftHk N c i (K i) (v t) hv hvp + Rg i) =
      (fun i => g i t - torusTransportCarrier (v t) hv hvp (C i) (hC i) (w i)) := by
    funext i
    dsimp only [Rg, z]
    rw [torusTransportCarrier_sub, plainTransport_synthesis]
    abel
  rw [hs, hg]
end

/-! Construct the genuine time L² total flux and time L¹ total value source
representing every native Fourier RHS row of the common weak graph limit. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainNativeTrace_continuousOn (K : ι → ℕ) (D : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ν ρ : ℝ) (hρ : 0 < ρ) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (α B lam : ℝ)
    (hj : ∀ t ∈ Set.Icc a b, ∀ i l, 1 ≤ l → l ≤ K i → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j)
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hid : ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A F g U i φ)
    (hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b))
    (R : ℝ) (hub : ∀ i, ∀ t ∈ Set.Icc a b, ‖u i t‖ ≤ R)
    (huw : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (K i)) (coupledHighGraphReadout K i (U t))) :
    ∀ i, ContinuousOn (u i) (Set.Icc a b) := by
  obtain ⟨S, H, hS, hH, hq⟩ := plainPhysicalForcing_exists K D hab ν ρ hρ v hv hc hp V hV hb
    α B lam hj A hA hAm hAc hAp F g hF hg U hU
  let q : (L : ℕ) → ℝ → CoupledPlainCoefficients (h := h) L := fun L t z =>
    coupledTimeRhs K D ν t v A F g (U t) z.1 (coupledModeHk L z z.1 1)
  have hprim : ∀ L, ∀ t ∈ Set.Icc a b,
      plainInitialCoefficients L K (fun i => u i t) = plainInitialCoefficients L K f +
        ∫ r in a..t, q L r := by
    intro L t ht
    have hh := (plainTrace_coefficients_integralSolution L K D ν ρ hρ hab v hv
      (fun t ht => (hc t ht).continuous) V hb A hA hAm hAc F g hF hg U u f hid).2 t ht
    simpa only [AVenhance.Infra.ODE.linearRhs, plainMatrixCLM_zero_apply, zero_add] using hh
  have hsrc := plainTrace_sourcePrimitive K a b u f q S H hprim hq
  exact plainSourcePrimitive_continuousOn K hab S H hS hH u f
    (fun i t => coupledHighGraphReadout K i (U t)) (highTimeGraphReadout_memLp K a b U) huw
    hcont R hub hsrc
end

/-! Actual weak traces obey the projected matrix equation almost everywhere,
with the literal Fourier tail carriers as the residual forcing. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainNativeTrace_residualRhs_ae (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (hu : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (K i)) (w i t)) :
    let U := coupledCarrierHighTime K a b w hw
    let c := fun t => plainInitialCoefficients N K (fun i => u i t)
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath K a b v hv hvp C hC z i t
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r : CoupledFourierModeIndex (h := h) N,
      coupledTimeRhs K D ν t v A F g (U t) r.1 (coupledModeHk N r r.1 1) =
        plainMatrixCLM (plainFourierMatrix N D ν K v A t) (c t) r +
          plainSourceCoefficients N K (fun i => RF i t) (fun i => Rg i t) r := by
  dsimp only
  filter_upwards [coupledCarrierHighTime_ae K a b w hw, hu,
    ae_restrict_mem measurableSet_Icc] with t htU htu ht
  intro r
  have heU : coupledCarrierHighTime K a b w hw t = coupledCarrierHighJets K (fun i => w i t) := by
    apply PiLp.ext
    intro i
    exact (htU i).symm
  rw [heU]
  let c := plainInitialCoefficients N K (fun i => u i t)
  have hec (i : ι) : coupledPlainSynthesis N i (K i + 1) c = galerkinProj N (w i t) := by
    have heu : (fun j => u j t) = (fun j => truncateTorusHk (Nat.le_succ (K j)) (w j t)) := funext htu
    dsimp only [c]
    rw [heu]
    exact plainInitialCoefficients_higher_synthesis N K (fun j => w j t) i
  have hh := plainCarrierRhs_eq_matrix_residual N K D ν ρ hρ a b t ht v (hv t ht) (hvp t ht)
    V hV (hvb t ht) C (hC t ht) A hA (hc t ht) (hp t ht) F g (fun i => w i t) c r
  dsimp only at hh
  simp_rw [hec] at hh
  simp_rw [torusSpatialFluxPath_of_mem K D a b ν ρ hρ A hA hc hp _ t ht]
  simpa only [plainTransportCarrierPath, dite_eq_left ht] using! hh
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! One common spacetime weak subsequence of actual finite Fourier energy solutions. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (hC : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk (K i) (h i))

include hρ hA hv hvp hC hp in
/-- Actual finite Fourier solutions possess a common weak limit with genuine periodic Sobolev jets. -/
theorem plainCoupledFourier_energy_weak_subsequence (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (hab : a ≤ b)
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ y : (N : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) N),
      ∃ (U : CoupledHighTime (h := h) K a b) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ N, AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
        (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N K f) a b (AVenhance.Infra.ODE.extendCurve hab (y N)) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab (y N)) a b ∧
      (∀ t ∈ Set.Icc a b,
        massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (AVenhance.Infra.ODE.extendCurve hab (y N) t)).val) +
          (ν / 2) * (∫ s in Set.Icc a b,
            massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (AVenhance.Infra.ODE.extendCurve hab (y N) s)).val)) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) ∧
      ‖plainHigherBochner N K a b hab (y N)‖ ^ 2 ≤
        ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2)) ∧
      (∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
        Filter.Tendsto (fun n => ell (plainHigherBochner (φ n) K a b hab (y (φ n))))
          Filter.atTop (𝓝 (ell U))) ∧
      (∀ i, MemLp (fun t => coupledHighGraphReadout K i (U t)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout K i (U t)).val = U t i) ∧
      (∀ t ∈ Set.Icc a b, ∃ (V : CoupledLowHilbert (h := h) K) (ψ : ℕ → ℕ), StrictMono ψ ∧
        (∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
          Filter.Tendsto (fun n => ell (plainLowerSynthesisCLM (φ (ψ n)) K
            (AVenhance.Infra.ODE.extendCurve hab (y (φ (ψ n))) t)))
            Filter.atTop (𝓝 (ell V))) ∧
        (∀ i, V i ∈ torusHkGraph (E := h i) (K i)) ∧
        (t = a → V = WithLp.toLp 2 (fun i => (f i).val)) ∧
        (‖V‖ ≤ Real.sqrt ((∑ i, π i / factorialWeightMin ρ (K i)) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2))) ∧
        (∀ i, ∀ ζ : TorusHk 1 (h i),
          inner ℝ (coupledLowValueCLM (h := h) K i V) (torusHkValueCLM ζ) -
            inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM ζ) =
            coupledIntegratedRhs K D ν a t v A F g U i ζ)) := by
  classical
  choose y hy using (fun N => plainCoupledFourierODE_exists_bochner_bound N D ν ρ hρ K a b v A hA
    hv hvp hC hp F g hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur
    hab hv_bdd hv_meas hA_meas f hF hg)
  let M : ℝ := ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2)
  have hnorm (N : ℕ) : ‖plainHigherBochner N K a b hab (y N)‖ ≤ Real.sqrt M := by
    have hs := (hy N).2.2.2
    change _ ≤ M at hs
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hs
  obtain ⟨U, φ, hφ, hclm⟩ := exists_strictMono_tendsto_highTime_clm K a b (Real.sqrt M)
    (fun N => plainHigherBochner N K a b hab (y N)) hnorm
  refine ⟨y, U, φ, hφ, hy, hclm, fun i => highTimeGraphReadout_memLp K a b U i, ?_⟩
  constructor
  · apply highTimeGraphReadout_val_ae K a b hclm
    intro n
    exact plainHigherBochner_graph_ae (φ n) K a b hab (y (φ n))
  · intro t ht
    let C : ℝ := 2 * massNormSq ρ π (fun i => (f i).val) +
      (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
      10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2
    have he (n : ℕ) : massNormSq ρ π (fun i => (coupledPlainSynthesis (φ n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y (φ n)) t)).val) ≤ C := by
      have he := (hy (φ n)).2.2.1 t ht
      have hdiss : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ π (fun i => (coupledPlainSynthesis (φ n) i (K i + 1)
            (AVenhance.Infra.ODE.extendCurve hab (y (φ n)) s)).val)) :=
        mul_nonneg (div_nonneg hν.le (by norm_num))
          (integral_nonneg (fun s => massGradNormSq_nonneg ρ π hπ _))
      change _ ≤ C at he
      linarith
    obtain ⟨V, ψ, hψ, hw, hgraph, hnormV⟩ := plainLower_mass_subsequence K ρ hρ π hπ φ
      (fun n => AVenhance.Infra.ODE.extendCurve hab (y (φ n)) t) C he
    refine ⟨V, ψ, hψ, hw, hgraph, ?_, hnormV, ?_⟩
    · intro hta
      subst t
      have hinitial (N : ℕ) : AVenhance.Infra.ODE.extendCurve hab (y N) a =
          plainInitialCoefficients N K f := by
        simpa only [intervalIntegral.integral_same, add_zero] using (hy N).1 a ⟨le_rfl, hab⟩
      apply plainInitialLower_subsubsequence_eq K f φ ψ hφ hψ V
      intro ell
      simpa only [hinitial] using hw ell
    · intro i ζ
      let Qlo : ℝ := ∑ j, π j / factorialWeightMin ρ (K j)
      have hQlo : 0 ≤ Qlo := Finset.sum_nonneg (fun j _ =>
        div_nonneg (hπ j).le (factorialWeightMin_pos ρ hρ (K := K j)).le)
      have hl (n : ℕ) : ‖plainLowerSynthesisCLM (φ (ψ n)) K
          (AVenhance.Infra.ODE.extendCurve hab (y (φ (ψ n))) t)‖ ≤ Real.sqrt (Qlo * C) := by
        have hsq := (plainLowerSynthesis_normSq_le_mass (φ (ψ n)) K ρ hρ π hπ
          (AVenhance.Infra.ODE.extendCurve hab (y (φ (ψ n))) t)).trans
          (mul_le_mul_of_nonneg_left (he (ψ n)) hQlo)
        simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq
      exact plainClosedTrace_component_identity D ν ρ hρ K hab ht v hv_bdd hv_meas
        (fun r hr => (hv r hr).continuous) A hA hA_meas hC F g hF hg f
        (φ ∘ ψ) (hφ.comp hψ) (fun n => y (φ (ψ n))) (fun n => (hy (φ (ψ n))).1)
        U (Real.sqrt M) (fun n => hnorm (φ (ψ n)))
        (fun ell => (hclm ell).comp hψ.tendsto_atTop)
        V (Real.sqrt (Qlo * C)) hl hw i ζ

end AVRegularity.CoupledEnergy.Galerkin
end
