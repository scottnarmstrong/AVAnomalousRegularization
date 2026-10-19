-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSequence
public import AVRegularity.CoupledEnergy.Variational.TorusSpatialFluxTimeLp
public import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Every weak solution of the coupled torus problem gives a continuous plain coefficient curve
satisfying the actual projected matrix ODE with its Fourier residual sources. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainWeakSolution_residualODE_exists (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath K a b v hv hvp C hC z i t
    ∃ y : ℝ → CoupledPlainCoefficients (h := h) N,
      Continuous y ∧
      (∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N K (fun i => u i t)) ∧
      IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
        (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
        (fun t => plainSourceCoefficients N K (fun i => RF i t) (fun i => Rg i t)) y) volume a b ∧
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
        (fun t => plainSourceCoefficients N K (fun i => RF i t) (fun i => Rg i t))
        (plainInitialCoefficients N K f) a b y := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let RF := fun i t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp z i t
  let Rg := fun i t => g i t - plainTransportCarrierPath K a b v hv hvp C hC z i t
  let U := coupledCarrierHighTime K a b w hsol.2.1
  let c := fun t => plainInitialCoefficients N K (fun i => u i t)
  let q : ℝ → CoupledPlainCoefficients (h := h) N := fun t r =>
    coupledTimeRhs K D ν t v A F g (U t) r.1 (coupledModeHk N r r.1 1)
  have hccont : ContinuousOn c (Set.Icc a b) := by
    apply plainTrace_coefficients_continuousOn N K a b u
    intro i φ
    exact ((torusHkValueCLM (K := K i) (E := h i)).continuous.comp_continuousOn (hsol.1 i)).inner continuousOn_const
  let curve : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N) :=
    ⟨fun t => c t, continuousOn_iff_continuous_domRestrict.mp hccont⟩
  let y := AVenhance.Infra.ODE.extendCurve hab curve
  have hy (t : ℝ) (ht : t ∈ Set.Icc a b) : y t = c t := by
    exact AVenhance.Infra.ODE.extendCurve_eq_of_mem hab curve ht
  have hnative := torusRawWeakSolution_nativeEquation K D ν ρ hρ hab v hmv
    (fun t ht => (hv t ht).continuous) V hvb A hA hmA hc F g hF hg w u f hsol
  obtain ⟨hq, hprim⟩ := plainTrace_coefficients_integralSolution N K D ν ρ hρ hab v hmv
    (fun t ht => (hv t ht).continuous) V hvb A hA hmA hc F g hF hg U u f hnative
  have halign : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (K i)) (w i t) := by
    filter_upwards [ae_all_iff.mpr hsol.2.2.1] with t ht
    exact fun i => (ht i).symm
  have hrows := plainNativeTrace_residualRhs_ae N K D ν ρ hρ a b v hv hvp V hV hvb C hC
    A hA hc hp F g w hsol.2.1 u halign
  have he : q =ᵐ[volume.restrict (Set.Icc a b)] AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => RF i t) (fun i => Rg i t)) y := by
    filter_upwards [hrows, ae_restrict_mem measurableSet_Icc] with t ht htI
    funext r
    simp only [AVenhance.Infra.ODE.linearRhs, Pi.add_apply, hy t htI]
    exact ht r
  obtain ⟨hint, hode⟩ := plainPrimitive_changeRhs hab q c y (plainInitialCoefficients N K f)
    (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
    (fun t => plainSourceCoefficients N K (fun i => RF i t) (fun i => Rg i t)) hq hprim hy he
  exact ⟨y, AVenhance.Infra.ODE.continuous_extendCurve hab curve, hy, hint, hode⟩

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The exact mass value-source budget of the transport projection residual
converges with the original source in time L¹. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainResidualValue_mass_limit (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    let z := fun N i t => w i t - galerkinProj N (w i t)
    Tendsto (fun N => ∫ t in Set.Icc a b, Real.sqrt (massNormSq ρ π
      (fun i => (g i t - plainTransportCarrierPath K a b v hv hvp C hC (z N) i t).val)))
      atTop (𝓝 (∫ t in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i t).val)))) := by
  dsimp only
  let z : ℕ → ∀ i, ℝ → TorusHk (K i + 1) (h i) := fun N i t => w i t - galerkinProj N (w i t)
  have hz (N : ℕ) (i : ι) : MemLp (z N i) 2 (volume.restrict (Set.Icc a b)) := by
    simpa only [z, Pi.sub_apply, Function.comp_def] using!
      (hw i).sub ((galerkinProj N).comp_memLp' (hw i))
  let T : ℕ → ∀ i, ℝ → TorusHk (K i) (h i) := fun N => plainTransportCarrierPath K a b v hv hvp C hC (z N)
  have hT (N : ℕ) (i : ι) : Integrable (T N i) (volume.restrict (Set.Icc a b)) :=
    (plainTransportCarrierPath_memLp K a b v hv hvp C hC hab ρ hρ hmv V hV hvb (z N) (hz N) i).integrable (by norm_num)
  exact torusMassNorm_sub_integral_tendsto (volume.restrict (Set.Icc a b)) K ρ π hπ g hg T hT
    (fun i => plainTransportCarrierPath_tail_norm_tendsto K a b v hv hvp C hC
      hab ρ hρ hmv V hV hvb w hw i)

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
theorem plainCoupledFourier_exists_weakTrace (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
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
    ∃ (U : CoupledHighTime (h := h) K a b) (u : ∀ i, ℝ → TorusHk (K i) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout K i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout K i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (K i)) (coupledHighGraphReadout K i (U t))) := by
  classical
  obtain ⟨y, U, n, hn, hy, hw, hmem, hgraphAE, hpoint⟩ :=
    plainCoupledFourier_energy_weak_subsequence D ν ρ hρ K a b v A hA hv hvp hC hp F g
      hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab hv_bdd hv_meas hA_meas f hF hg
  choose V ψ hψ hweak hgraph hinitial hnorm hid using (fun r : Set.Icc a b => hpoint r r.property)
  let u : ∀ i, ℝ → TorusHk (K i) (h i) := fun i r =>
    if hr : r ∈ Set.Icc a b then ⟨V ⟨r, hr⟩ i, hgraph ⟨r, hr⟩ i⟩ else 0
  have huval (i : ι) (r : ℝ) (hr : r ∈ Set.Icc a b) : (u i r).val = V ⟨r, hr⟩ i := by
    simp only [u, dite_eq_left hr]
  have hidentity (i : ι) (r : ℝ) (hr : r ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
      inner ℝ (torusHkValueCLM (u i r)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
        coupledIntegratedRhs K D ν a r v A F g U i φ := by
    have hi := hid ⟨r, hr⟩ i φ
    change inner ℝ ((u i r).val (valueIndex2 (K i))) _ - _ = _
    rw [huval i r hr]
    exact hi
  have hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b) := by
    intro i φ
    obtain ⟨Bv, hBv⟩ := hv_bdd
    have hc := coupledIntegratedRhs_continuousOn K D ν ρ hρ hab v hv_meas
      (fun r hr => (hv r hr).continuous) Bv hBv A hA hA_meas hC F g hF hg U i φ
    apply (hc.add continuousOn_const).congr
    intro r hr
    exact eq_add_of_sub_eq (hidentity i r hr φ)

  have hbound : ∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R := by
    refine ⟨Real.sqrt ((∑ i, π i / factorialWeightMin ρ (K i)) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2)), ?_⟩
    intro i r hr
    change ‖(u i r).val‖ ≤ _
    rw [huval i r hr]
    exact (PiLp.norm_apply_le (V ⟨r, hr⟩) i).trans (hnorm ⟨r, hr⟩)
  let C : ℝ := 2 * massNormSq ρ π (fun i => (f i).val) +
    (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
    10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2
  let Qlo : ℝ := ∑ i, π i / factorialWeightMin ρ (K i)
  let M : ℝ := ((∑ i, π i) * (b - a) + Qlo * (2 / ν)) * C
  have hQlo : 0 ≤ Qlo := Finset.sum_nonneg (fun i _ =>
    div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ (K := K i)).le)
  have hhigh (m : ℕ) : ‖plainHigherBochner (n m) K a b hab (y (n m))‖ ≤ Real.sqrt M := by
    have hs := (hy (n m)).2.2.2
    change _ ≤ M at hs
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hs
  have hfinite (m : ℕ) (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖torusHkValueCLM (coupledPlainSynthesis (n m) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y (n m)) t))‖ ≤ Real.sqrt (Qlo * C) := by
    have he := (hy (n m)).2.2.1 t ht
    have hdiss : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
        massGradNormSq ρ π (fun i => (coupledPlainSynthesis (n m) i (K i + 1)
          (AVenhance.Infra.ODE.extendCurve hab (y (n m)) s)).val)) :=
      mul_nonneg (div_nonneg hν.le (by norm_num))
        (integral_nonneg (fun s => massGradNormSq_nonneg ρ π hπ _))
    have hemass : massNormSq ρ π (fun i => (coupledPlainSynthesis (n m) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y (n m)) t)).val) ≤ C := by
      change _ ≤ C at he
      linarith
    have hsq := (plainLowerSynthesis_normSq_le_mass (n m) K ρ hρ π hπ
      (AVenhance.Infra.ODE.extendCurve hab (y (n m)) t)).trans
      (mul_le_mul_of_nonneg_left hemass hQlo)
    have hl : ‖plainLowerSynthesisCLM (n m) K
        (AVenhance.Infra.ODE.extendCurve hab (y (n m)) t)‖ ≤ Real.sqrt (Qlo * C) := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq
    exact (PiLp.norm_apply_le
      (coupledPlainSynthesis (n m) i (K i) (AVenhance.Infra.ODE.extendCurve hab (y (n m)) t)).val
      (valueIndex2 (K i))).trans ((PiLp.norm_apply_le
        (plainLowerSynthesisCLM (n m) K (AVenhance.Infra.ODE.extendCurve hab (y (n m)) t)) i).trans hl)
  have halign : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (K i)) (coupledHighGraphReadout K i (U t)) := by
    apply plainTrace_eq_highGraph_ae K a b U u hgraphAE
    intro cutoff
    apply ae_all_iff.mpr
    intro r
    exact plainEquation_trace_pairing_eq_ae D ν ρ hρ K hab v hv_bdd hv_meas
      (fun t ht => (hv t ht).continuous) A hA hA_meas hC F g hF hg f n hn
      (fun m => y (n m)) (fun m => (hy (n m)).1) U (Real.sqrt M) hhigh hw
      r.1 (coupledModeHk cutoff r r.1 1) _ (hcont r.1 _) (Real.sqrt (Qlo * C))
      (fun m t ht => hfinite m r.1 t ht) (fun t ht => hidentity r.1 t ht _)
  obtain ⟨R, hR⟩ := hbound
  refine ⟨U, u, hmem, hgraphAE, ?_, ⟨R, hR⟩, hidentity, hcont, ?_, halign⟩
  · intro i
    apply Subtype.ext
    rw [huval i a ⟨le_rfl, hab⟩, hinitial ⟨a, ⟨le_rfl, hab⟩⟩ rfl]
  · exact fun i => plainTrace_memLp K a b u hcont R hR i

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The exact flux and value-source budgets of the Fourier residual system
converge to the original forcing budgets. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainResidualSources_mass_limits (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    let z := fun N i t => w i t - galerkinProj N (w i t)
    let RF := fun N i t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp (z N) i t
    let Rg := fun N i t => g i t - plainTransportCarrierPath K a b v hv hvp C hC (z N) i t
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b, massNormSq ρ π (fun i => (RF N i t).val))
      Filter.atTop (nhds (∫ t in Set.Icc a b, massNormSq ρ π (fun i => (F i t).val))) ∧
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (Rg N i t).val)))
      Filter.atTop (nhds (∫ t in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i t).val)))) := by
  refine ⟨plainResidualFlux_mass_limit K D ν ρ hρ a b hab A hA hmA hc hp F hF w hw π, ?_⟩
  exact plainResidualValue_mass_limit K ρ hρ a b hab v hmv hv hvp V hV hvb C hC g w hw hg π hπ
end

/-! Every weak solution of the coupled torus problem obeys the finite Fourier energy
estimate, with its exact vanishing projection residual sources. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainWeakSolution_projected_energy (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (α B lam : ℝ)
    (hα : 0 ≤ α) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A)) :
    let z : ∀ i, ℝ → TorusHk (K i + 1) (h i) := fun i t => w i t - galerkinProj N (w i t)
    let RF : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun i t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp z i t
    let Rg : ∀ i, ℝ → TorusHk (K i) (h i) := fun i t => g i t - plainTransportCarrierPath K a b v hv hvp C hC z i t
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ π (fun i => (galerkinProj N (u i t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (galerkinProj N (w i s)).val)) ≤
      2 * massNormSq ρ π (fun i => (galerkinProj N (f i)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (RF i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (Rg i s).val))) ^ 2 := by
  dsimp only
  let z : ∀ i, ℝ → TorusHk (K i + 1) (h i) := fun i t => w i t - galerkinProj N (w i t)
  let RF : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun i t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp z i t
  let Rg : ∀ i, ℝ → TorusHk (K i) (h i) := fun i t => g i t - plainTransportCarrierPath K a b v hv hvp C hC z i t
  have hzLp (i : ι) : MemLp (z i) 2 (volume.restrict (Set.Icc a b)) := by
    simpa only [z, Pi.sub_apply, Function.comp_def] using!
      (hsol.2.1 i).sub ((galerkinProj N).comp_memLp' (hsol.2.1 i))
  have hRF (i : ι) : MemLp (RF i) 2 (volume.restrict (Set.Icc a b)) :=
    torusForcedSpatialFluxPath_memLp K D a b ν ρ hρ A hA hc hp hab hmA z hzLp F hF i
  have hRg (i : ι) : Integrable (Rg i) (volume.restrict (Set.Icc a b)) := by
    have ht := plainTransportCarrierPath_memLp K a b v hv hvp C hC hab ρ hρ hmv V hV hvb z hzLp i
    simpa only [Rg, Pi.sub_apply] using! (hg i).sub (ht.integrable (by norm_num))
  obtain ⟨y, hycont, hy, hint, hode⟩ := plainWeakSolution_residualODE_exists N K D ν ρ hρ
    a b hab v hmv hv hvp V hV hvb C hC A hA hmA hc hp F g w u f hF hg hsol
  have henergy := plainODE_uniform_mass_energy N D ν ρ hρ K a b v A hA hv hvp hc hp RF Rg
    hν π hπ Kmax hK α B lam hα hB hlam hsmall hstrain hd hjets hschur hab y
      (plainInitialCoefficients N K f) hode hycont hRF hRg hint
  have hlower (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) :
      coupledPlainSynthesis N i (K i) (y t) = galerkinProj N (u i t) := by
    rw [hy t ht]
    exact plainInitialCoefficients_synthesis N K (fun j => u j t) i
  have hinit (i : ι) : coupledPlainSynthesis N i (K i) (y a) = galerkinProj N (f i) := by
    rw [hlower a ⟨le_rfl, hab⟩ i, hsol.2.2.2.1 i]
  have hhigher : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ i,
      coupledPlainSynthesis N i (K i + 1) (y s) = galerkinProj N (w i s) := by
    filter_upwards [ae_all_iff.mpr hsol.2.2.1, ae_restrict_mem measurableSet_Icc] with s hs hsI
    intro i
    rw [hy s hsI]
    have he : (fun j => u j s) = (fun j => truncateTorusHk (Nat.le_succ (K j)) (w j s)) :=
      funext (fun j => (hs j).symm)
    rw [he]
    exact plainInitialCoefficients_higher_synthesis N K (fun j => w j s) i
  have hintEq : (∫ s in Set.Icc a b, massGradNormSq ρ π
      (fun i => (coupledPlainSynthesis N i (K i + 1) (y s)).val)) =
      ∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (galerkinProj N (w i s)).val) := by
    apply integral_congr_ae
    filter_upwards [hhigher] with s hs
    simp only [hs]
  intro t ht
  have he := henergy t ht
  simp only [hlower t ht, hinit, hintEq] at he
  exact he
end

/-! The exact coupled energy bound for every weak solution of the coupled torus problem.
All Fourier residual source budgets vanish in the limiting estimate. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainWeakSolution_energy (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (α B lam : ℝ)
    (hα : 0 ≤ α) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A)) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ π (fun i => (u i t).val) +
        (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (w i s).val)) ≤
      2 * massNormSq ρ π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2 := by
  obtain ⟨hflux, hvalue⟩ := plainResidualSources_mass_limits K D ν ρ hρ a b hab v hmv hv hvp
    V hV hvb C hC A hA hmA hc hp F g w hsol.2.1 hF hg π hπ
  have hgrad := galerkinProj_massGradNormSq_integral_tendsto K a b ρ π w hsol.2.1
  have hinitial := galerkinProj_massNormSq_tendsto K ρ π hπ f
  intro t ht
  have htime := galerkinProj_massNormSq_tendsto K ρ π hπ (fun i => u i t)
  have hleft := htime.add (hgrad.const_mul (ν / 2))
  have hright := ((hinitial.const_mul 2).add (hflux.const_mul (8 / ν))).add ((hvalue.pow 2).const_mul 10)
  exact le_of_tendsto_of_tendsto' hleft hright (fun N =>
    plainWeakSolution_projected_energy N K D ν ρ hρ a b hab v hmv hv hvp V hV hvb C hC
      A hA hmA hc hp F g w u f hF hg hsol hν π hπ Kmax hK α B lam hα hB hlam hsmall hstrain
      hd hjets hschur t ht)
end

/-! Uniqueness of weak solutions of the coupled torus problem: the exact coupled energy bound
applied to the difference of two solutions with the same data. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainWeakSolution_unique (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (α B lam : ℝ)
    (hα : 0 ≤ α) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (u' : ∀ i, ℝ → TorusHk (K i) (h i)) (w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hsol' : IsCoupledWeakSolutionTorus ν a b v D K A f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  have hdiff := torusWeakSolution_difference K D ν ρ hρ hab v hmv
    (fun t ht => (hv t ht).continuous) V hvb A hA hmA hc F g hF hg w w' u u' f hsol hsol'
  have he := plainWeakSolution_energy (h := h) K D ν ρ hρ a b hab v hmv hv hvp V hV hvb C hC
    A hA hmA hc hp (fun _ _ => 0) (fun _ _ => 0) (fun i t => w i t - w' i t)
    (fun i t => u i t - u' i t) (fun _ => 0) (fun i => timeMemLp_zero (E := TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (volume.restrict (Set.Icc a b)) 2)
    (fun i => timeIntegrable_zero (E := TorusHk (K i) (h i)) (volume.restrict (Set.Icc a b))) hdiff hν π hπ Kmax hK α B lam hα hB hlam hsmall hstrain
    hd hjets hschur
  intro i t ht
  have hh := he t ht
  simp only [torusMassNormSq_zero K ρ π hπ,
    Real.sqrt_zero, integral_zero, mul_zero, zero_add, zero_pow (by decide : 2 ≠ 0)] at hh
  have hg0 : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
      massGradNormSq ρ π (fun i => (w i s - w' i s).val)) :=
    mul_nonneg (div_nonneg hν.le (by norm_num))
      (integral_nonneg (fun s => massGradNormSq_nonneg ρ π hπ _))
  have hm : massNormSq ρ π (fun i => (u i t - u' i t).val) ≤ 0 := by linarith
  exact sub_eq_zero.mp (torusCarrier_eq_zero_of_mass_le_zero K ρ hρ π hπ
    (fun i => u i t - u' i t) hm i)
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Actual strong closed-time traces of the common coupled Galerkin limit.
All spectral-tail premises are discharged from the original equation. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
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
theorem plainCoupledFourier_exists_strongTrace (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
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
    ∃ (U : CoupledHighTime (h := h) K a b) (u : ∀ i, ℝ → TorusHk (K i) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout K i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout K i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (K i)) (coupledHighGraphReadout K i (U t))) ∧
      (∀ i, ContinuousOn (u i) (Set.Icc a b)) := by
  obtain ⟨U, u, hmem, hgraph, hinit, hbound, hid, hcont, huLp, huw⟩ :=
    plainCoupledFourier_exists_weakTrace D ν ρ hρ K a b v A hA hv hvp hC hp F g hν π hπ
      Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab hv_bdd hv_meas hA_meas f hF hg
  obtain ⟨R, hR⟩ := hbound
  obtain ⟨V, hV⟩ := hv_bdd
  have hV0 : 0 ≤ V := (norm_nonneg (v a 0)).trans (hV a ⟨le_rfl, hab⟩ 0)
  have hj : ∀ t ∈ Set.Icc a b, ∀ i l, 1 ≤ l → l ≤ K i → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l) := by
    intro t ht i l hl hlK
    exact hjets t ht l hl (hlK.trans (hK i))
  have hs := plainNativeTrace_continuousOn K D hab ν ρ hρ v hv_meas hv hvp V hV0 hV
    αv B lam hj A hA hA_meas hC hp F g hF hg U hgraph u f hid hcont R hR huw
  exact ⟨U, u, hmem, hgraph, hinit, ⟨R, hR⟩, hid, hcont, huLp, huw, hs⟩
end

/-! Actual strong closed-time traces of the common coupled Galerkin limit.
All spectral-tail premises are discharged from the original equation. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
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
theorem plainCoupledFourier_exists_weakSolution (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
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
    ∃ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b v D K A f F g u w := by
  obtain ⟨U, u, hmem, hgraph, hinit, _, hid, _, _, huw, hstrong⟩ :=
    plainCoupledFourier_exists_strongTrace D ν ρ hρ K a b v A hA hv hvp hC hp F g hν π hπ
      Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab hv_bdd hv_meas hA_meas f hF hg
  obtain ⟨V, hV⟩ := hv_bdd
  let w := fun i t => coupledHighGraphReadout K i (U t)
  have hidentity := torusNativeEquation_implies_rawWeakIdentity K D ν ρ hρ hab v hv_meas
    (fun r hr => (hv r hr).continuous) V hV A hA hA_meas hC F g hF hg U w hgraph u f hid
  refine ⟨u, w, hstrong, hmem, ?_, hinit, ?_⟩
  · intro i
    exact huw.mono (fun r hr => (hr i).symm)
  · intro i t ht φ
    simpa only [torusRawCouplingFlux] using! hidentity i t ht φ
end

end AVRegularity.CoupledEnergy.Galerkin
end
