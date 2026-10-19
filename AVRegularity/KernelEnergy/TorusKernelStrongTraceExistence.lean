-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSolutionExistence
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionTorus
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Hilbert weak compactness and closed Sobolev graph readout. -/

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
theorem kernelFourier_exists_weakTrace
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (U : CoupledHighTime (h := h) (fun _ => k) a b) (u : ∀ i, ℝ → TorusHk (k) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout (fun _ => k) i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout (fun _ => k) i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          P.kernelIntegratedRhs t v F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (k)) (coupledHighGraphReadout (fun _ => k) i (U t))) := by
  classical
  obtain ⟨y, U, n, hn, hy, hw, hmem, hgraphAE, hpoint⟩ :=
    P.kernelFourier_energy_closedTrace_subsequence v hv hvp F g αv B lam
      hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f hF hg
  choose V ψ hψ hweak hgraph hinitial hnorm hid using (fun r : Set.Icc a b => hpoint r r.property)
  let u : ∀ i, ℝ → TorusHk (k) (h i) := fun i r =>
    if hr : r ∈ Set.Icc a b then ⟨V ⟨r, hr⟩ i, hgraph ⟨r, hr⟩ i⟩ else 0
  have huval (i : ι) (r : ℝ) (hr : r ∈ Set.Icc a b) : (u i r).val = V ⟨r, hr⟩ i := by
    simp only [u, dite_eq_left hr]
  have hidentity (i : ι) (r : ℝ) (hr : r ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
      inner ℝ (torusHkValueCLM (u i r)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
        P.kernelIntegratedRhs r v F g U i φ := by
    have hi := hid ⟨r, hr⟩ i φ
    change inner ℝ ((u i r).val (valueIndex2 (k))) _ - _ = _
    rw [huval i r hr]
    exact hi
  have hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b) := by
    intro i φ
    obtain ⟨Bv, hBv⟩ := hv_bdd
    have hc := P.kernelIntegratedRhs_continuousOn v hv_meas
      (fun r hr => (hv r hr).continuous) Bv hBv F g hF hg U i φ
    apply (hc.add continuousOn_const).congr
    intro r hr
    exact eq_add_of_sub_eq (hidentity i r hr φ)

  have hbound : ∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R := by
    refine ⟨Real.sqrt ((∑ i, P.π i / factorialWeightMin ρ (k)) *
          (2 * massNormSq ρ P.π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2)), ?_⟩
    intro i r hr
    change ‖(u i r).val‖ ≤ _
    rw [huval i r hr]
    exact (PiLp.norm_apply_le (V ⟨r, hr⟩) i).trans (hnorm ⟨r, hr⟩)
  let C : ℝ := 2 * massNormSq ρ P.π (fun i => (f i).val) +
    (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
    10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2
  let Qlo : ℝ := ∑ i, P.π i / factorialWeightMin ρ (k)
  let M : ℝ := ((∑ i, P.π i) * (b - a) + Qlo * (2 / ν)) * C
  have hQlo : 0 ≤ Qlo := Finset.sum_nonneg (fun i _ =>
    div_nonneg (P.hπ i).le (factorialWeightMin_pos ρ P.radius_pos (K := k)).le)
  have hhigh (m : ℕ) : ‖plainHigherBochner (n m) (fun _ => k) a b P.htime (y (n m))‖ ≤ Real.sqrt M := by
    have hs := (hy (n m)).2.2.2
    change _ ≤ M at hs
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hs
  have hfinite (m : ℕ) (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖torusHkValueCLM (coupledPlainSynthesis (n m) i (k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t))‖ ≤ Real.sqrt (Qlo * C) := by
    have he := (hy (n m)).2.2.1 t ht
    have hdiss : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
        massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis (n m) i (k + 1)
          (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) s)).val)) :=
      mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
        (integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _))
    have hemass : massNormSq ρ P.π (fun i => (coupledPlainSynthesis (n m) i (k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)).val) ≤ C := by
      change _ ≤ C at he
      linarith
    have hsq := (plainLowerSynthesis_normSq_le_mass (n m) (fun _ => k) ρ P.radius_pos P.π P.hπ
      (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)).trans
      (mul_le_mul_of_nonneg_left hemass hQlo)
    have hl : ‖plainLowerSynthesisCLM (n m) (fun _ => k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)‖ ≤ Real.sqrt (Qlo * C) := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq
    exact (PiLp.norm_apply_le
      (coupledPlainSynthesis (n m) i (k) (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)).val
      (valueIndex2 (k))).trans ((PiLp.norm_apply_le
        (plainLowerSynthesisCLM (n m) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)) i).trans hl)
  have halign : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (k)) (coupledHighGraphReadout (fun _ => k) i (U t)) := by
    apply plainTrace_eq_highGraph_ae (fun _ => k) a b U u hgraphAE
    intro cutoff
    apply ae_all_iff.mpr
    intro r
    exact P.kernelEquation_trace_pairing_eq_ae v hv_bdd hv_meas
      (fun t ht => (hv t ht).continuous) F g hF hg f n hn
      (fun m => y (n m)) (fun m => (hy (n m)).1) U (Real.sqrt M) hhigh hw
      r.1 (coupledModeHk cutoff r r.1 1) _ (hcont r.1 _) (Real.sqrt (Qlo * C))
      (fun m t ht => hfinite m r.1 t ht) (fun t ht => hidentity r.1 t ht _)
  obtain ⟨R, hR⟩ := hbound
  refine ⟨U, u, hmem, hgraphAE, ?_, ⟨R, hR⟩, hidentity, hcont, ?_, halign⟩
  · intro i
    apply Subtype.ext
    rw [huval i a ⟨le_rfl, P.htime⟩, hinitial ⟨a, ⟨le_rfl, P.htime⟩⟩ rfl]
  · exact fun i => plainTrace_memLp (fun _ => k) a b u hcont R hR i

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_residualEnergy
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
      ∀ t ∈ Set.Icc a b,
        massNormSq ρ P.π (fun i => (galerkinProj N (u i t)).val) +
          (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ P.π
            (fun i => (galerkinProj N (w i s)).val)) ≤
        2 * massNormSq ρ P.π (fun i => (galerkinProj N (f i)).val) +
          (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π
            (fun i => (RF i s - P.finiteFlux N y i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (Rg i s).val))) ^ 2 := by

  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let RF := fun i t => F i t + P.diffusionResidual z i t
  let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
  obtain ⟨y, hycont, hy, hRFnew, hRg, hkODE, hkint⟩ :=
    P.kernelForcedWeakSolution_residualODE N v hv hvp F g hv_meas V hV hvb T hT w u f hF hg hsol
  have he := P.kernelODE_uniform_mass_energy N v hv hvp
    (fun i t => RF i t - P.finiteFlux N y i t) Rg αv B lam hα hB hlam hsmall hstrain
    hd hjets y (plainInitialCoefficients N (fun _ => k) f) hkODE hycont hRFnew hRg hkint
  have hlower (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) :
      coupledPlainSynthesis N i (k) (y t) = galerkinProj N (u i t) := by
    rw [hy t ht]
    exact plainInitialCoefficients_synthesis N (fun _ => k) (fun j => u j t) i
  have hinit (i : ι) : coupledPlainSynthesis N i (k) (y a) = galerkinProj N (f i) := by
    rw [hlower a ⟨le_rfl, P.htime⟩ i, hsol.2.2.2.1 i]
  have hhigher : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ i,
      coupledPlainSynthesis N i (k + 1) (y s) = galerkinProj N (w i s) := by
    filter_upwards [ae_all_iff.mpr hsol.2.2.1, ae_restrict_mem measurableSet_Icc] with s hs hsI
    intro i
    rw [hy s hsI]
    have he : (fun j => u j s) = (fun j => truncateTorusHk (Nat.le_succ (k)) (w j s)) :=
      funext (fun j => (hs j).symm)
    rw [he]
    exact plainInitialCoefficients_higher_synthesis N (fun _ => k) (fun j => w j s) i
  have hintEq : (∫ s in Set.Icc a b, massGradNormSq ρ P.π
      (fun i => (coupledPlainSynthesis N i (k + 1) (y s)).val)) =
      ∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (galerkinProj N (w i s)).val) := by
    apply integral_congr_ae
    filter_upwards [hhigher] with s hs
    simp only [hs]
  refine ⟨y, hycont, hy, ?_⟩
  intro t ht
  have he := he t ht
  simp only [hlower t ht, hinit, hintEq] at he
  exact he

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_component_deriv_perturbed_le
    (i : ι) (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (M ε : ℝ) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b,
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) ≤ M)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv (fun s => factorialNormSq ρ (coupledPlainSynthesis N i k (y s)).val) t +
        (3 * ν / 2 - ε) * gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) (y t)).val ≤
      2 * |P.carrierPair (fun j r => coupledPlainSynthesis N j (k + 1) (y r)) i t| +
        2 * P.π i * M * Real.sqrt (massNormSq ρ P.π (fun j => (g j t).val)) +
        (P.π i / ε) * massNormSq ρ P.π (fun j => (F j t).val) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hy.ae_hasDerivAt P.htime hint] with t ht
  intro hmem
  rw [(plainSynthesis_factorial_hasDerivAt N i k ρ (ht hmem)).deriv]
  have hpoint := P.kernelRhs_component_perturbed_le N v t hmem (hv t hmem) (hvp t hmem)
    (y t) (fun j => F j t) (fun j => g j t) αv B lam hα hB hlam
    hsmall hstrain (hd t hmem) (hjets t hmem) M ε hε (hM t hmem) i
  have hp : P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) (y t)) i t =
      P.carrierPair (fun j r => coupledPlainSynthesis N j (k + 1) (y r)) i t :=
    P.carrierPair_congr_time _ _ i t (fun _ => rfl)
  rw [hp] at hpoint
  dsimp only [AVenhance.Infra.ODE.linearRhs]
  convert mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2) using 1
  · ring
  · field_simp

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_residualPerturbedEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (M ε : ℝ) (hM0 : 0 ≤ M) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (u i t).val)) ≤ M)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f F g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∃ y : ℝ → CoupledPlainCoefficients (h := h) N,
      Continuous y ∧ (∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun i => u i t)) ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
        massNormSq ρ P.π (fun i => (galerkinProj N (u i t)).val) +
          (5 * ν / 4 - ε) * (∫ r in Set.Ioc s t, massGradNormSq ρ P.π
            (fun i => (galerkinProj N (w i r)).val)) ≤
        massNormSq ρ P.π (fun i => (galerkinProj N (u i s)).val) +
          2 * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (Rg i r).val))) +
          (1 / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π
            (fun i => (RF i r - P.finiteFlux N y i r).val)) := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let RF := fun i t => F i t + P.diffusionResidual z i t
  let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
  obtain ⟨y, hycont, hy, hRFnew, hRg, hkODE, hkint⟩ :=
    P.kernelForcedWeakSolution_residualODE N v hv hvp F g hv_meas V hV hvb T hT w u f hF hg hsol
  have hMy (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) ≤ M := by
    rw [hy t ht]
    exact (Real.sqrt_le_sqrt (plainInitialCoefficients_mass_le N (fun _ => k) ρ P.π P.hπ
      (fun i => u i t))).trans (hM t ht)
  have he := P.kernelODE_mass_perturbed_interval_le N v hv hvp
    (fun i t => RF i t - P.finiteFlux N y i t) Rg αv B lam hα hB hlam hsmall hstrain
    hd hjets y (plainInitialCoefficients N (fun _ => k) f) hkODE hycont M ε hM0 hε hMy hRFnew hRg hkint
  have hlower (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) :
      coupledPlainSynthesis N i (k) (y t) = galerkinProj N (u i t) := by
    rw [hy t ht]
    exact plainInitialCoefficients_synthesis N (fun _ => k) (fun j => u j t) i
  have hhigher : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ i,
      coupledPlainSynthesis N i (k + 1) (y s) = galerkinProj N (w i s) := by
    filter_upwards [ae_all_iff.mpr hsol.2.2.1, ae_restrict_mem measurableSet_Icc] with s hs hsI
    intro i
    rw [hy s hsI]
    have he : (fun j => u j s) = (fun j => truncateTorusHk (Nat.le_succ (k)) (w j s)) :=
      funext (fun j => (hs j).symm)
    rw [he]
    exact plainInitialCoefficients_higher_synthesis N (fun _ => k) (fun j => w j s) i
  refine ⟨y, hycont, hy, ?_⟩
  intro s hs t ht hst
  have hsub : Set.Ioc s t ⊆ Set.Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hintEq : (∫ r in Set.Ioc s t, massGradNormSq ρ P.π
      (fun i => (coupledPlainSynthesis N i (k + 1) (y r)).val)) =
      ∫ r in Set.Ioc s t, massGradNormSq ρ P.π (fun i => (galerkinProj N (w i r)).val) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hhigher] with r hr
    simp only [hr]
  have he := he s hs t ht hst
  simp only [hlower t ht, hlower s hs, hintEq] at he
  exact he

end TorusKernelOperator
end

/-! Time closure with the exact parenthesized forcing constants. -/

section
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
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))


include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_component_perturbed_interval_le
    (i : ι) (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y) (M ε : ℝ) (hM0 : 0 ≤ M) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b,
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) ≤ M)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      factorialNormSq ρ (coupledPlainSynthesis N i k (y t)).val +
        (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t,
          gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) (y r)).val) ≤
      factorialNormSq ρ (coupledPlainSynthesis N i k (y s)).val +
        2 * (∫ r in Set.Icc a b,
          |P.carrierPair (fun j τ => coupledPlainSynthesis N j (k + 1) (y τ)) i r|) +
        2 * P.π i * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun j => (g j r).val))) +
        (P.π i / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun j => (F j r).val)) := by
  have hac := plainSynthesis_factorial_absolutelyContinuous N i k ρ
    (hy.absolutelyContinuousOnInterval P.htime hint)
  have hc := ((torusFactorialGradientReadout (E := h i) ρ k).continuous.comp
    (coupledPlainSynthesis_continuous N i (k + 1) hycont)).norm.pow 2
  change Continuous (fun r => ‖torusFactorialGradientReadout (E := h i) ρ k
    (coupledPlainSynthesis N i (k + 1) (y r))‖ ^ 2) at hc
  simp only [torusFactorialGradientReadout_normSq] at hc
  have hr := hc.intervalIntegrable (μ := volume) a b
  let W := fun j r => coupledPlainSynthesis N j (k + 1) (y r)
  have hW (j : ι) : MemLp (W j) 2 (volume.restrict (Set.Icc a b)) :=
    coupledPlainSynthesis_memLp N j (k + 1) a b hycont
  have hCp := (P.carrierPair_integrable W hW i).abs
  have hf := massNormSq_integrable ρ P.π P.hπ (fun i => torusJet_memLp k (hF i))
  have hg' := massNorm_integrable ρ P.π P.hπ
    (fun i => torusJet_memLp k (memLp_one_iff_integrable.mpr (hg i)))
  let H := fun r => 2 * |P.carrierPair W i r| + 2 * P.π i * M * Real.sqrt (massNormSq ρ P.π (fun i => (g i r).val)) +
    (P.π i / ε) * massNormSq ρ P.π (fun i => (F i r).val)
  have hH : Integrable H (volume.restrict (Set.Icc a b)) :=
    ((hCp.const_mul 2).add (hg'.const_mul (2 * P.π i * M))).add (hf.const_mul (P.π i / ε))
  have hd := P.kernelODE_component_deriv_perturbed_le N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets i y initial hy M ε hε hM hint
  intro s hs t ht hst
  have hpos : ∀ r, 0 ≤ H r := fun r =>
      add_nonneg (add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (P.hπ i).le) hM0) (Real.sqrt_nonneg _)))
        (mul_nonneg (div_nonneg (P.hπ i).le hε.le) (massNormSq_nonneg ρ P.π P.hπ _))
  have he := perturbedTimeEnergyGlobal P.htime hs ht hst hac hr hH hpos hd
  have heq : (∫ r in Set.Icc a b, H r) =
      2 * (∫ r in Set.Icc a b, |P.carrierPair W i r|) +
      2 * P.π i * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun j => (g j r).val))) +
      (P.π i / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun j => (F j r).val)) := by
    have hfirst := integral_add ((hCp.const_mul 2).add (hg'.const_mul (2 * P.π i * M)))
      (hf.const_mul (P.π i / ε))
    have hsecond := integral_add (hCp.const_mul 2) (hg'.const_mul (2 * P.π i * M))
    simp only [Pi.add_apply] at hfirst hsecond
    dsimp only [H]
    rw [hfirst, hsecond]
    simp only [integral_const_mul]
  rw [heq] at he
  simpa only [add_assoc] using he

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_projectedEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f (fun i t => F i t + P.carrierFlux w i t) g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.carrierFlux z i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (galerkinProj N (u i t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (galerkinProj N (w i s)).val)) ≤
      2 * massNormSq ρ P.π (fun i => (galerkinProj N (f i)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (RF i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (Rg i s).val))) ^ 2 := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let Ftotal := fun i t => F i t + P.carrierFlux w i t
  have hFt (i : ι) : MemLp (Ftotal i) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add _ 2 (F i) (P.carrierFlux w i) (hF i)
      (P.carrierFlux_memLp_of_family w hsol.2.1 i)
  obtain ⟨y, _, hy, he⟩ := P.kernelForcedWeakSolution_residualEnergy N v hv hvp Ftotal g
    αv B lam hα hB hlam hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hFt hg hsol
  have hflux (i : ι) := P.finiteFlux_eq_projectedCarrierFlux_ae N y u w hy hsol.2.2.1 i
  have hintEq :
      (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => ((F i s + P.carrierFlux w i s) +
          P.diffusionResidual z i s - P.finiteFlux N y i s).val)) =
      (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => (F i s + P.carrierFlux z i s +
          P.diffusionResidual z i s).val)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hflux] with s hs
    apply congrArg (massNormSq ρ P.π)
    funext i
    rw [hs i, P.carrierFlux_sub w (fun j t => galerkinProj N (w j t)) i s]
    congr 1
    abel
  intro t ht
  have h := he t ht
  dsimp only [Ftotal] at h
  rw [hintEq] at h
  exact h

end TorusKernelOperator
end

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

section
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
theorem kernelResidualFlux_mass_limit
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    let z := fun N i t => w i t - galerkinProj N (w i t)
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b, massNormSq ρ P.π
      (fun i => (F i t + P.carrierFlux (z N) i t + P.diffusionResidual (z N) i t).val))
      Filter.atTop (nhds (∫ t in Set.Icc a b, massNormSq ρ P.π (fun i => (F i t).val))) := by
  dsimp only
  let z := fun N i t => w i t - galerkinProj N (w i t)
  have hz (N : ℕ) (i : ι) : MemLp (z N i) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub _ 2 _ _ (hw i) ((galerkinProj N).comp_memLp' (hw i))
  let Q := fun N => P.carrierFlux (z N)
  let R := fun N => P.diffusionResidual (z N)
  have hQ (N : ℕ) (i : ι) : MemLp (Q N i) 2 (volume.restrict (Set.Icc a b)) :=
    P.carrierFlux_memLp_of_family _ (hz N) i
  have hR (N : ℕ) (i : ι) : MemLp (R N i) 2 (volume.restrict (Set.Icc a b)) :=
    torusSpatialFluxPath_memLp (fun _ => k) 0 a b ν ρ P.radius_pos noLocalCoefficient
      noLocalSeminorm noLocalSmoothOnInterval noLocalPeriodicOnInterval P.htime
      noLocalMeasurable (z N) (hz N) i
  have hlR (i : ι) : Filter.Tendsto (fun N => ∫ t in Set.Icc a b, ‖R N i t‖ ^ 2)
      Filter.atTop (nhds 0) :=
    torusSpatialFluxPath_tail_square_tendsto (fun _ => k) 0 a b ν ρ P.radius_pos
      noLocalCoefficient noLocalSeminorm noLocalSmoothOnInterval noLocalPeriodicOnInterval
      P.htime noLocalMeasurable w hw i
  have hl := torusMassNormSq_perturbed_integral_tendsto (volume.restrict (Set.Icc a b))
    (fun _ => k) ρ P.π F hF (fun N i t => Q N i t + R N i t)
    (fun N i => timeMemLp_pointwise_add _ 2 _ _ (hQ N i) (hR N i))
    (fun i => timeL2_residual_add_square_tendsto _ (fun N => Q N i) (fun N => R N i)
      (fun N => hQ N i) (fun N => hR N i) (P.carrierFlux_tail_square_tendsto w hw i) (hlR i))
  simpa only [Q, R, add_assoc] using! hl

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_projectedPerturbedEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (M ε : ℝ) (hM0 : 0 ≤ M) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (u i t).val)) ≤ M)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f (fun i t => F i t + P.carrierFlux w i t) g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.carrierFlux z i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      massNormSq ρ P.π (fun i => (galerkinProj N (u i t)).val) +
        (5 * ν / 4 - ε) * (∫ r in Set.Ioc s t, massGradNormSq ρ P.π (fun i => (galerkinProj N (w i r)).val)) ≤
      massNormSq ρ P.π (fun i => (galerkinProj N (u i s)).val) +
        2 * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (Rg i r).val))) +
        (1 / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun i => (RF i r).val)) := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let Ftotal := fun i t => F i t + P.carrierFlux w i t
  have hFt (i : ι) : MemLp (Ftotal i) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add _ 2 (F i) (P.carrierFlux w i) (hF i)
      (P.carrierFlux_memLp_of_family w hsol.2.1 i)
  obtain ⟨y, _, hy, he⟩ := P.kernelForcedWeakSolution_residualPerturbedEnergy N v hv hvp Ftotal g
    αv B lam hα hB hlam hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hFt hg M ε hM0 hε hM hsol
  have hflux (i : ι) := P.finiteFlux_eq_projectedCarrierFlux_ae N y u w hy hsol.2.2.1 i
  have hintEq :
      (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => ((F i s + P.carrierFlux w i s) +
          P.diffusionResidual z i s - P.finiteFlux N y i s).val)) =
      (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => (F i s + P.carrierFlux z i s +
          P.diffusionResidual z i s).val)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hflux] with s hs
    apply congrArg (massNormSq ρ P.π)
    funext i
    rw [hs i, P.carrierFlux_sub w (fun j t => galerkinProj N (w j t)) i s]
    congr 1
    abel
  intro r hr t ht hrt
  have h := he r hr t ht hrt
  dsimp only [Ftotal] at h
  rw [hintEq] at h
  exact h

end TorusKernelOperator
end

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

section
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
theorem kernelWeakSolution_forcedWeakSolution
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u w y) :
    IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w := by
  refine ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1, ?_⟩
  intro i t ht φ
  have hs : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hf : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      P.inputRawFlux y i r x + (F i r).toFunction.jet (valueIndex2 k) x =
      torusRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i x +
        (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k) x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs
      (P.inputRawFlux_eq_kernelRawFlux_ae w y hsol.2.2.2.2.2.1 i),
      ae_restrict_mem measurableSet_Ioc] with r hr hrI
    rw [hr]
    filter_upwards [P.totalCarrierFlux_raw_ae w F i r (hs hrI)] with x hx
    exact hx.symm
  have hp : ∀ r ∈ Set.Ioc a t,
      Integrable (torusRawSpatialRhs (fun _ => k) 0 ν r v noLocalCoefficient
        (fun j s => F j s + P.carrierFlux w j s) g (fun j => w j r) i φ)
        (volume.restrict AVenhance.unitCube) := by
    intro r hr
    exact (torusRawSpatialRhs_integrable_and_integral (fun _ => k) 0 ν ρ P.radius_pos
      a b r (hs hr) v (hv r (hs hr)).continuous V hV (hvb r (hs hr))
      noLocalCoefficient (noLocalSeminorm (h := h) (k := k) (ρ := ρ) (a := a) (b := b))
      (fun j j' d => (noLocalSmoothOnInterval (h := h) (k := k) r (hs hr) j j' d).continuous)
      (fun j s => F j s + P.carrierFlux w j s) g (fun j => w j r) i φ).1
  exact weakIdentity_flux_congr_time (volume.restrict AVenhance.unitCube) ν a t v
    ((u i t).toFunction.jet (valueIndex2 k)) ((f i).toFunction.jet (valueIndex2 k))
    (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (P.inputRawFlux y i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => torusRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i)
    (fun r => (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k)) hf hp (hsol.2.2.2.2.2.2 i t ht φ)

end TorusKernelOperator
end

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

section
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
theorem kernelWeakSolution_restart
    (v : ℝ → Vec 2 → Vec 2) (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u w y)
    (s : ℝ) (hs : s ∈ Set.Icc a b) :
    IsKernelWeakSolutionTorus ν s b v k D P.B P.C P.S (fun i => u i s) F g u w y := by
  have hsub : Set.Icc s b ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 le_rfl
  have hμ : volume.restrict (Set.Icc s b) ≤ volume.restrict (Set.Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨(fun i => (hsol.1 i).mono hsub), (fun i => (hsol.2.1 i).mono_measure hμ),
    (fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i)),
    (fun _ => rfl), (fun i j α => (hsol.2.2.2.2.1 i j α).mono_measure hμ),
    (fun i j α => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.2.2.2.1 i j α)), ?_⟩
  intro i t ht φ
  exact weakIdentity_restart (volume.restrict AVenhance.unitCube) ν a s t hs.1 ht.1 v
    ((u i t).toFunction.jet (valueIndex2 k)) ((u i s).toFunction.jet (valueIndex2 k))
    ((f i).toFunction.jet (valueIndex2 k)) (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (P.inputRawFlux y i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k))
    (hsol.2.2.2.2.2.2 i t (hsub ht) φ) (hsol.2.2.2.2.2.2 i s hs φ)

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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
theorem kernelForcedWeakSolution_energy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (u i t).val) +
        (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s).val)) ≤
      2 * massNormSq ρ P.π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 := by
  have hflux := P.kernelResidualFlux_mass_limit F hF w hsol.2.1
  have hvalue := plainResidualValue_mass_limit (fun _ => k) ρ P.radius_pos a b P.htime
    v hv_meas hv hvp V hV hvb T hT g w hsol.2.1 hg P.π P.hπ
  have hgrad := galerkinProj_massGradNormSq_integral_tendsto (fun _ => k) a b ρ P.π w hsol.2.1
  have hinitial := galerkinProj_massNormSq_tendsto (fun _ => k) ρ P.π P.hπ f
  intro t ht
  have htime := galerkinProj_massNormSq_tendsto (fun _ => k) ρ P.π P.hπ (fun i => u i t)
  have hleft := htime.add (hgrad.const_mul (ν / 2))
  have hright := ((hinitial.const_mul 2).add (hflux.const_mul (8 / ν))).add ((hvalue.pow 2).const_mul 10)
  exact le_of_tendsto_of_tendsto' hleft hright (fun N =>
    P.kernelForcedWeakSolution_projectedEnergy N v hv hvp F g αv B lam hα hB hlam
      hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF hg hsol t ht)

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Hilbert weak compactness and closed Sobolev graph readout. -/

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
theorem kernelFourier_exists_strongTrace
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (U : CoupledHighTime (h := h) (fun _ => k) a b) (u : ∀ i, ℝ → TorusHk (k) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout (fun _ => k) i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout (fun _ => k) i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          P.kernelIntegratedRhs t v F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (k)) (coupledHighGraphReadout (fun _ => k) i (U t))) ∧
      (∀ i, ContinuousOn (u i) (Set.Icc a b)) := by
  obtain ⟨U, u, hmem, hgraph, hi, hbound, hid, hcont, hlowmem, halign⟩ :=
    P.kernelFourier_exists_weakTrace v hv hvp F g αv B lam hα hB hlam hsmall hstrain hd hjets
      hv_bdd hv_meas f hF hg
  obtain ⟨R, hR⟩ := hbound
  refine ⟨U, u, hmem, hgraph, hi, ⟨R, hR⟩, hid, hcont, hlowmem, halign, ?_⟩
  obtain ⟨V, hV⟩ := hv_bdd
  exact P.kernelNativeTrace_continuousOn v hv_meas hv hvp (max V 0) (le_max_right _ _)
    (fun t ht x => (hV t ht x).trans (le_max_left _ _)) αv B lam
    (fun t ht _i l hl hk x => hjets t ht l hl hk x)
    F g hF hg U hgraph u f hid hcont R hR halign

end TorusKernelOperator

end AVRegularity.KernelEnergy
end
