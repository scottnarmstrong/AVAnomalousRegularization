-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
public import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Finite weak test contraction of the actual flux and value forcing. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Literal source pairing with a synthesized finite test. -/
def plainForcingTestIntegrand (N : ℕ) (z : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) (x : Vec 2) : ℝ :=
  ∑ i, (inner ℝ (g i x) (coupledPlainRawJet N z i 0 Fin.elim0 x) -
    ∑ k : Fin 2, inner ℝ (F i x k) (coupledPlainRawJet N z i 1 (fun _ => k) x))

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Every original forcing Fourier row is spatially integrable. -/
theorem plainFourierForcingIntegrand_integrable (N : ℕ)
    (F : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (h i))
    (r : CoupledFourierModeIndex (h := h) N) :
    Integrable (fun x => ∑ i, (inner ℝ (g i x) (coupledModeJet N r i 0 Fin.elim0 x) -
      ∑ k : Fin 2, inner ℝ (F i x k) (coupledModeJet N r i 1 (fun _ => k) x)))
      (volume.restrict AVenhance.unitCube) := by
  apply integrable_finsetSum
  intro i _
  exact (plainValuePairing_integrable N r i (g i)).sub
    (integrable_finsetSum Finset.univ (fun k _ => plainFluxPairing_integrable N r i (F i) k))

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The finite source dot product is the literal weak source pairing. -/
theorem plainForcingTest_integral_contraction (N : ℕ)
    (z : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) :
    (∑ r, z r * plainFourierForcing N (fun i => F i) (fun i => g i) r) =
      ∫ x in AVenhance.unitCube, plainForcingTestIntegrand N z F g x := by
  unfold plainFourierForcing
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun r _ =>
    (plainFourierForcingIntegrand_integrable N F g r).const_mul (z r))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [plainForcingTestIntegrand, Finset.sum_sub_distrib, mul_sub]
  rw [plainTestJet_inner_sum, plainTestGradient_inner_sum]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The fixed higher-order spacetime readout after solving the plain finite ODE. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Synthesize all higher-order component graphs into the one fixed Hilbert space. -/
def plainHigherSynthesisCLM (N : ℕ) (K : ι → ℕ) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] CoupledHighHilbert (h := h) K :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (torusHkGraph (E := h i) (K i + 1)).toSubmodule.subtypeL.comp
      (coupledPlainSynthesis N i (K i + 1))))

@[simp] theorem plainHigherSynthesisCLM_apply (N : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    plainHigherSynthesisCLM N K c i = (coupledPlainSynthesis N i (K i + 1) c).val := rfl

/-- Each finite path has a genuine higher-order Bochner L² readout. -/
theorem plainHigherSynthesis_memLp (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N} (hy : Continuous y) :
    MemLp (fun t => plainHigherSynthesisCLM N K (y t)) 2 (volume.restrict (Set.Icc a b)) := by
  let : ∀ i, Module ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i)) := fun i => inferInstance
  let : Module ℝ (CoupledHighHilbert (h := h) K) := inferInstance
  let : NormedSpace ℝ (CoupledHighHilbert (h := h) K) := inferInstance
  let : SecondCountableTopologyEither ℝ (CoupledHighHilbert (h := h) K) :=
    secondCountableTopologyEither_of_left ℝ _
  have hc := (plainHigherSynthesisCLM N K).continuous.comp hy
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable.restrict).mpr
    ((hc.norm.pow 2).integrableOn_Icc)

/-- The Bochner norm square is literally the time integral of the finite higher-order norm square. -/
theorem plainHigherSynthesis_toLp_normSq (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N} (hy : Continuous y) :
    ‖(plainHigherSynthesis_memLp N K a b hy).toLp (fun t => plainHigherSynthesisCLM N K (y t))‖ ^ 2 =
      ∫ t in Set.Icc a b, ‖plainHigherSynthesisCLM N K (y t)‖ ^ 2 := by
  let : ∀ i, InnerProductSpace ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i)) := fun i => inferInstance
  let : InnerProductSpace ℝ (CoupledHighHilbert (h := h) K) :=
    PiLp.innerProductSpace (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))
  let : InnerProductSpace ℝ (CoupledHighTime (h := h) K a b) := L2.innerProductSpace
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(plainHigherSynthesis_memLp N K a b hy).coeFn_toLp] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

/-- Pointwise coercivity of each actual synthesized higher-order component. -/
theorem plainHigherSynthesis_component_normSq_le (N : ℕ) (K : ι → ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    ‖plainHigherSynthesisCLM N K c i‖ ^ 2 ≤
      π i * massNormSq ρ π (fun j => (coupledPlainSynthesis N j (K j) c).val) +
      (π i / factorialWeightMin ρ (K i)) *
        massGradNormSq ρ π (fun j => (coupledPlainSynthesis N j (K j + 1) c).val) := by
  have hc := componentJetNormSq_le_mass ρ hρ π hπ
    (fun j => (coupledPlainSynthesis N j (K j + 1) c).val) i
  have he : (fun j => truncateJet (Nat.le_succ (K j)) (coupledPlainSynthesis N j (K j + 1) c).val) =
      (fun j => (coupledPlainSynthesis N j (K j) c).val) := by
    funext j
    exact congrArg Subtype.val (coupledPlainSynthesis_truncate N j (Nat.le_succ (K j)) c)
  rw [he] at hc
  exact hc

/-- The complete ambient higher-order norm is controlled by the actual mass energy and dissipation. -/
theorem plainHigherSynthesis_normSq_le (N : ℕ) (K : ι → ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (c : CoupledPlainCoefficients (h := h) N) :
    ‖plainHigherSynthesisCLM N K c‖ ^ 2 ≤
      (∑ i, π i) * massNormSq ρ π (fun j => (coupledPlainSynthesis N j (K j) c).val) +
      (∑ i, π i / factorialWeightMin ρ (K i)) *
        massGradNormSq ρ π (fun j => (coupledPlainSynthesis N j (K j + 1) c).val) := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    plainHigherSynthesis_component_normSq_le N K ρ hρ π hπ c i)
  simpa only [Finset.sum_add_distrib, ← Finset.sum_mul] using hs

/-- The actual fixed Hilbert spacetime element associated with one solved finite curve. -/
def plainHigherBochner (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) : CoupledHighTime (h := h) K a b :=
  (plainHigherSynthesis_memLp N K a b (AVenhance.Infra.ODE.continuous_extendCurve hab y)).toLp
    (fun t => plainHigherSynthesisCLM N K (AVenhance.Infra.ODE.extendCurve hab y t))

/-- Its norm square is exactly the actual finite higher-order spacetime integral. -/
theorem plainHigherBochner_normSq (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) :
    ‖plainHigherBochner N K a b hab y‖ ^ 2 =
      ∫ t in Set.Icc a b, ‖plainHigherSynthesisCLM N K (AVenhance.Infra.ODE.extendCurve hab y t)‖ ^ 2 :=
  plainHigherSynthesis_toLp_normSq N K a b (AVenhance.Infra.ODE.continuous_extendCurve hab y)

/-- Every finite spacetime element has genuine periodic Sobolev jets almost everywhere. -/
theorem plainHigherBochner_graph_ae (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      plainHigherBochner N K a b hab y t i ∈ torusHkGraph (E := h i) (K i + 1) := by
  filter_upwards [(plainHigherSynthesis_memLp N K a b
    (AVenhance.Infra.ODE.continuous_extendCurve hab y)).coeFn_toLp] with t ht
  intro i
  change (plainHigherSynthesis_memLp N K a b
    (AVenhance.Infra.ODE.continuous_extendCurve hab y)).toLp
    (fun s => plainHigherSynthesisCLM N K (AVenhance.Infra.ODE.extendCurve hab y s)) t i ∈ _
  rw [ht, plainHigherSynthesisCLM_apply]
  exact (coupledPlainSynthesis N i (K i + 1) (AVenhance.Infra.ODE.extendCurve hab y t)).property

end AVRegularity.CoupledEnergy.Galerkin
end
