-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.TorusBandSourceIntegrand
import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
public import AVRegularity.CoupledEnergy.Variational.FactorialPairing
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The synthesis map has identity mass coordinates and is injective. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- The value component of a bundled mode is its explicitly promoted cell class. -/
theorem coupledModeHk_value_eq_cellLp (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K : ℕ) :
    (coupledModeHk N r i K).val (valueIndex2 K) = plainModeCellLp N r i 0 Fin.elim0 := rfl

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The value mass matrix in the cell L² Hilbert spaces is exactly the identity. -/
theorem plainModeCellLp_mass_identity (N : ℕ)
    (r c : CoupledFourierModeIndex (h := h) N) :
    (∑ i, inner ℝ (plainModeCellLp N r i 0 Fin.elim0) (plainModeCellLp N c i 0 Fin.elim0)) =
      if r = c then 1 else 0 := by
  have hentry (i : ι) :
      inner ℝ (plainModeCellLp N r i 0 Fin.elim0) (plainModeCellLp N c i 0 Fin.elim0) =
        ∫ x in AVenhance.unitCube, inner ℝ (coupledModeJet N r i 0 Fin.elim0 x)
          (coupledModeJet N c i 0 Fin.elim0 x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [plainModeCellLp_ae N r i 0 Fin.elim0,
      plainModeCellLp_ae N c i 0 Fin.elim0] with x hr hc
    rw [hr, hc]
  simp_rw [hentry]
  exact plainCoupledMode_cell_orthonormal N r c

/-- Applying a value Fourier test after synthesis recovers the corresponding coefficient. -/
theorem plainSynthesis_mass_coordinate (N : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (r : CoupledFourierModeIndex (h := h) N) :
    (∑ i, plainValueForcingCLM N r i (K i) (coupledPlainSynthesis N i (K i) c)) = c r := by
  simp only [coupledPlainSynthesis_apply, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [plainValueForcingCLM, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply_apply]
  change (∑ a, ∑ i, c a * inner ℝ (plainModeCellLp N r i 0 Fin.elim0)
    ((coupledModeHk N a i (K i)).val (valueIndex2 (K i)))) = c r
  simp_rw [coupledModeHk_value_eq_cellLp, ← Finset.mul_sum, plainModeCellLp_mass_identity]
  simp

/-- The reconstructed value pairing is the ordinary finite scalar dot product. -/
theorem plainSynthesis_mass_pairing (N : ℕ) (K : ι → ℕ)
    (c d : CoupledPlainCoefficients (h := h) N) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) c))
      (torusHkValueCLM (coupledPlainSynthesis N i (K i) d))) = ∑ a, c a * d a := by
  have hfirst (i : ι) : torusHkValueCLM (coupledPlainSynthesis N i (K i) c) =
      ∑ a, c a • plainModeCellLp N a i 0 Fin.elim0 := by
    simp only [coupledPlainSynthesis_apply, map_sum, map_smul]
    rfl
  simp_rw [hfirst, sum_inner, real_inner_smul_left]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact plainSynthesis_mass_coordinate N K d a
end

/-! Literal spatial integrals of the finite weak test equation. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
variable (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
  (v : Vec 2 → Vec 2) (hv : Continuous v)
  (A : ∀ i i', (d : admissibleOrders K D i i') → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, Continuous (A i i' d))

include hv hA
/-- Every reconstructed finite spatial row is integrable. -/
theorem plainSpatialRowIntegrand_integrable (r : CoupledFourierModeIndex (h := h) N)
    (c : CoupledPlainCoefficients (h := h) N) :
    Integrable (plainSpatialRowIntegrand N D ν K v A r c)
      (volume.restrict AVenhance.unitCube) := by
  have he := funext (plainSpatialRowIntegrand_eq_sum N D ν K v A r c)
  rw [he]
  apply integrable_finsetSum
  intro a _
  exact (plainFourierIntegrand_integrable N D ν K v hv A hA r a).const_mul (c a)

/-- Contracting integrated rows equals the literal spatial integral of the full test form. -/
theorem plainSpatialTest_integral_contraction (c z : CoupledPlainCoefficients (h := h) N) :
    (∑ r, z r * ∫ x in AVenhance.unitCube, plainSpatialRowIntegrand N D ν K v A r c x) =
      ∫ x in AVenhance.unitCube, plainSpatialTestIntegrand N D ν K v A c z x := by
  calc
    _ = ∑ r, ∫ x in AVenhance.unitCube, z r * plainSpatialRowIntegrand N D ν K v A r c x := by
      apply Finset.sum_congr rfl
      intro r _
      rw [integral_const_mul]
    _ = ∫ x in AVenhance.unitCube, ∑ r, z r * plainSpatialRowIntegrand N D ν K v A r c x :=
      (integral_finsetSum Finset.univ (fun r _ =>
        (plainSpatialRowIntegrand_integrable N D ν K v hv A hA r c).const_mul (z r))).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (plainSpatialRow_test_contraction N D ν K v A c z))
end

/-! Split the genuine finite spatial weak form into its integrable native
terms before taking the spacetime weak limit. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem coupledPlainRawTensor_continuous (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (m : ℕ) : Continuous (coupledPlainRawTensor N c i m) := by
  exact (PiLp.continuous_toLp 2 (fun _ : DerivativeWord2 m => h i)).comp
    (continuous_pi (fun w => (coupledPlainRawJet_contDiff N c i m w).continuous))

/-- All scalar pieces of the finite test form are spatially integrable. -/
theorem plainSpatialTest_pieces_integrable (N D : ℕ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2) (hv : Continuous v)
    (A : ∀ i i', (d : admissibleOrders K D i i') → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Continuous (A i i' d)) (c z : CoupledPlainCoefficients (h := h) N) :
    (∀ i k, Integrable (fun x => inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
      (coupledPlainRawJet N z i 1 (fun _ => k) x)) (volume.restrict AVenhance.unitCube)) ∧
    (∀ i k, Integrable (fun x => v x k * inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
      (coupledPlainRawJet N z i 0 Fin.elim0 x)) (volume.restrict AVenhance.unitCube)) ∧
    (∀ i i' d k, Integrable (fun x => inner ℝ (A i i' d x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
      (coupledPlainRawJet N z i 1 (fun _ => k) x)) (volume.restrict AVenhance.unitCube)) := by
  have hc : ∀ i m w, Continuous (coupledPlainRawJet N c i m w) :=
    fun i m w => (coupledPlainRawJet_contDiff N c i m w).continuous
  have hz : ∀ i m w, Continuous (coupledPlainRawJet N z i m w) :=
    fun i m w => (coupledPlainRawJet_contDiff N z i m w).continuous
  have ht : ∀ i m, Continuous (coupledPlainRawTensor N c i m) :=
    coupledPlainRawTensor_continuous N c
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    apply continuous_cell_integrable
    fun_prop
  · intro i k
    apply continuous_cell_integrable
    fun_prop
  · intro i i' d k
    apply continuous_cell_integrable
    fun_prop

/-- The full finite spatial integral is the sum of the native diffusion, drift and coupling integrals. -/
theorem plainSpatialTest_integral_split (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2) (hv : Continuous v)
    (A : ∀ i i', (d : admissibleOrders K D i i') → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Continuous (A i i' d)) (c z : CoupledPlainCoefficients (h := h) N) :
    (∫ x in AVenhance.unitCube, plainSpatialTestIntegrand N D ν K v A c z x) =
      -ν * (∑ i, ∫ x in AVenhance.unitCube, ∑ k : Fin 2,
        inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
          (coupledPlainRawJet N z i 1 (fun _ => k) x)) -
      (∑ i, ∑ k : Fin 2, ∫ x in AVenhance.unitCube, v x k *
        inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
          (coupledPlainRawJet N z i 0 Fin.elim0 x)) -
      (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∫ x in AVenhance.unitCube, ∑ k : Fin 2,
        inner ℝ (A i i' d x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
          (coupledPlainRawJet N z i 1 (fun _ => k) x)) := by
  obtain ⟨hd, hvv, haa⟩ := plainSpatialTest_pieces_integrable N D K v hv A hA c z
  have hds (i : ι) := integrable_finsetSum Finset.univ (fun k _ => hd i k)
  have hvs (i : ι) := integrable_finsetSum Finset.univ (fun k _ => hvv i k)
  have has (i i' : ι) (d : admissibleOrders K D i i') :=
    integrable_finsetSum Finset.univ (fun k _ => haa i i' d k)
  have hats (i i' : ι) := integrable_finsetSum Finset.univ (fun d _ => has i i' d)
  have hai (i : ι) := integrable_finsetSum Finset.univ (fun i' _ => hats i i')
  have hdt := integrable_finsetSum Finset.univ (fun i _ => hds i)
  have hvt := integrable_finsetSum Finset.univ (fun i _ => hvs i)
  have hat := integrable_finsetSum Finset.univ (fun i _ => hai i)
  unfold plainSpatialTestIntegrand
  have hs0 := integral_add ((hdt.const_mul (-ν)).add hvt.neg) hat.neg
  have hs1 := integral_add (hdt.const_mul (-ν)) hvt.neg
  simp only [Pi.add_apply, Pi.neg_apply] at hs0 hs1
  rw [hs0, hs1, integral_const_mul, integral_neg, integral_neg]
  rw [integral_finsetSum Finset.univ (fun i _ => hds i),
    integral_finsetSum Finset.univ (fun i _ => hvs i),
    integral_finsetSum Finset.univ (fun i _ => hai i)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hvv _ k),
    integral_finsetSum Finset.univ (fun i' _ => hats _ i'),
    integral_finsetSum Finset.univ (fun d _ => has _ _ d)]
  ring
end

/-! Sum ordered jet tail estimates in the actual Hilbert graph norm. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusBand_sqNorm_le_of_jetBounds {K : ℕ} (N M : ℕ) (u : TorusHk K E) (C : ℝ)
    (hb : ∀ j : JetIndex2 K, ‖torusBandJetCLM K N M j u‖ ^ 2 ≤ C) :
    ‖galerkinProj N u - galerkinProj M u‖ ^ 2 ≤ (Fintype.card (JetIndex2 K) : ℝ) * C := by
  change ‖(galerkinProj N u - galerkinProj M u).val‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _j : JetIndex2 K, C := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp
end

/-! Value pairings allow different Sobolev orders for the trial and test jets. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The value readout of a synthesized vector is independent of its bundled order. -/
theorem plainSynthesis_value_order_independent (N : ℕ) (i : ι) (K L : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) :
    torusHkValueCLM (coupledPlainSynthesis N i K c) =
      torusHkValueCLM (coupledPlainSynthesis N i L c) := by
  simp only [coupledPlainSynthesis_apply, map_sum, map_smul]
  rfl

/-- Trial H^K jets and H¹ tests have the same coefficient mass pairing. -/
theorem plainSynthesis_mixed_mass_pairing (N : ℕ) (K L : ι → ℕ)
    (c z : CoupledPlainCoefficients (h := h) N) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) c))
      (torusHkValueCLM (coupledPlainSynthesis N i (L i) z))) = ∑ r, c r * z r := by
  rw [← plainSynthesis_mass_pairing N K c z]
  apply Finset.sum_congr rfl
  intro i _
  rw [plainSynthesis_value_order_independent N i (L i) (K i) z]
end

/-! Literal cell integrals for the entire finite forcing vector. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Raw value-mode pairings are integrable for every spatial L² value. -/
theorem plainValuePairing_integrable (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (u : ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) :
    Integrable (fun x => inner ℝ (u x) (coupledModeJet N r i 0 Fin.elim0 x))
      (volume.restrict AVenhance.unitCube) := by
  apply (L2.integrable_inner (𝕜 := ℝ) u (plainModeCellLp N r i 0 Fin.elim0)).congr
  filter_upwards [plainModeCellLp_ae N r i 0 Fin.elim0] with x hx
  rw [hx]

omit [Fintype ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Raw flux-mode pairings are integrable, using each actual flux coordinate. -/
theorem plainFluxPairing_integrable (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (F : ComponentL2 (volume.restrict AVenhance.unitCube)
      (PiLp 2 (fun _ : Fin 2 => h i))) (k : Fin 2) :
    Integrable (fun x => inner ℝ (F x k) (coupledModeJet N r i 1 (fun _ => k) x))
      (volume.restrict AVenhance.unitCube) := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k
  apply (L2.integrable_inner (𝕜 := ℝ) (P.compLpL 2 _ F)
    (plainModeCellLp N r i 1 (fun _ => k))).congr
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (L := P) F,
    plainModeCellLp_ae N r i 1 (fun _ => k)] with x hx hm
  rw [hx, hm]
  rfl

omit [Fintype ι] in
/-- The flux observable is the literal integral of the raw flux against the mode gradient. -/
theorem plainFluxForcingCLM_eq_integral (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K₀ : ℕ) (F : TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h i))) :
    plainFluxForcingCLM N r i K₀ F = ∫ x in AVenhance.unitCube,
      ∑ k : Fin 2, inner ℝ ((torusHkValueCLM F) x k)
        (coupledModeJet N r i 1 (fun _ => k) x) := by
  rw [plainFluxForcingCLM_eq_integrals, integral_finsetSum Finset.univ
    (fun k _ => plainFluxPairing_integrable N r i (torusHkValueCLM F) k)]
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (torusHkValueCLM F)] with x hx
  rw [hx]
  rfl

/-- The full forcing vector agrees with the scalar Fourier-coefficient integral. -/
theorem plainSourceCoefficients_eq_fourierForcing (N : ℕ) (K : ι → ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) (r : CoupledFourierModeIndex (h := h) N) :
    plainSourceCoefficients N K F g r = plainFourierForcing N
      (fun i => torusHkValueCLM (F i)) (fun i => torusHkValueCLM (g i)) r := by
  unfold plainSourceCoefficients plainFourierForcing
  have hsum := integral_finsetSum Finset.univ (fun i _ =>
    (plainValuePairing_integrable N r i (torusHkValueCLM (g i))).sub
      (integrable_finsetSum Finset.univ (fun k _ =>
        plainFluxPairing_integrable N r i (torusHkValueCLM (F i)) k)))
  simp only [Pi.sub_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [plainValueForcingCLM_eq_integral, plainFluxForcingCLM_eq_integral,
    integral_sub (plainValuePairing_integrable N r i (torusHkValueCLM (g i)))
      (integrable_finsetSum Finset.univ (fun k _ =>
        plainFluxPairing_integrable N r i (torusHkValueCLM (F i)) k))]
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Time differentiation of the exact factorial mass energy after finite synthesis. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The finite factorial energy has precisely the native carrier pairing as its derivative. -/
theorem plainSynthesis_factorial_hasDerivAt (N : ℕ) (i : ι) (K : ℕ) (ρ : ℝ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N}
    {q : CoupledPlainCoefficients (h := h) N} {t : ℝ} (hy : HasDerivAt y q t) :
    HasDerivAt (fun s => factorialNormSq ρ (coupledPlainSynthesis N i K (y s)).val)
      (2 * inner ℝ (factorialWeightedJet ρ (coupledPlainSynthesis N i K q).val)
        (factorialWeightedJet ρ (coupledPlainSynthesis N i K (y t)).val)) t := by
  have hj (j : Fin (K + 1)) (w : DerivativeWord2 j.val) :=
    plainSynthesis_energy_hasDerivAt (plainJetSynthesisCLM N i K ⟨j, w⟩) hy
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) (fun w _ => hj j w)).const_mul
      (factorialWeight ρ j.val))
  convert hs using 1
  · rfl
  · rw [factorialWeightedJet_inner]
    simp only [plainJetSynthesisCLM_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro w _
    rw [real_inner_comm]
    ring

/-- Component masses only form a finite weighted sum in the chain rule. -/
theorem plainSynthesis_mass_hasDerivAt (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N}
    {q : CoupledPlainCoefficients (h := h) N} {t : ℝ} (hy : HasDerivAt y q t) :
    HasDerivAt (fun s => massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y s)).val))
      (2 * ∑ i, (π i)⁻¹ * inner ℝ
        (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) q).val)
        (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) (y t)).val)) t := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (plainSynthesis_factorial_hasDerivAt N i (K i) ρ hy).const_mul ((π i)⁻¹))
  convert hs using 1
  · rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Finite scalar sums preserve absolute continuity, without a carrier instance search. -/
theorem plainFiniteSum_absolutelyContinuous {J : Type*} (s : Finset J)
    {a b : ℝ} (f : J → ℝ → ℝ)
    (hf : ∀ j ∈ s, AbsolutelyContinuousOnInterval (f j) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ j ∈ s, f j t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj, Pi.add_apply] using!
      (hf j (Finset.mem_insert_self j s)).add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
end

/-! The band energy chain rule gives a uniform squared-jet tail estimate
with the explicit vanishing source budget. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusBandJet_sqNorm_le_tailBudget {K : ℕ} (N M : ℕ) {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) {j : ℕ} (hj : j ≤ K) (word : DerivativeWord2 j)
    (R : ℝ) (f : TorusHk K E) (H u : ℝ → TorusHk K E)
    (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E))) (w : ℝ → TorusHk (K + 1) E)
    (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Icc a b)))
    (hub : ∀ r ∈ Set.Icc a b, ‖u r‖ ≤ R)
    (henergy : ‖torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ (u t)‖ ^ 2 -
      ‖torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ f‖ ^ 2 =
      ∫ r in a..t, torusBandSourceIntegrand N M hj word H u S w r) :
    ‖torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ (u t)‖ ^ 2 ≤
      torusSourceTailBudget N a b R f H S w + torusSourceTailBudget M a b R f H S w := by
  have hmN := torusSourceTailMajorant_integrable N a b R H S w hH hS hw
  have hmM := torusSourceTailMajorant_integrable M a b R H S w hH hS hw
  have hqm := torusBandSourceIntegrand_aestronglyMeasurable N M hj word a b H u S w
    hH.aestronglyMeasurable hu hS.aestronglyMeasurable hw.aestronglyMeasurable
  have hb : ∀ᵐ r ∂volume.restrict (Set.Icc a b),
      |torusBandSourceIntegrand N M hj word H u S w r| ≤
        torusSourceTailMajorant N R H S w r + torusSourceTailMajorant M R H S w r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact torusBandSourceIntegrand_abs_le N M hj word R H u S w r (hub r hr)
  have hbound := intervalIntegral_le_full_majorant ht
    (torusBandSourceIntegrand N M hj word H u S w)
    (fun r => torusSourceTailMajorant N R H S w r + torusSourceTailMajorant M R H S w r)
    hqm (hmN.add hmM) hb
  rw [integral_add hmN hmM, ← henergy] at hbound
  have hinit : ‖torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ f‖ ^ 2 ≤
      2 * ‖galerkinProj N f - f‖ ^ 2 + 2 * ‖galerkinProj M f - f‖ ^ 2 := by
    have he := galerkinBand_jet_norm_le_tails N M f ⟨⟨j, by omega⟩, word⟩
    rw [← torusBandJetCLM_apply] at he
    nlinarith [norm_nonneg (torusBandJetCLM K N M ⟨⟨j, by omega⟩, word⟩ f),
      norm_nonneg (galerkinProj N f - f), norm_nonneg (galerkinProj M f - f),
      sq_nonneg (‖galerkinProj N f - f‖ - ‖galerkinProj M f - f‖)]
  unfold torusSourceTailBudget
  linarith
end

/-! The lower-order ambient synthesis used for pointwise closed-time weak traces. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The plain finite vector maps into the fixed lower-order ambient jet Hilbert space. -/
def plainLowerSynthesisCLM (N : ℕ) (K : ι → ℕ) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] CoupledLowHilbert (h := h) K :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (torusHkGraph (E := h i) (K i)).toSubmodule.subtypeL.comp
      (coupledPlainSynthesis N i (K i))))

@[simp] theorem plainLowerSynthesisCLM_apply (N : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    plainLowerSynthesisCLM N K c i = (coupledPlainSynthesis N i (K i) c).val := rfl

/-- Actual finite mass energy controls the lower-order ambient jet norm. -/
theorem plainLowerSynthesis_normSq_le_mass (N : ℕ) (K : ι → ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (c : CoupledPlainCoefficients (h := h) N) :
    ‖plainLowerSynthesisCLM N K c‖ ^ 2 ≤
      (∑ i, π i / factorialWeightMin ρ (K i)) *
        massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) c).val) :=
  coupledLowHilbert_normSq_le_mass K ρ hρ π hπ (plainLowerSynthesisCLM N K c)
end

end AVRegularity.CoupledEnergy.Galerkin
end
