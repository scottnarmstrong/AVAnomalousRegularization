-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.PlainComponentTest
public import AVRegularity.CoupledEnergy.Galerkin.PlainFamilyMeasurableFromRows
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Genuine temporal measurability of the weak Sobolev traces follows from
their continuous finite Pi-coefficient cutoffs and strong spatial Fourier
convergence. Uniform lower bounds then give actual time L² membership. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Scalar H¹-observable continuity gives genuine strongly measurable Sobolev traces. -/
theorem plainTrace_aestronglyMeasurable (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (hu : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) (i : ι) :
    AEStronglyMeasurable (u i) (volume.restrict (Set.Icc a b)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (plainTrace_galerkinProj_continuousOn N K a b u hu i).aestronglyMeasurable measurableSet_Icc)
  exact Filter.Eventually.of_forall (fun t => galerkinProj_tendsto (u i t))

/-- Uniformly bounded genuine weak Sobolev traces belong to time L². -/
theorem plainTrace_memLp (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (hu : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b))
    (R : ℝ) (hb : ∀ i, ∀ t ∈ Set.Icc a b, ‖u i t‖ ≤ R) (i : ι) :
    MemLp (u i) 2 (volume.restrict (Set.Icc a b)) := by
  apply MemLp.of_bound (plainTrace_aestronglyMeasurable K a b u hu i) R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hb i t ht

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Scalar value tests determine genuine periodic Sobolev measurability,
by the already proved finite Fourier synthesis argument. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {T : Type*} [MeasurableSpace T]

theorem torusCarrier_aestronglyMeasurable_of_integrable_tests (μ : Measure T) (K : ℕ)
    (u : T → TorusHk K E)
    (htest : ∀ φ : TorusHk 1 E,
      Integrable (fun t => inner ℝ (torusHkValueCLM (u t)) (torusHkValueCLM φ)) μ) :
    AEStronglyMeasurable u μ := by
  let orders : Unit → ℕ := fun _ => K
  let family : ∀ _ : Unit, T → TorusHk K E := fun _ => u
  apply plainFamily_aestronglyMeasurable_of_integrable_rows μ orders family _ ()
  intro N r
  have hi := htest (coupledModeHk (h := fun _ : Unit => E) N r r.1 1)
  simpa only [plainInitialCoefficients_mode_pairing, orders, family] using hi
end

/-! The higher synthesis of coefficients of a truncated genuine carrier
is exactly its higher Fourier projection. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainInitialCoefficients_higher_synthesis (N : ℕ) (K : ι → ℕ)
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) :
    coupledPlainSynthesis N i (K i + 1)
      (plainInitialCoefficients N K (fun j => truncateTorusHk (Nat.le_succ (K j)) (w j))) =
      galerkinProj N (w i) := by
  apply TorusHk.ext_value
  rw [coupledPlainSynthesis_value_order_independent N i (K i + 1) (K i),
    plainInitialCoefficients_synthesis]
  change torusHkValueCLM (galerkinProj N (truncateTorusHk (Nat.le_succ (K i)) (w i))) =
    torusHkValueCLM (galerkinProj N (w i))
  rw [torusHkValue_galerkinProj, torusHkValue_galerkinProj]
  rfl
end

/-! Reconstruct the finite source as the actual Fourier cutoff of the value
forcing plus the divergence of a smooth cutoff of the weak flux. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Initial Fourier coefficients synthesize the same smooth cutoff at every target order. -/
theorem plainInitialCoefficients_synthesis_smoothLift (N : ℕ) (K : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (i : ι) (L : ℕ) :
    coupledPlainSynthesis N i L (plainInitialCoefficients N K f) =
      smoothFourierLift (K := K i) (L := L) N (f i) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (coupledPlainSynthesis N i L (plainInitialCoefficients N K f)) =
    torusHkValueCLM (smoothFourierLift (K := K i) (L := L) N (f i))
  rw [smoothFourierLift_value_projection]
  change (coupledPlainSynthesis N i L (plainInitialCoefficients N K f)).val (valueIndex2 L) = _
  rw [coupledPlainSynthesis_value_order_independent N i L (K i)]
  rw [plainInitialCoefficients_synthesis]
  rfl
end

/-! Finite derivative coordinates are skew-adjoint in the explicit scalar mass pairing. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Scalar dot products of derivative coordinates are literal smooth spatial pairings. -/
theorem plainDerivativeCoefficients_dot_eq_integrals (N : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (c d : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainDerivativeCoefficients N 0 w c a * d a) =
      ∑ i, ∫ x in AVenhance.unitCube, inner ℝ (coupledPlainRawJet N c i r w x)
        (coupledPlainRawJet N d i 0 Fin.elim0 x) := by
  rw [← plainSynthesis_mass_pairing N (fun _ => 0) (plainDerivativeCoefficients N 0 w c) d]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [plainDerivativeCoefficients_value_ae N 0 w c i,
    coupledPlainSynthesis_jet_ae N i 0 d (valueIndex2 0)] with x hx hd
  change inner ℝ (((coupledPlainSynthesis N i 0 (plainDerivativeCoefficients N 0 w c)).val
    (valueIndex2 0)) x) (((coupledPlainSynthesis N i 0 d).val (valueIndex2 0)) x) = _
  rw [hx, hd]
  rfl

/-- Directional differentiation is skew-adjoint for the actual finite Fourier coefficients. -/
theorem plainDerivativeCoefficients_direction_skew (N : ℕ) (k : Fin 2)
    (c d : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) c a * d a) =
      -∑ a, c a * plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) d a := by
  have hcomm : (∑ a, c a * plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) d a) =
      ∑ a, plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) d a * c a :=
    Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  rw [hcomm, plainDerivativeCoefficients_dot_eq_integrals,
    plainDerivativeCoefficients_dot_eq_integrals, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ 1 (coupledPlainRawJet N c i 0 Fin.elim0) :=
    (coupledPlainRawJet_contDiff N c i 0 Fin.elim0).of_le (by simp)
  have hd : ContDiff ℝ 1 (coupledPlainRawJet N d i 0 Fin.elim0) :=
    (coupledPlainRawJet_contDiff N d i 0 Fin.elim0).of_le (by simp)
  have hgrad (z : CoupledPlainCoefficients (h := h) N) (x : Vec 2) :
      fderiv ℝ (coupledPlainRawJet N z i 0 Fin.elim0) x (basisVec k) =
        coupledPlainRawJet N z i 1 (fun _ : Fin 1 => k) x :=
    coupledPlainRawJet_fderiv N z i 0 Fin.elim0 k x
  have hibp := Variational.periodic_hilbert_partial_ibp
    (coupledPlainRawJet N c i 0 Fin.elim0) (coupledPlainRawJet N d i 0 Fin.elim0) hc hd
    (coupledPlainRawJet_periodic N c i 0 Fin.elim0)
    (coupledPlainRawJet_periodic N d i 0 Fin.elim0) k
  simp only [hgrad] at hibp
  have hswap : (fun x => inner ℝ (coupledPlainRawJet N c i 0 Fin.elim0 x)
      (coupledPlainRawJet N d i 1 (fun _ : Fin 1 => k) x)) =
      fun x => inner ℝ (coupledPlainRawJet N d i 1 (fun _ : Fin 1 => k) x)
        (coupledPlainRawJet N c i 0 Fin.elim0 x) :=
    funext (fun _ => real_inner_comm _ _)
  rw [hswap] at hibp
  exact hibp
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Relate the actual differentiated drift integrals to the bounded Hilbert commutator. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The Hilbert mask pairing is the literal sum of spatial derivative integrals. -/
theorem plainDriftMaskL2Array_pairing {K j : ℕ} (hj : j ≤ K)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (m : PositionMask j) :
    inner ℝ (driftMaskL2Array hj v hv
      (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
      (fun a => (coupledPlainRawJet_contDiff N c i a.1.val a.2).continuous) m)
      (orderL2Array (jetToL2
        (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
        (fun a => coupledPlainRawJet_memLp N c i a.1.val a.2)) ⟨j, by omega⟩) =
      ∑ w : DerivativeWord2 j, ∫ x in AVenhance.unitCube,
        inner ℝ (driftMaskTerm hj v
          (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2) m w x)
          (coupledPlainRawJet N c i j w x) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (driftMaskTerm_memLp hj v hv
      (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
      (fun a => (coupledPlainRawJet_contDiff N c i a.1.val a.2).continuous) m w).coeFn_toLp,
    (coupledPlainRawJet_memLp N c i j w).coeFn_toLp] with x hx hy
  simpa only [driftMaskL2Array, orderL2Array, jetToL2, WithLp.ofLp_toLp] using
    congrArg₂ (inner ℝ) hx hy

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- A principal mask vanishes when paired with the corresponding differentiated field. -/
theorem plainDriftMaskL2Array_principal_pairing_zero {K j : ℕ} (hj : j ≤ K)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ v x (basisVec k) k = 0)
    (m : PositionMask j) (hm : maskLeftLength j m = 0) :
    inner ℝ (driftMaskL2Array hj v hv
      (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
      (fun a => (coupledPlainRawJet_contDiff N c i a.1.val a.2).continuous) m)
      (orderL2Array (jetToL2
        (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
        (fun a => coupledPlainRawJet_memLp N c i a.1.val a.2)) ⟨j, by omega⟩) = 0 := by
  rw [plainDriftMaskL2Array_pairing hj N c i v hv m]
  apply Finset.sum_eq_zero
  intro w _
  have hz := periodic_hilbert_transport_energy_zero v (hv.of_le (by simp)) hp hd
    (coupledPlainRawJet N c i j w)
    ((coupledPlainRawJet_contDiff N c i j w).of_le (by simp))
    (coupledPlainRawJet_periodic N c i j w)
  simpa only [plainDrift_principalMask hj N c i v m hm,
    sum_inner, real_inner_smul_left, coupledPlainRawJet_fderiv] using hz

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Removing the principal transport part leaves exactly the bounded commutator pairing. -/
theorem plainDrift_full_pairing_eq_commutator {K j : ℕ} (hj : j ≤ K)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ v x (basisVec k) k = 0) :
    (∑ m : PositionMask j, ∑ w : DerivativeWord2 j, ∫ x in AVenhance.unitCube,
      inner ℝ (driftMaskTerm hj v
        (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2) m w x)
        (coupledPlainRawJet N c i j w x)) =
      inner ℝ (driftCommutatorL2Array hj v hv
        (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
        (fun a => (coupledPlainRawJet_contDiff N c i a.1.val a.2).continuous))
        (orderL2Array (jetToL2
          (fun a : JetIndex2 (K + 1) => coupledPlainRawJet N c i a.1.val a.2)
          (fun a => coupledPlainRawJet_memLp N c i a.1.val a.2)) ⟨j, by omega⟩) := by
  simp_rw [← plainDriftMaskL2Array_pairing hj N c i v hv]
  unfold driftCommutatorL2Array
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : 1 ≤ maskLeftLength j m
  · rw [ite_eq_left hm]
  · have hz : maskLeftLength j m = 0 := by omega
    rw [ite_eq_right hm, inner_zero_left,
      plainDriftMaskL2Array_principal_pairing_zero hj N c i v hv hp hd m hz]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Absolute absorption of the full differentiated transport contribution of the synthesized field. -/
theorem plainDrift_full_energy_abs_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hp : AVenhance.IsZ2Periodic v)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ v x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    |∑ j : Fin (K + 1), factorialWeight ρ j.val *
      ∑ m : PositionMask j.val, ∑ w : DerivativeWord2 j.val,
        ∫ x in AVenhance.unitCube, inner ℝ
          (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v
            (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2) m w x)
          (coupledPlainRawJet N c i j.val w x)| ≤
      (ν / 4) * gradFactorialNormSq ρ (jetToL2
        (fun z : JetIndex2 (K + 1) => coupledPlainRawJet N c i z.1.val z.2)
        (fun z => coupledPlainRawJet_memLp N c i z.1.val z.2)) := by
  simp_rw [plainDrift_full_pairing_eq_commutator _ N c i v hv hp hd]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  simp_rw [abs_mul, abs_of_nonneg (factorialWeight_nonneg ρ _)]
  exact driftCommutatorL2Array_energy_abs_sum_le hK ρ a B lam ν hρ ha hB hlam hν hsmall hstrain
    v hv hjets _ (fun z => (coupledPlainRawJet_contDiff N c i z.1.val z.2).continuous) _
end

/-! One forcing coefficient is exactly the native component value-minus-
flux test against its retained H¹ Fourier mode. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
theorem plainFluxForcingCLM_off_component (N : ℕ)
    (r : CoupledFourierModeIndex (h := h) N) (i : ι) (hi : i ≠ r.1)
    (K : ℕ) (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => h i))) :
    plainFluxForcingCLM N r i K F = 0 := by
  rw [plainFluxForcingCLM_eq_integral]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun x => by simp [coupledModeJet, hi])

omit [Fintype ι] in
theorem plainFluxForcingCLM_mode_pairing (N : ℕ)
    (r : CoupledFourierModeIndex (h := h) N) (i : ι) (K : ℕ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => h i))) :
    plainFluxForcingCLM N r i K F = inner ℝ (torusHkValueCLM F)
      (torusH1GradientL2CLM (E := h i) (coupledModeHk N r i 1)) := by
  rw [plainFluxForcingCLM_eq_integral, L2.inner_def]
  apply integral_congr_ae
  have hm : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      (coupledModeHk N r i 1).val ⟨⟨1, by omega⟩, fun _ => k⟩ x =
        coupledModeJet N r i 1 (fun _ => k) x :=
    ae_all_iff.mpr (fun k => coupledModeHk_jet_ae N r i 1 ⟨⟨1, by omega⟩, fun _ => k⟩)
  filter_upwards [torusH1GradientL2CLM_ae (coupledModeHk N r i 1), hm] with x hx hmx
  rw [hx]
  simp only [PiLp.inner_apply]
  simp_rw [hmx]

theorem plainSourceCoefficients_mode_pairing (N : ℕ) (K : ι → ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) (r : CoupledFourierModeIndex (h := h) N) :
    plainSourceCoefficients N K F g r =
      inner ℝ (torusHkValueCLM (g r.1)) (torusHkValueCLM (coupledModeHk N r r.1 1)) -
      inner ℝ (torusHkValueCLM (F r.1))
        (torusH1GradientL2CLM (E := h r.1) (coupledModeHk N r r.1 1)) := by
  unfold plainSourceCoefficients
  rw [Finset.sum_eq_single r.1]
  · rw [plainFluxForcingCLM_mode_pairing]
    change plainValueForcingCLM N r r.1 (K r.1) (g r.1) - _ = _
    rw [← plainInitialCoefficients_component N K g r, plainInitialCoefficients_mode_pairing]
  · intro i _ hi
    rw [plainValueForcingCLM_off_component N r i hi, plainFluxForcingCLM_off_component N r i hi]
    exact sub_self 0
  · simp
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Exact mass energy and dissipation of actual Fourier projections converge
at closed times and in the full time integral. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem galerkinProj_massNormSq_tendsto (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (w : ∀ i, TorusHk (K i) (E i)) :
    Tendsto (fun N => massNormSq ρ π (fun i => (galerkinProj N (w i)).val)) atTop
      (𝓝 (massNormSq ρ π (fun i => (w i).val))) := by
  have hl := ((massWeightedCarrierCLM (E := E) K ρ π).continuous.tendsto w).comp
    (carrierFamilyProjection_tendsto K w)
  have hh := hl.norm.pow 2
  simpa only [Function.comp_def, massWeightedCarrierCLM_normSq K ρ π hπ,
    carrierFamilyProjection_apply] using hh

theorem torusGradientTensor_massNormSq (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (w : ∀ i, TorusHk (K i + 1) (E i)) :
    massNormSq ρ π (fun i => (torusGradientTensor (w i)).val) =
      massGradNormSq ρ π (fun i => (w i).val) := by
  unfold massNormSq massGradNormSq
  simp only [torusGradientTensor_factorialNormSq]

theorem galerkinProj_massGradNormSq_integral_tendsto (K : ι → ℕ) (a b ρ : ℝ) (π : ι → ℝ)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (E i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => ∫ t in Set.Icc a b,
      massGradNormSq ρ π (fun i => (galerkinProj N (w i t)).val)) atTop
      (𝓝 (∫ t in Set.Icc a b, massGradNormSq ρ π (fun i => (w i t).val))) := by
  let G := fun i t => torusGradientTensor (w i t)
  let R := fun N i t => torusGradientTensor (galerkinProj N (w i t) - w i t)
  have htail (N : ℕ) (i : ι) : MemLp (fun t => galerkinProj N (w i t) - w i t)
      2 (volume.restrict (Set.Icc a b)) := by
    simpa only [Function.comp_def, Pi.sub_apply] using!
      ((galerkinProj N).comp_memLp' (hw i)).sub (hw i)
  have hG (i : ι) : MemLp (G i) 2 (volume.restrict (Set.Icc a b)) :=
    torusGradientTensor_carrier_memLp (K i) a b (w i) (hw i)
  have hR (N : ℕ) (i : ι) : MemLp (R N i) 2 (volume.restrict (Set.Icc a b)) :=
    torusGradientTensor_carrier_memLp (K i) a b _ (htail N i)
  have hlim (i : ι) : Tendsto (fun N => ∫ t in Set.Icc a b, ‖R N i t‖ ^ 2) atTop (𝓝 0) := by
    have hh := timeL2_integral_square_clm_tendsto (volume.restrict (Set.Icc a b))
      (torusGradientTensorCLM (E := E i) (K i))
      (fun N t => galerkinProj N (w i t) - w i t) (fun N => htail N i)
      (galerkinProj_time_tail_square_tendsto (K i + 1) a b (w i) (hw i))
    simpa only [torusGradientTensorCLM_apply] using hh
  have hh := torusMassNormSq_perturbed_integral_tendsto (volume.restrict (Set.Icc a b)) K ρ π G hG R hR hlim
  have he (N : ℕ) (i : ι) (t : ℝ) : G i t + R N i t = torusGradientTensor (galerkinProj N (w i t)) := by
    dsimp only [G, R]
    rw [torusGradientTensor_sub]
    abel
  simpa only [he, G, torusGradientTensor_massNormSq K ρ π] using hh

end AVRegularity.CoupledEnergy.Galerkin
end
