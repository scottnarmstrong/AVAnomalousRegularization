-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.FiniteDriftCoefficient
public import AVRegularity.EntryWeak.MetricCloseEllipticity
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CycleEvolution.FibreCoefficientConvolutionSum
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Velocity.Port.Section2FlowRegularityCore
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The molecular lower bound survives realification and cell integration. -/

def molecularVectorEnergy (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (w : Fin 2 → ComplexCellL2) : ℝ :=
  ∑ j : Fin 2, ∑ k : Fin 2, G t j k * inner ℝ (w j) (w k)

theorem molecularVectorEnergy_coercive (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j) (t : ℝ) (w : Fin 2 → ComplexCellL2) :
    (3 / 4) * ∑ j, ‖w j‖ ^ 2 ≤ molecularVectorEnergy G t w := by
  let f := fun j k x => G t j k * (w j x * star (w k x)).re
  have hf (j k : Fin 2) : Integrable (f j k) (volume.restrict AVenhance.unitCube) :=
    (cellPlain_pairing_integrable (w j) (w k)).const_mul (G t j k)
  have hfs (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hf j k)
  have hfss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hfs j)
  have hd (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (w j))
  have hds : Integrable (fun x => ∑ j : Fin 2, ‖w j x‖ ^ 2)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have h := integral_mono_ae (hds.const_mul (3 / 4)) hfss
    (Filter.Eventually.of_forall (fun x => by
      have hx := molecularMetric_complex_coercive G hG t (fun j => w j x)
      simpa [f, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, mul_assoc,
        mul_sub] using hx))
  have hE : (∫ x in AVenhance.unitCube, ∑ j : Fin 2, ∑ k : Fin 2, f j k x) =
      molecularVectorEnergy G t w := by
    rw [integral_finsetSum Finset.univ (fun j _ => hfs j)]
    unfold molecularVectorEnergy
    apply Finset.sum_congr rfl
    intro j _
    change (∫ x in AVenhance.unitCube, ∑ k : Fin 2, f j k x) = _
    rw [integral_finsetSum Finset.univ (fun k _ => hf j k)]
    apply Finset.sum_congr rfl
    intro k _
    simp only [f, integral_const_mul, ← cellPlain_pairing_eq_integral]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hd j), hE] at h
  simp_rw [cellL2_norm_sq_integral] at h
  exact h

theorem molecularDiffusionForm_coercive (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j) (t : ℝ) (u : TorusHk 1 ℂ) :
    (3 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤ -molecularDiffusionForm G t u u := by
  rw [molecularDiffusionForm_apply, neg_neg]
  exact molecularVectorEnergy_coercive G hG t (fun j => cellDerivativeCLM j u)

theorem molecularDiffusionForm_meanZero_gap (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j) (t : ℝ) (u : TorusHk 1 ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    3 * Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 ≤ -molecularDiffusionForm G t u u := by
  have hp := cellH1_meanZero_poincare u hm
  rw [← div_eq_inv_mul] at hp
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  have hmul := (le_div_iff₀ hπ).mp hp
  calc
    _ = (3 / 4) * (‖torusHkValueCLM u‖ ^ 2 * (4 * Real.pi ^ 2)) := by ring
    _ ≤ (3 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ ≤ -molecularDiffusionForm G t u u := molecularDiffusionForm_coercive G hG t u

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! A genuine finite-regularity transport carrier and its Sobolev norm estimate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def finiteTransportBudget (K : ℕ) (Cv : ℝ) (j : Fin (K + 1)) : ℝ :=
  (Fintype.card (DerivativeWord2 j.val) : ℝ) *
    (∑ k : Fin 2, Cv * ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k‖)

def finiteTransport (K : ℕ) (v : Vec 2 → Vec 2) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) v) (hp : AVenhance.IsZ2Periodic v)
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (u : TorusHk K (PiLp 2 (fun _ : Fin 2 => E))) : TorusHk K E :=
  u.mulCoefficient (A := finiteTransportBudget (E := E) K Cv) (driftFiberCoefficient v) (finite_driftFiberCoefficient_contDiff K v hv)
    (fun n x => by rw [driftFiberCoefficient_eq_sum]; dsimp only; rw [hp n x])
    (fun j x => finite_driftFiberCoefficient_array_bound j.val v
      (hv.of_le (by exact_mod_cast Nat.le_of_lt_succ j.isLt)) Cv hCv
      (hb j.val (Nat.le_of_lt_succ j.isLt)) x)

theorem finiteTransport_value_ae (K : ℕ) (v : Vec 2 → Vec 2) (Cv : ℝ)
    (hCv : 0 ≤ Cv) (hv : ContDiff ℝ (K : ℕ∞) v) (hp : AVenhance.IsZ2Periodic v)
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (u : TorusHk K (PiLp 2 (fun _ : Fin 2 => E))) :
    (finiteTransport K v Cv hCv hv hp hb u).val (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube]
      fun x => ∑ k : Fin 2, v x k • u.val (valueIndex2 K) x k := by
  let w := u.toFunction.mulCoefficient (A := finiteTransportBudget (E := E) K Cv) (driftFiberCoefficient v)
    (finite_driftFiberCoefficient_contDiff K v hv)
    (fun n x => by rw [driftFiberCoefficient_eq_sum]; dsimp only; rw [hp n x])
    (fun j x => finite_driftFiberCoefficient_array_bound j.val v
      (hv.of_le (by exact_mod_cast Nat.le_of_lt_succ j.isLt)) Cv hCv
      (hb j.val (Nat.le_of_lt_succ j.isLt)) x)
  have hw := torusJetToL2_ae w.jet w.hasPeriodicWeakJet.2.1 (valueIndex2 K)
  have hu := periodicJetRepresentative_ae u.val (valueIndex2 K)
  filter_upwards [hw, hu] with x hx hux
  change torusJetToL2 w.jet w.hasPeriodicWeakJet.2.1 (valueIndex2 K) x = _
  rw [hx]
  change multiplicationRawJet (driftFiberCoefficient v) u.toFunction.jet (valueIndex2 K) x = _
  rw [multiplicationRawJet_value, driftFiberCoefficient_apply]
  change u.toFunction.jet (valueIndex2 K) x = u.val (valueIndex2 K) x at hux
  rw [hux]

theorem finiteTransport_factorialNorm_le (K : ℕ) (v : Vec 2 → Vec 2) (Cv : ℝ)
    (hCv : 0 ≤ Cv) (hv : ContDiff ℝ (K : ℕ∞) v) (hp : AVenhance.IsZ2Periodic v)
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (u : TorusHk K (PiLp 2 (fun _ : Fin 2 => E))) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt (factorialNormSq ρ (finiteTransport K v Cv hCv hv hp hb u).val) ≤
      (∑ j : Fin (K + 1), factorialRootWeight ρ j.val * finiteTransportBudget (E := E) K Cv j) *
        Real.sqrt (factorialNormSq ρ u.val) :=
  TorusHk.mulCoefficient_factorialNorm_le u _ _ _ hρ

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! A small inverse-Jacobian error gives the required molecular metric window. -/

theorem gram_close_entry_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 / 32)
    (i j : Fin 2) :
    |(A * A.transpose) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 / 8 := by
  let E := A - (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have he (v w : Fin 2) : |E v w| ≤ 1 / 32 := hA v w
  have hid : (A * A.transpose) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
      E i j + E j i + E i 0 * E j 0 + E i 1 * E j 1 := by
    fin_cases i <;> fin_cases j <;>
      simp [E, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;> ring
  have hp (v : Fin 2) : |E i v * E j v| ≤ (1 / 32 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (he i v) (he j v) (abs_nonneg _) (by norm_num)
  rw [hid]
  calc
    _ ≤ |E i j + E j i + E i 0 * E j 0| + |E i 1 * E j 1| := abs_add_le _ _
    _ ≤ (|E i j + E j i| + |E i 0 * E j 0|) + |E i 1 * E j 1| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|E i j| + |E j i|) + |E i 0 * E j 0|) + |E i 1 * E j 1| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ ((1 / 32 + 1 / 32) + (1 / 32) ^ 2) + (1 / 32) ^ 2 :=
      add_le_add (add_le_add (add_le_add (he i j) (he j i)) (hp 0)) (hp 1)
    _ ≤ 1 / 8 := by norm_num

theorem gram_close_ellipticity (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 / 32)
    (ξ : Fin 2 → ℝ) :
    (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (A * A.transpose) i j * ξ i * ξ j ∧
      ∑ i, ∑ j, (A * A.transpose) i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2 :=
  metric_close_ellipticity _ (gram_close_entry_bound A hA) ξ

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Adding a regular perturbation flux preserves the natural higher source data. -/

def HigherSourceCarrierData.add_flux {I K src flux}
    (Q : HigherSourceCarrierData I K src flux)
    (j : ℝ → Vec 2 → ComplexCellVector) (J : ℝ → TorusHk K ComplexCellVector)
    (Nj : ℝ) (hNj : 0 ≤ Nj)
    (hp : MemLp (Function.uncurry j) 2 ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hJ : MemLp J 2 (volume.restrict I))
    (hj : ∀ᵐ t ∂volume.restrict I,
      torusHkValueCLM (J t) =ᵐ[volume.restrict AVenhance.unitCube] j t)
    (hb : ∀ t ∈ I, ‖J t‖ ≤ Nj) : HigherSourceCarrierData I K src (flux + j) where
  S := Q.S
  F := Q.F + J
  Ns := Q.Ns
  Nf := Q.Nf + Nj
  scalar_budget_nonneg := Q.scalar_budget_nonneg
  flux_budget_nonneg := add_nonneg Q.flux_budget_nonneg hNj
  scalar_memLp := Q.scalar_memLp
  flux_memLp := timeMemLp_pointwise_add (E := ComplexCellVector)
    ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) 2
    (Function.uncurry flux) (Function.uncurry j) Q.flux_memLp hp
  scalar_carrier_memLp := Q.scalar_carrier_memLp
  flux_carrier_memLp := timeMemLp_pointwise_add (E := TorusHk K ComplexCellVector)
    (volume.restrict I) 2 Q.F J Q.flux_carrier_memLp hJ
  scalar_value := Q.scalar_value
  scalar_mean_zero := Q.scalar_mean_zero
  flux_value := by
    filter_upwards [Q.flux_value, hj] with t ht hjt
    exact higherCarrier_add_value_ae K (Q.F t) (J t) _ _ ht hjt
  scalar_bound := Q.scalar_bound
  flux_bound := by
    intro t ht
    exact (norm_add_le (Q.F t) (J t)).trans (add_le_add (Q.flux_bound t ht) (hb t ht))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Literal measurable higher flux carriers can be added to produced source data. -/

def HigherSourceCarrierData.withAdditionalFlux {I : Set ℝ} {K : ℕ}
    {src : ℝ → Vec 2 → ℂ} {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData I K src flux)
    (J : ℝ → Vec 2 → ComplexCellVector) (w : ℝ → TorusHk K ComplexCellVector)
    (R : ℝ) (hR : 0 ≤ R)
    (hJ : MemLp (Function.uncurry J) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hw : MemLp w 2 (volume.restrict I))
    (he : ∀ᵐ t ∂volume.restrict I, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube] J t)
    (hb : ∀ t ∈ I, ‖w t‖ ≤ R) : HigherSourceCarrierData I K src (flux + J) :=
  Q.add_flux J w R hR hJ hw he hb

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Vanishing past values of a genuine solution also remove its metric perturbation forcing. -/

theorem cellSolution_past_zero_gradient {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution univ C src F D) (a : ℝ)
    (h0 : ∀ t, t ≤ a → cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ᵐ t ∂volume.restrict (Iic a),
      cellGradient (D t) =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  have hj := hD.2.1.filter_mono
    (ae_mono (Measure.restrict_mono (subset_univ (Iic a)) le_rfl))
  filter_upwards [hj, ae_restrict_mem measurableSet_Iic] with t ht hm
  exact weakJet_zero_value_gradient (D t) ht (h0 t hm)

theorem cellSolution_past_zero_metric_flux {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution univ C src F D) (a : ℝ)
    (h0 : ∀ t, t ≤ a → cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ᵐ t ∂volume.restrict (Iic a),
      cellMetricFlux G D t =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  filter_upwards [cellSolution_past_zero_gradient D hD a h0] with t ht
  filter_upwards [ht] with x hx
  change cellMetricFluxVector (G t x) (cellGradient (D t) x) = 0
  rw [hx]
  apply PiLp.ext
  intro j
  simp [cellMetricFluxVector]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! At determinant one the planar inverse is linear in the Jacobian entries. -/

theorem planar_inverse_eq_adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 1) : A⁻¹ = A.adjugate := by
  rw [Matrix.inv_def, hA]
  simp

theorem planar_inverse_entry_formula (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 1) (i j : Fin 2) :
    A⁻¹ i j = (if i = j then 1 else -1) * A j.rev i.rev := by
  rw [planar_inverse_eq_adjugate A hA, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! A positive finite-order Péclet threshold for the proved transport budget. -/

theorem finiteTransportBudget_linear (K : ℕ) (Cv : ℝ) (j : Fin (K + 1)) :
    finiteTransportBudget (E := ℂ) K Cv j = Cv * finiteTransportBudget (E := ℂ) K 1 j := by
  unfold finiteTransportBudget
  rw [← Finset.mul_sum]
  simp only [one_mul]
  ring

theorem finiteTransportBudgetSum_linear (K : ℕ) (ρ Cv : ℝ) :
    (∑ j : Fin (K + 1), factorialRootWeight ρ j.val * finiteTransportBudget (E := ℂ) K Cv j) =
      Cv * ∑ j : Fin (K + 1), factorialRootWeight ρ j.val * finiteTransportBudget (E := ℂ) K 1 j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteTransportBudget_linear K Cv j]
  ring

def smallPecletThreshold (K : ℕ) (ρ Cv : ℝ) : ℝ :=
  1 / (8 * (1 + |Cv * ∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
    finiteTransportBudget (E := ℂ) K 1 j|))

theorem smallPecletThreshold_pos (K : ℕ) (ρ Cv : ℝ) : 0 < smallPecletThreshold K ρ Cv := by
  unfold smallPecletThreshold
  positivity

theorem smallPecletThreshold_budget (K : ℕ) (ρ Cv Pe : ℝ) (hPe : 0 ≤ Pe)
    (hsmall : Pe ≤ smallPecletThreshold K ρ Cv) :
    (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K (Pe * Cv) j) ≤ 1 / 8 := by
  rw [finiteTransportBudgetSum_linear]
  let B := Cv * ∑ j : Fin (K + 1), factorialRootWeight ρ j.val * finiteTransportBudget (E := ℂ) K 1 j
  have hb : Pe * (8 * (1 + |B|)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hsmall
  have hab := mul_le_mul_of_nonneg_left (le_abs_self B) hPe
  change Pe * Cv * _ ≤ _
  have he : Pe * Cv * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K 1 j) = Pe * B := by dsimp only [B]; ring
  rw [he]
  nlinarith

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A genuine source reserve supplies the actual periodic good field used by the polynomial identities. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem JointSourceReserve.goodField {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (t : ℝ) : GoodField H (fun X z => f t z X) := by
  refine ⟨?_, Q.periodic t⟩
  exact (Q.regular t).comp (contDiff_snd.prodMk contDiff_fst)

omit [BorelSpace E] [SecondCountableTopology E] in
theorem JointSourceReserve.exponentialGoodField {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) :
    GoodField H (fun X z => Real.exp (A X) • f t z X) := by
  refine ⟨?_, ?_⟩
  · exact (Real.contDiff_exp.comp (A.contDiff.comp contDiff_fst)).smul (Q.goodField t).1
  · intro X k z
    exact congrArg (fun e : E => Real.exp (A X) • e) (Q.periodic t X k z)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The actual pulse drift has precisely the weak Péclet amplitude on the unit cell. -/

theorem normalizedPulseDrift_horizontal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : k % 4 = 1)
    (s : ℝ) (z : Vec 2) :
    ocPulseCellDrift α q Λ ζ m ν k s z =
      ![0, (ocEpsilon q Λ m ^ (1 + α) / ν) *
        (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s)) *
        Real.cos (2 * Real.pi * z 0)] := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  unfold ocPulseCellDrift
  rw [ocShearVel_horizontal hk]
  have hphase : 2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (ocEpsilon q Λ m • z) 0 =
      2 * Real.pi * z 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hphase]
  ext i
  fin_cases i
  · simp
  · simp only [Pi.smul_apply, smul_eq_mul]
    change (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) *
        ((2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          Real.cos (2 * Real.pi * z 0))) = _
    rw [ocEll_sq_eq hν]
    field_simp [he.ne', hν.ne']
    simp
    ring_nf
    rw [mul_inv_cancel₀ hν.ne']
    simp

theorem normalizedPulseDrift_vertical {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : k % 4 = 3)
    (s : ℝ) (z : Vec 2) :
    ocPulseCellDrift α q Λ ζ m ν k s z =
      ![-((ocEpsilon q Λ m ^ (1 + α) / ν) *
        (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s)) *
        Real.cos (2 * Real.pi * z 1)), 0] := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  unfold ocPulseCellDrift
  rw [ocShearVel_vertical hk]
  have hphase : 2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (ocEpsilon q Λ m • z) 1 =
      2 * Real.pi * z 1 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hphase]
  ext i
  fin_cases i
  · simp only [Pi.smul_apply, smul_eq_mul]
    change (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) *
        (-(2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          Real.cos (2 * Real.pi * z 1))) = _
    rw [ocEll_sq_eq hν]
    field_simp [he.ne', hν.ne']
    simp
    ring_nf
    rw [mul_inv_cancel₀ hν.ne']
    simp
  · simp

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Derivatives of a determinant-one planar inverse need no denominator estimates. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem planar_inverse_entry_derivative_norm
    (A : P → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ x, (A x).det = 1) (i j : Fin 2) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => (A y)⁻¹ i j) x‖ =
      ‖iteratedFDeriv ℝ n (fun y => A y j.rev i.rev) x‖ := by
  have he : (fun y => (A y)⁻¹ i j) =
      fun y => (if i = j then 1 else -1) * A y j.rev i.rev :=
    funext (fun y => planar_inverse_entry_formula (A y) (hA y) i j)
  rw [he]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte, neg_one_mul]
    change ‖iteratedFDeriv ℝ n (-(fun y => A y j.rev i.rev)) x‖ = _
    rw [iteratedFDeriv_neg]
    change ‖-(iteratedFDeriv ℝ n (fun y => A y j.rev i.rev) x)‖ = _
    exact norm_neg _

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The literal weak pulse drift has a uniform Péclet-linear value bound. -/

theorem normalizedPulseDrift_norm_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) (s : ℝ) (z : Vec 2) :
    ‖ocPulseCellDrift α q Λ ζ m ν k s z‖ ≤
      (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi) := by
  let Pe := ocEpsilon q Λ m ^ (1 + α) / ν
  have hPe : 0 ≤ Pe := div_nonneg (Real.rpow_nonneg
    (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le
  have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k
    (ocEll q Λ m ν ^ 2 * s)
  have hc (i : Fin 2) :
      |Pe * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s)) *
        Real.cos (2 * Real.pi * z i)| ≤ Pe * (2 * Real.pi) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hPe, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_nonneg hp.1]
    calc
      _ ≤ Pe * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s)) :=
        mul_le_of_le_one_right (mul_nonneg hPe (mul_nonneg (by positivity) hp.1))
          (Real.abs_cos_le_one _)
      _ ≤ Pe * (2 * Real.pi) := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * Real.pi) hp.2) hPe
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hPe (by positivity))).2
  intro i
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    obtain ⟨r, rfl⟩ := hk
    omega
  rcases hk4 with h1 | h3
  · rw [normalizedPulseDrift_horizontal hΛ hν h1]
    fin_cases i
    · change ‖(0 : ℝ)‖ ≤ Pe * (2 * Real.pi)
      simpa using mul_nonneg hPe (by positivity : 0 ≤ 2 * Real.pi)
    · change ‖Pe * (2 * Real.pi * _) * Real.cos (2 * Real.pi * z 0)‖ ≤ _
      exact hc 0
  · rw [normalizedPulseDrift_vertical hΛ hν h3]
    fin_cases i
    · change ‖-(Pe * (2 * Real.pi * _) * Real.cos (2 * Real.pi * z 1))‖ ≤ _
      simpa only [norm_neg, Real.norm_eq_abs] using hc 1
    · change ‖(0 : ℝ)‖ ≤ Pe * (2 * Real.pi)
      simpa using mul_nonneg hPe (by positivity : 0 ≤ 2 * Real.pi)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Cutoff-independent spatial energy for the bounded molecular generator. -/

theorem molecularGenerator_source_energy_bound
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    2 * (molecularGeneratorForm G v V hv hb t u u + cellSourceFunctional 0 S F u) +
      (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      (1 + 8 * V ^ 2) * ‖torusHkValueCLM u‖ ^ 2 +
        ‖S‖ ^ 2 + 4 * ∑ j, ‖F j‖ ^ 2 := by
  have hd := molecularDiffusionForm_coercive G hG t u
  have hdr (j : Fin 2) := cellDrift_pairing_abs_le
    (molecularCoefficients G v) V hv hb t j (cellDerivativeCLM j u) (torusHkValueCLM u)
  have hF (j : Fin 2) := abs_real_inner_le_norm (F j) (cellDerivativeCLM j u)
  have hS := abs_real_inner_le_norm S (torusHkValueCLM u)
  have hdr' (j : Fin 2) := (neg_le_abs _).trans (hdr j)
  have hF' (j : Fin 2) := (neg_le_abs _).trans (hF j)
  have hS' := (le_abs_self _).trans hS
  have hshift (j : Fin 2) : cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j =
      cellDerivativeCLM j := by simp [cellShiftedDerivativeCLM, cellScalarCLM]
  simp only [molecularGeneratorForm, sub_apply, add_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply, cellSourceFunctional, innerSL_apply_apply,
    hshift, Fin.sum_univ_two] at hd ⊢
  have hyD (j : Fin 2) := sq_nonneg
    (‖cellDerivativeCLM j u‖ / 2 - 2 * |V| * ‖torusHkValueCLM u‖)
  have hyF (j : Fin 2) := sq_nonneg (‖cellDerivativeCLM j u‖ / 2 - 2 * ‖F j‖)
  have hyS := sq_nonneg (‖S‖ - ‖torusHkValueCLM u‖)
  have hV : |V| ^ 2 = V ^ 2 := sq_abs V
  nlinarith [hdr' 0, hdr' 1, hF' 0, hF' 1, hyD 0, hyD 1, hyF 0, hyF 1]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Reuse the genuine bilinear norm product rule on lists, preserving repeated word terms. -/

theorem independent_metric_flux_list_product_rule_tendsto {P J : Type*}
    (l : Filter P) (r : P → ℝ) (S : List J)
    (A : J → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (B C : J → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E : J → P → ℝ → RawJet2 1 ℂ) (D T : J → ℝ → RawJet2 1 ℂ)
    (hA : ∀ j ∈ S, ∀ p, cellMetricSupNorm (A j p) < ⊤ ∧
      Measurable (Function.uncurry (A j p)))
    (hB : ∀ j ∈ S, cellMetricSupNorm (B j) < ⊤ ∧ Measurable (Function.uncurry (B j)))
    (hC : ∀ j ∈ S, cellMetricSupNorm (C j) < ⊤ ∧ Measurable (Function.uncurry (C j)))
    (hD : ∀ j ∈ S, cellEnergyNorm univ (D j) < ⊤)
    (hEm : ∀ j ∈ S, ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E j p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hDm : ∀ j ∈ S, ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D j z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hTm : ∀ j ∈ S, ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => T j z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hAc : ∀ j ∈ S, Tendsto (fun p => cellMetricSupNorm (r p • (A j p - B j) - C j)) l (𝓝 0))
    (hEc : ∀ j ∈ S, Tendsto (fun p => cellEnergyNorm univ (E j p - D j)) l (𝓝 0))
    (hEd : ∀ j ∈ S, Tendsto (fun p => cellEnergyNorm univ (r p • (E j p - D j) - T j)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ
      (r p • (((S.map (fun j => cellMetricFlux (A j p) (E j p))).sum) -
        (S.map (fun j => cellMetricFlux (B j) (D j))).sum) -
        (S.map (fun j => cellMetricFlux (C j) (D j) + cellMetricFlux (B j) (T j))).sum))
      l (𝓝 0) := by
  simp only [independent_list_map_sum_eq_fin_sum]
  have hm (j : Fin S.length) : S.get j ∈ S := List.get_mem S j
  simpa only [one_smul] using
    cellMetricFlux_finset_productRule_tendsto l r (Finset.univ : Finset (Fin S.length))
      (fun _ => 1) (fun j => A (S.get j)) (fun j => B (S.get j)) (fun j => C (S.get j))
      (fun j => E (S.get j)) (fun j => D (S.get j)) (fun j => T (S.get j))
      (fun j _ => hA _ (hm j)) (fun j _ => hB _ (hm j)) (fun j _ => hC _ (hm j))
      (fun j _ => hD _ (hm j)) (fun j _ => hEm _ (hm j)) (fun j _ => hDm _ (hm j))
      (fun j _ => hTm _ (hm j)) (fun j _ => hAc _ (hm j))
      (fun j _ => hEc _ (hm j)) (fun j _ => hEd _ (hm j))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The inverse Jacobian of an actual offset flow is the Jacobian of its inverse slice. -/

theorem offsetJacobian_inverse_eq {g : ChainGeom} (hg : GeomSpatialSmooth g)
    (hi : ChainGeometry.InvLaw g) (u r : ℝ) (x : Vec 2) :
    (jacMatrix (fun y => g.1 u y r) x)⁻¹ =
      jacMatrix (fun y => g.1 r y u) (g.1 u x r) := by
  have he : (fun y => g.1 r y u) ∘ (fun y => g.1 u y r) = id := by
    funext y
    exact hi r u y
  have hJ := CycleReference.jacMatrix_comp (f := fun y => g.1 r y u)
    (g := fun y => g.1 u y r) x ((hg r u).differentiable (by simp) _)
    ((hg u r).differentiable (by simp) _)
  rw [he, CycleReference.jacMatrix_identity] at hJ
  exact Matrix.inv_eq_left_inv hJ.symm

theorem offsetJacobian_inverse_entry_smooth {g : ChainGeom} (hg : GeomSpatialSmooth g)
    (hi : ChainGeometry.InvLaw g) (u r : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (jacMatrix (fun y => g.1 u y r) x)⁻¹ i j) := by
  have he : (fun x => (jacMatrix (fun y => g.1 u y r) x)⁻¹ i j) =
      fun x => jacMatrix (fun y => g.1 r y u) (g.1 u x r) i j := by
    funext x
    rw [offsetJacobian_inverse_eq hg hi]
  rw [he]
  exact (CycleReference.jacMatrix_entry_smooth (hg r u) i j).comp (hg u r)

theorem actualOffset_inverse_law (D : OCData) (A : RealChain) :
    ChainGeometry.InvLaw (A.geom D) :=
  ChainGeometry.invLaw_geomAux D A.children (A.baseLevel + 1) A.slots
    (ChainGeometry.invLaw_base D A.baseLevel A.base
      (D.slotAnchor (A.baseLevel + 1) (A.slots.headD 0)))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Value-one scalar coefficient reserves give the literal map-valued good fields and box regularity. -/

theorem realLinearMap_field_contDiff_of_value_one {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : ℕ)
    (f : F → ℝ →L[ℝ] ℝ) (hf : ContDiff ℝ (H : ℕ∞) (fun x => f x 1)) :
    ContDiff ℝ (H : ℕ∞) f := by
  have he : f = fun x => f x 1 • ContinuousLinearMap.id ℝ ℝ := by
    funext x
    apply DFunLike.ext
    intro r
    have h := (f x).map_smul r 1
    simpa only [smul_eq_mul, mul_one, smul_apply, ContinuousLinearMap.id_apply, mul_comm] using h
  rw [he]
  exact hf.smul contDiff_const

theorem scalarCoefficient_goodField {ι : Type*} (H m : ℕ)
    (c : LiftCoeff ι (fun _ => ℝ)) (α : DerivativeWord2 m) (v u : ι)
    (Qc : JointSourceReserve H (fun t z Y => c m α t Y z v u 1)) (t : ℝ) :
    GoodField H (fun X z => c m α t X z v u) := by
  refine ⟨?_, ?_⟩
  · exact realLinearMap_field_contDiff_of_value_one H
      (fun X : Vec 2 × Vec 2 => c m α t X.1 X.2 v u) (Qc.goodField t).1
  · intro X k z
    apply DFunLike.ext
    intro r
    have hs (y : Vec 2) : c m α t X y v u r = r • c m α t X y v u 1 := by
      simpa only [smul_eq_mul, mul_one] using (c m α t X y v u).map_smul r 1
    rw [hs, hs]
    have hp := Qc.periodic t X k z
    change c m α t X (z + AVenhance.latticeShift k) v u 1 = c m α t X z v u 1 at hp
    exact congrArg (fun x : ℝ => r • x) hp

theorem scalarCoefficient_boxSmooth {ι : Type*} (H p q m : ℕ) (hpq : p + q ≤ H)
    (c : LiftCoeff ι (fun _ => ℝ)) (α : DerivativeWord2 m) (v u : ι)
    (Qc : JointSourceReserve H (fun t z Y => c m α t Y z v u 1)) (t : ℝ) :
    IsBoxSmooth p q (fun X z => c m α t X z v u) :=
  Weighted.isBoxSmooth_of_joint_contDiff p q _
    ((scalarCoefficient_goodField H m c α v u Qc t).mono hpq).1

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleJointProofs
namespace AVRegularity.EntryWeakProofs

/-! One chronological lowering step preserves genuine joint fast/slow budgets. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem transitionT_independent_slow_cons_local_jet_bound
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (I A : List (Fin 2)) (i : Fin 2) (n : ℕ) (C M : ℝ) (X : P × Vec 2)
    (hKC : ∀ a b j, j ≤ n →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => K Z.1 Z.2 a b) X‖ ≤ C)
    (hTM : ∀ Q j, j ≤ n + 1 →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => transitionT (K Z.1) I Q Z.2) X‖ ≤ M)
    :
    ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => transitionT (K Z.1) (i :: I) A Z.2) X‖ ≤
      3 * (n + 1 : ℕ) * 2 ^ n * C * M := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hKC 0 0 0 (Nat.zero_le _))
  have hM : 0 ≤ M := (norm_nonneg _).trans (hTM [] 0 (Nat.zero_le _))
  let price :=  (n + 1 : ℕ) * (2 : ℝ) ^ n * C * M
  have hP : 0 ≤ price :=  by dsimp only [price]; positivity
  have hT (Q : List (Fin 2)) := transitionT_independent_slow_smooth K hK I Q
  have hD (b : Fin 2) : ContDiff ℝ (n : ℕ∞)
      (fun Z : P × Vec 2 => fderiv ℝ (transitionT (K Z.1) I A) Z.2 (basisVec b)) :=
    ((Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff _ (hT A)).clm_apply
      contDiff_const).of_le (by simp)
  have hp (b : Fin 2) :
      ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => K Z.1 Z.2 b i *
        fderiv ℝ (transitionT (K Z.1) I A) Z.2 (basisVec b)) X‖ ≤ price := by
    apply uniform_product_jet_bound _ _ X n ((hK b i).of_le (by simp)) (hD b) C M
    · intro j hj
      exact hKC b i j hj
    · intro j hj
      apply (independent_slow_directional_derivative_jet_norm_le
        (fun Z : P × Vec 2 => transitionT (K Z.1) I A Z.2) j
        ((hT A).of_le (by simp)) X b).trans
      exact hTM A (j + 1) (Nat.add_le_add_right hj 1)
  have hs : ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => ∑ b : Fin 2,
      K Z.1 Z.2 b i * fderiv ℝ (transitionT (K Z.1) I A) Z.2 (basisVec b)) X‖ ≤ 2 * price := by
    apply (finite_jet_sum_norm_le _ n (fun b => ((hK b i).of_le (by simp)).mul (hD b)) X).trans
    calc
      _ ≤ ∑ _b : Fin 2, price := Finset.sum_le_sum (fun b _ => hp b)
      _ = _ := by simp
  have heP : 3 * (n + 1 : ℕ) * 2 ^ n * C * M = 3 * price := by dsimp only [price]; ring
  rw [heP]
  cases A with
  | nil =>
    have he : (fun Z : P × Vec 2 => transitionT (K Z.1) (i :: I) [] Z.2) =
        fun Z => ∑ b : Fin 2, K Z.1 Z.2 b i *
          fderiv ℝ (transitionT (K Z.1) I []) Z.2 (basisVec b) := by
      funext Z
      simp only [transitionT, add_zero]
    rw [he]
    exact hs.trans (by linarith only [hP])
  | cons a A =>
    have hq : ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 =>
        K Z.1 Z.2 a i * transitionT (K Z.1) I A Z.2) X‖ ≤ price := by
      apply uniform_product_jet_bound _ _ X n ((hK a i).of_le (by simp))
        ((hT A).of_le (by simp)) C M
      · intro j hj
        exact hKC a i j hj
      · intro j hj
        exact hTM A j (hj.trans (Nat.le_succ _))
    have hh := finite_jet_add_norm_le
      (fun Z : P × Vec 2 => ∑ b : Fin 2, K Z.1 Z.2 b i *
        fderiv ℝ (transitionT (K Z.1) I (a :: A)) Z.2 (basisVec b))
      (fun Z : P × Vec 2 => K Z.1 Z.2 a i * transitionT (K Z.1) I A Z.2) n
      (ContDiff.sum (fun b _ => ((hK b i).of_le (by simp)).mul (hD b)))
      (((hK a i).of_le (by simp)).mul ((hT A).of_le (by simp))) X
    change ‖iteratedFDeriv ℝ n
      (fun Z : P × Vec 2 => transitionT (K Z.1) (i :: I) (a :: A) Z.2) X‖ ≤ _ at hh
    exact hh.trans ((add_le_add hs hq).trans_eq (by ring))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Literal ordered metric-word forcing differentiates in its actual uniformly local norm. -/

theorem independent_word_metric_flux_derivative_tendsto {P I : Type*} (l : Filter P) (r : P → ℝ)
    (Gj : List I → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (G0 : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : List I → P → ℝ → RawJet2 1 ℂ)
    (c0 : List I → ℝ → RawJet2 1 ℂ) (i : I) (w : List I)
    (hGj : ∀ p ∈ independentWordForcing w, ∀ X,
      cellMetricSupNorm (Gj p.1 X) < ⊤ ∧ Measurable (Function.uncurry (Gj p.1 X)))
    (hG0 : ∀ p ∈ independentWordForcing w,
      cellMetricSupNorm (G0 p.1) < ⊤ ∧ Measurable (Function.uncurry (G0 p.1)))
    (hG1 : ∀ p ∈ independentWordForcing w,
      cellMetricSupNorm (G0 (i :: p.1)) < ⊤ ∧ Measurable (Function.uncurry (G0 (i :: p.1))))
    (hc0 : ∀ p ∈ independentWordForcing w,
      cellEnergyNorm univ (c0 p.2) < ⊤)
    (hcjm : ∀ p ∈ independentWordForcing w, ∀ X a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => cj p.2 X z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc0m : ∀ p ∈ independentWordForcing w, ∀ a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => c0 p.2 z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc1m : ∀ p ∈ independentWordForcing w, ∀ a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => c0 (i :: p.2) z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hGd : ∀ p ∈ independentWordForcing w,
      Tendsto (fun X => cellMetricSupNorm (r X • (Gj p.1 X - G0 p.1) - G0 (i :: p.1))) l (𝓝 0))
    (hcc : ∀ p ∈ independentWordForcing w,
      Tendsto (fun X => cellEnergyNorm univ
        (cj p.2 X - c0 p.2)) l (𝓝 0))
    (hcd : ∀ p ∈ independentWordForcing w,
      Tendsto (fun X => cellEnergyNorm univ
        (r X • (cj p.2 X - c0 p.2) -
          c0 (i :: p.2))) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ
      (r p • (independentWordMetricFlux (fun u => Gj u p) (fun u => cj u p) w -
        independentWordMetricFlux G0 c0 w) - independentWordMetricFluxDerivative G0 c0 i w)) l (𝓝 0) := by
  exact independent_metric_flux_list_product_rule_tendsto l r (independentWordForcing w)
    (fun p => Gj p.1) (fun p => G0 p.1) (fun p => G0 (i :: p.1))
    (fun p => cj p.2) (fun p => c0 p.2) (fun p => c0 (i :: p.2))
    hGj hG0 hG1 hc0 hcjm hc0m hc1m hGd hcc hcd

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Constant molecular metrics are coercive on every differentiated Sobolev energy. -/

def dataHigherDiffusion (K : ℕ) (ρ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (w : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) : ℝ :=
  ∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ a : DerivativeWord2 j.val,
    molecularVectorEnergy G t (fun k =>
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
        2 (volume.restrict AVenhance.unitCube) (w.val ⟨j, a⟩))

theorem dataHigherDiffusion_coercive (K : ℕ) (ρ : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j)
    (t : ℝ) (w : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) :
    (3 / 4) * factorialNormSq ρ w.val ≤ dataHigherDiffusion K ρ G t w := by
  unfold factorialNormSq derivativeNormSq dataHigherDiffusion
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg _ _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hs := tensorL2_inner_eq_sum (w.val ⟨j, a⟩) (w.val ⟨j, a⟩)
  simp only [real_inner_self_eq_norm_sq] at hs
  rw [hs]
  exact molecularVectorEnergy_coercive G hG t _

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A physical shear has uniform positive jets at every finer label scale. -/

theorem scaled_shear_positive_derivative_bound {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    (k : ℤ) (hk : Odd k) (I ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ ocEpsilon q Λ m)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n (fun y => I • ocShearVel α q Λ m k y) x‖ ≤
      |I| * (2 * Real.pi) ^ (n + 1) * ocA α q Λ m := by
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have ha : ocEpsilon q Λ m ^ α * (ocEpsilon q Λ m)⁻¹ = ocA α q Λ m := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one he.ne']
    unfold ocA
    congr 1
    ring
  have hb := scaled_shear_derivative_norm_le (α := α) (q := q) (m := m) hΛ k hk I n x
  apply scale_ratio_derivative_bound ρ (ocEpsilon q Λ m) hρ he hρe (n - 1)
    (|I| * (2 * Real.pi) ^ (n + 1) * ocA α q Λ m) (by unfold ocA; positivity)
  refine hb.trans_eq ?_
  have hp : ((ocEpsilon q Λ m)⁻¹) ^ n =
      ((ocEpsilon q Λ m)⁻¹) ^ (n - 1) * (ocEpsilon q Λ m)⁻¹ := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
  rw [mul_pow, hp]
  rw [← ha, pow_succ]
  ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! A finite chronological reserve bounds every mixed order-lowering factor. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem transitionT_independent_slow_local_jet_bound
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (X : P × Vec 2)
    (hKC : ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => K Z.1 Z.2 a b) X‖ ≤ C)
    (I A : List (Fin 2)) (n : ℕ) (hn : n + I.length ≤ N) :
    ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => transitionT (K Z.1) I A Z.2) X‖ ≤
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length := by
  induction I generalizing A n with
  | nil =>
    cases A with
    | nil =>
      cases n with
      | zero => simp [transitionT, norm_iteratedFDeriv_zero]
      | succ n => simp [transitionT, iteratedFDeriv_const_of_ne]
    | cons a A => simp [transitionT]
  | cons i I ih =>
    let B := 3 * (N + 1 : ℕ) * (2 : ℝ) ^ N * C
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hnn : n ≤ N := by simp only [List.length_cons] at hn; omega
    have hh := transitionT_independent_slow_cons_local_jet_bound K hK I A i n C (B ^ I.length) X
      (fun a b j hj => hKC a b j (hj.trans hnn))
      (fun Q j hj => ih Q j (by simp only [List.length_cons] at hn; omega))
    have hc : 3 * (n + 1 : ℕ) * (2 : ℝ) ^ n * C ≤ B := by
      have hp : (2 : ℝ) ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hnn
      have hcnt : ((n + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hnn 1
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcnt (by norm_num)
      · exact hp
      · positivity
      · positivity
    exact hh.trans ((mul_le_mul_of_nonneg_right hc (pow_nonneg hB _)).trans_eq (by
      simp only [List.length_cons, pow_succ]
      ring))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Uniform energy of the actual molecular finite systems. -/

theorem molecularFinite_energy_bound {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u du : ℝ → ComplexCellL2) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : MemLp (fun t => (y t).val) 2 (volume.restrict (Icc a b)))
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (molecularGeneratorB G v V hv hb t))
      (fun t => cellGalerkinSource N (cellSourceFunctional 0 (S t) (F t)).toLinearMap)
      u du y) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 + ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2 ≤
        (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2) *
          Real.exp ((1 + 8 * V ^ 2) * (t - a)) := by
  let R := 1 + 8 * V ^ 2
  let f := fun s => ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2
  let d := fun s => (1 / 2) * ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hf : IntervalIntegrable f volume a b := by
    have hsum := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
      (cellTime_normSq_intervalIntegrable hab (hF 1))
    simpa only [f, Fin.sum_univ_two, Pi.add_def] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsum.const_mul 4)
  have hd : IntervalIntegrable d volume a b := by
    have hdj (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
      ((cellDerivativeCLM j).comp_memLp' hy)
    simpa only [d, Fin.sum_univ_two, Function.comp_def, Pi.add_def] using
      ((hdj 0).add (hdj 1)).const_mul (1 / 2)
  apply h.time.energy_dissipation_le_gronwall hab R hR f d hf hd
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [f]; positivity)
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [d]; positivity)
  · have ha := h.agrees
    have he := h.equation
    rw [uIcc_of_le hab] at ha he
    filter_upwards [ha, he] with s has hes
    have hp := molecularGenerator_source_energy_bound G v V hG hv hb s (y s).val (S s) (F s)
    have hi := hes (y s)
    rw [real_inner_comm, has, hi]
    change 2 * (molecularGeneratorForm G v V hv hb s (y s).val (y s).val +
      cellSourceFunctional 0 (S s) (F s) (y s).val) + d s ≤
      R * ‖torusHkValueCLM (y s).val‖ ^ 2 + f s
    simpa only [d, R, f, add_assoc] using hp

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Mean subtraction preserves actual fast smoothness and derivative budgets. -/

theorem smooth_cell_mean_norm_le (f : Vec 2 → ℂ) (C : ℝ) (hb : ∀ z, ‖f z‖ ≤ C) : ‖cellMean f‖ ≤ C := by
  let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simp only [Measure.restrict_apply_univ, weak_unitCube_volume]; exact ENNReal.one_lt_top⟩
  exact (norm_integral_le_of_norm_le_const (μ := volume.restrict AVenhance.unitCube)
    (Filter.Eventually.of_forall hb)).trans_eq (by simp [Measure.real, weak_unitCube_volume])

theorem smooth_cellQ0_periodic (f : Vec 2 → ℂ) (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (cellQ0 f) := by
  intro n z
  change f (z + AVenhance.latticeShift n) - cellMean f = f z - cellMean f
  rw [hp n z]

/-! Mean subtraction preserves the finite fast reserve without additional derivatives. -/

theorem finite_cellQ0 (f : Vec 2 → ℂ) (K : ℕ) (hf : ContDiff ℝ (K : ℕ∞) f) :
    ContDiff ℝ (K : ℕ∞) (cellQ0 f) := hf.sub contDiff_const

theorem finite_cellQ0_derivative_bound (f : Vec 2 → ℂ) (K : ℕ)
    (hf : ContDiff ℝ (K : ℕ∞) f) (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hb : ∀ n, n ≤ K → ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ C n)
    (n : ℕ) (hnK : n ≤ K) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (cellQ0 f) z‖ ≤ 2 * C n := by
  by_cases hn : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero]
    exact (norm_sub_le _ _).trans (by
      have hm := smooth_cell_mean_norm_le f (C 0)
        (fun x => by simpa only [norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le K) x)
      have hx : ‖f z‖ ≤ C 0 := by simpa only [norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le K) z
      linarith)
  · change ‖iteratedFDeriv ℝ n (f - fun _ => cellMean f) z‖ ≤ _
    rw [iteratedFDeriv_sub (hf.of_le (by exact_mod_cast hnK)) contDiff_const,
      iteratedFDeriv_const_of_ne hn, Pi.sub_apply, Pi.zero_apply, sub_zero]
    exact (hb n hnK z).trans (by linarith [hC n])

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A child inherits parent chart budgets with its actual relative-shear error. -/

theorem childGeom_fderiv_factorization (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) (g : ChainGeom) (hg : GeomSpatialSmooth g) (u r : ℝ) (x : Vec 2) :
    fderiv ℝ (fun y => (D.childGeom k pk s' c g).1 u y r) x =
      (fderiv ℝ (fun y => g.1 u y g.2.2)
        (childShearMap D k pk u r c g (g.1 g.2.2 x r))).comp
        ((fderiv ℝ (childShearMap D k pk u r c g) (g.1 g.2.2 x r)).comp
          (fderiv ℝ (fun y => g.1 g.2.2 y r) x)) := by
  let f := fun y => g.1 u y g.2.2
  let z := childShearMap D k pk u r c g
  let p := fun y => g.1 g.2.2 y r
  have hf : Differentiable ℝ f := (hg u g.2.2).differentiable (by simp)
  have hz : Differentiable ℝ z :=
    (childShearMap_spatial_smooth D k pk u r c g).differentiable (by simp)
  have hp : Differentiable ℝ p := (hg g.2.2 r).differentiable (by simp)
  change fderiv ℝ (f ∘ (z ∘ p)) x = _
  rw [fderiv_comp x (hf _) ((hz.comp hp) _)]
  rw [fderiv_comp x (hz _) (hp _)]
  rfl

theorem childGeom_operator_close_of_parent_bounds
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (k : ℕ) (pk : ℤ) (hpk : Odd pk) (s' : ℝ) (c : ChainChild)
    (g : ChainGeom) (hg : GeomSpatialSmooth g) (u r a b : ℝ)
    (hu : ∀ x, ‖fderiv ℝ (fun y => g.1 u y g.2.2) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ a)
    (hr : ∀ x, ‖fderiv ℝ (fun y => g.1 g.2.2 y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ b) (x : Vec 2) :
    ‖fderiv ℝ (fun y => (D.childGeom k pk s' c g).1 u y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      (1 + a) * (1 + |u - r| * ((4 * Real.pi ^ 2) * ocA D.α D.q D.Λ k)) *
        (1 + b) - 1 := by
  rw [childGeom_fderiv_factorization D k pk s' c g hg u r x]
  exact operator_triple_close _ _ _ _ _ _ (hu _)
    (childShearMap_operator_close D hΛ hζ k pk hpk u r c g _) (hr x)

end AVRegularity.EntryWeakProofs
end
end
