-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.EntryWeak.NormalizedLiftAComponentDecomposition
import AVRegularity.CoupledEnergy.Galerkin.PlainSourceEnergy
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity
import AVenhance.Infra.Section3.CorrectorGradient
public import AVRegularity.EntryWeak.WeakTransferPartitionBudget
public import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
import AVRegularity.CycleReference.TransitionZero
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Each scalar lift source uses its own lower-degree and inherited-source reserves. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftAComponentReserve (H : ℕ) (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (v : ι)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q.v t z i))
    (Q1 : ∀ u, JointSourceReserve (H + 2) (fun t z Y => (Real.exp (A Y))⁻¹ •
      liftApply (n - 1) (Cc hh (n - 1)) f t Y z u))
    (Q2 : 2 ≤ n → ∀ u, JointSourceReserve (H + 2) (fun t z Y => (Real.exp (A Y))⁻¹ •
      liftApply (n - 2) (Cc hh (n - 2)) f t Y z u))
    (QS : hh ≠ 0 → ∀ j ∈ Finset.range (min D n + 1),
      JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
        sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) Y z v)) :
    JointSourceReserve H (fun t z Y => normalizedLiftASource Q Cc f hh n A t z Y v) := by
  let F := fun d t z Y => (Real.exp (A Y))⁻¹ • liftApply d (Cc hh d) f t Y z
  have he (d : ℕ) (t : ℝ) : liftApply d (Cc hh d) f t =
      fun X y => Real.exp (A X) • F d t y X := by
    funext X y
    simp only [F, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  let B1 := normalizedCellB1Source A Q.η Q.G Q.v (fun t z Y => F (n - 1) t z Y v)
  let B2 := fun t z Y => if 2 ≤ n then
    normalizedCellB2Source A Q.η Q.G (fun t z Y => F (n - 2) t z Y v) t z Y else 0
  let S := fun t z Y => if hh = 0 then 0 else
    ∑ j ∈ Finset.range (min D n + 1), (Real.exp (A Y))⁻¹ •
      sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) Y z v
  have QB2 : JointSourceReserve H B2 := by
    by_cases hn : 2 ≤ n
    · exact (normalizedCellB2SourceReserve H A Q.η Q.G _ QG (Q2 hn v)).congrSource
        (by funext t z Y; exact (ite_eq_left hn).symm)
    · exact (JointSourceReserve.zero H).congrSource
        (by funext t z Y; exact (ite_eq_right hn).symm)
  have Qs : JointSourceReserve H S := by
    by_cases hhh : hh = 0
    · exact (JointSourceReserve.zero H).congrSource
        (by funext t z Y; exact (ite_eq_left hhh).symm)
    · exact (JointSourceReserve.finsetSum _ H _ (QS hhh)).congrSource
        (by funext t z Y; exact (ite_eq_right hhh).symm)
  have hfield : (fun t z Y => normalizedLiftASource Q Cc f hh n A t z Y v) =
      fun t z Y => B1 t z Y + B2 t z Y - S t z Y := by
    funext t z Y
    unfold normalizedLiftASource liftA
    rw [he (n - 1) t, he (n - 2) t]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_sub, smul_add, B1, B2, S]
    rw [normalizedCellB1Source_component H A Q.η Q.G Q.v (F (n - 1)) QG Q1 t z Y v]
    by_cases hn : 2 ≤ n
    · simp only [ite_eq_left hn]
      rw [normalizedCellB2Source_component H A Q.η Q.G (F (n - 2)) QG (Q2 hn) t z Y v]
      by_cases hhh : hh = 0
      · simp only [ite_eq_left hhh, Pi.zero_apply, smul_zero,
          normalizedCellB1Source, normalizedCellB2Source, Pi.smul_apply]
      · simp only [ite_eq_right hhh, Finset.sum_apply, Finset.smul_sum,
          normalizedCellB1Source, normalizedCellB2Source, Pi.smul_apply]
    · simp only [ite_eq_right hn]
      by_cases hhh : hh = 0
      · simp only [ite_eq_left hhh, Pi.zero_apply, smul_zero,
          normalizedCellB1Source, Pi.smul_apply]
      · simp only [ite_eq_right hhh, Finset.sum_apply, Finset.smul_sum,
          Pi.zero_apply, smul_zero, normalizedCellB1Source, Pi.smul_apply]
  let L : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  have hsub : (fun t z Y => B1 t z Y + B2 t z Y + L (S t z Y)) =
      fun t z Y => B1 t z Y + B2 t z Y - S t z Y := by
    funext t z Y
    simp only [L, neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg]
  exact (((normalizedCellB1SourceReserve H A Q.η Q.G Q.v _ QG Qv (Q1 v)).add QB2).add
    (Qs.map L)).congrSource (hsub.trans hfield.symm)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Grade-zero eddy recursion is independent of the ambient source-degree index. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D D' : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem liftA_zero_grade_degree_congr (Q : LiftOperatorData ι h D) (Q' : LiftOperatorData ι h D')
    (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) :
    liftA Q Cc f 0 n t = liftA Q' Cc f 0 n t := by
  funext X z
  unfold liftA
  rw [hη, hG, hv]
  simp only [ite_true]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem liftCellSource_zero_grade_degree_congr (Q : LiftOperatorData ι h D) (Q' : LiftOperatorData ι h D')
    (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) :
    liftCellSource Q Cc f 0 n t = liftCellSource Q' Cc f 0 n t := by
  have ha q := liftA_zero_grade_degree_congr Q Q' hη hG hv Cc f q t
  have hm q : liftMean Q Cc f 0 q = liftMean Q' Cc f 0 q := by
    funext t'
    unfold liftMean
    rw [liftA_zero_grade_degree_congr Q Q' hη hG hv Cc f q t']
  funext X z
  simp only [liftCellSource, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp only [ha, hm]

theorem isLiftSequence_zero_grade_degree_congr (Q : LiftOperatorData ι h D) (Q' : LiftOperatorData ι h D')
    (hη : Q.η = Q'.η) (hG : Q.G = Q'.G) (hv : Q.v = Q'.v)
    (sX sZ N : ℕ) (a b : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N 0 Cc) : IsLiftSequence Q' sX sZ a b N 0 Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X
  have hh0 : hh = 0 := by omega
  subst hh
  have hi := hc.2.2.2.2.2.2 0 le_rfl n hn hnN f hf X
  rw [hG, hv] at hi
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t _ht
  funext z
  exact congrFun (congrFun (liftCellSource_zero_grade_degree_congr Q Q' hη hG hv Cc (fun _ => f) n t) X) z
end

/-! Genuine cross and inherited Taylor reserves assemble the physical slow flux with their actual budgets. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftInheritedTaylor (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (A : Vec 2 →L[ℝ] ℝ)
    (hh n : ℕ) (u v : ι) (k : Fin 2) (j : ℕ) (t : ℝ) (z Y : Vec 2) : ℝ :=
  (Real.exp (A Y))⁻¹ •
    ((((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
      (fun ε => sourceFlux Q.edge Q.η ε t
        (liftApply (n - j) (Cc (hh - 1) (n - j))
          (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) t) k Y z) 0) v

theorem normalizedLiftFluxX_reserve_assembly (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (A : Vec 2 →L[ℝ] ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (u v : ι) (k : Fin 2)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q.v t z i))
    (Q₁ : ∀ w, JointSourceReserve (H + 1)
      (fun t z Y => normalizedLiftTestField (Cc hh (n - 1)) (n - 1) A u w 1 t Y z))
    (Q₂ : ∀ w, JointSourceReserve (H + 1)
      (fun t z Y => normalizedLiftTestField (Cc hh (n - 2)) (n - 2) A u w 1 t Y z))
    (QT : ∀ j ∈ Finset.Icc 1 (min D n), JointSourceReserve H
      (normalizedLiftInheritedTaylor Q Cc A hh n u v k j)) :
    ∃ R : JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
        (liftFluxX Q Cc (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n t Y z k) v),
      ∀ r, R.budget r =
        (normalizedLiftFluxCrossReserve H A Q.η Q.G Q.v _ _ QG Qv (Q₁ v) (Q₂ v) k).budget r +
        ‖(-Real.sqrt Q.η) • ContinuousLinearMap.id ℝ ℝ‖ *
          ∑ j : Finset.Icc 1 (min D n), (QT j.val j.property).budget r := by
  let C := normalizedLiftFluxCrossReserve H A Q.η Q.G Q.v _ _ QG Qv (Q₁ v) (Q₂ v) k
  let T := JointSourceReserve.finsetSum (Finset.Icc 1 (min D n)) H _ QT
  let L : ℝ →L[ℝ] ℝ := (-Real.sqrt Q.η) • ContinuousLinearMap.id ℝ ℝ
  have he : (fun t z Y =>
      normalizedLiftFluxCrossSource A Q.η Q.G Q.v
        (fun t z Y => normalizedLiftTestField (Cc hh (n - 1)) (n - 1) A u v 1 t Y z)
        (fun t z Y => normalizedLiftTestField (Cc hh (n - 2)) (n - 2) A u v 1 t Y z)
        k t z Y + L (∑ j ∈ Finset.Icc 1 (min D n),
          normalizedLiftInheritedTaylor Q Cc A hh n u v k j t z Y)) =
      (fun t z Y => (Real.exp (A Y))⁻¹ •
        (liftFluxX Q Cc (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n t Y z k) v) := by
    funext t z Y
    rw [normalizedLiftFluxX_decomposition H Q Cc A hh n hn hhpos u v k Q₁ Q₂]
    simp only [L, smul_apply, ContinuousLinearMap.id_apply, neg_smul, sub_eq_add_neg,
      normalizedLiftInheritedTaylor]
  refine ⟨(C.add (T.map L)).congrSource he, ?_⟩
  intro r
  rw [JointSourceReserve.congrSource_budget]
  change C.budget r + ‖L‖ * T.budget r = _
  rw [JointSourceReserve.finsetSum_budget]
end

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVRegularity.Weighted
namespace AVRegularity.EntryWeakProofs

/-! The higher Fourier carriers read the actual molecular diffusion and transport. -/

abbrev FiniteMolecularCoefficients (N : ℕ) :=
  CoupledPlainCoefficients (h := fun _ : Unit => ℂ) N

def dataFiniteFlux (N K : ℕ) (P : MolecularData) (t : ℝ)
    (c : FiniteMolecularCoefficients N) : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)) :=
  mapTorusHkCLM K (metricFiberCoefficient (Matrix.transpose (P.G t)))
    (coupledPlainGradientHk N c Unit.unit K)

def dataFiniteTransport (N K : ℕ) (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c : FiniteMolecularCoefficients N) : TorusHk K ℂ :=
  finiteTransport K (P.v t) Cv hCv hv hp hb (coupledPlainGradientHk N c Unit.unit K)

theorem dataFiniteFlux_coordinate (N K : ℕ) (P : MolecularData) (t : ℝ)
    (c : FiniteMolecularCoefficients N) (k : Fin 2) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
      2 (volume.restrict AVenhance.unitCube) ((dataFiniteFlux N K P t c).val (valueIndex2 K)) =
    ∑ j : Fin 2, P.G t j k • cellDerivativeCLM j (coupledPlainSynthesis N Unit.unit 1 c) := by
  rw [dataFiniteFlux, mapTorusHkCLM_apply, mapTorusHk_jet_eq_compLp,
    molecularFlux_coordinate]
  simp_rw [molecularPlainGradient_coordinate]

theorem dataFiniteTransport_value (N K : ℕ) (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c : FiniteMolecularCoefficients N) :
    (dataFiniteTransport N K P t Cv hCv hv hp hb c).val (valueIndex2 K) =
    ∑ j : Fin 2, cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable
      P.drift_bounded t j (cellDerivativeCLM j (coupledPlainSynthesis N Unit.unit 1 c)) := by
  let w := coupledPlainGradientHk N c Unit.unit K
  let d := fun j : Fin 2 => cellDerivativeCLM j (coupledPlainSynthesis N Unit.unit 1 c)
  let f := fun j : Fin 2 => cellDriftEntryCLM (dataCoefficients P) P.V
    P.drift_measurable P.drift_bounded t j (d j)
  have ht := finiteTransport_value_ae K (P.v t) Cv hCv hv hp hb w
  have hd : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j : Fin 2,
      d j x = w.val (valueIndex2 K) x j := by
    apply ae_all_iff.mpr
    intro j
    have h := ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j) (w.val (valueIndex2 K))
    dsimp only [w] at h
    rw [molecularPlainGradient_coordinate N K c j] at h
    exact h
  have hf := ae_all_iff.mpr (fun j => cellDriftEntryCLM_ae (dataCoefficients P) P.V
    P.drift_measurable P.drift_bounded t j (d j))
  apply Lp.ext
  filter_upwards [ht, hd, hf, Lp.coeFn_finsetSum Finset.univ f] with x htx hdx hfx hsx
  change (finiteTransport K (P.v t) Cv hCv hv hp hb w).val (valueIndex2 K) x = (∑ j, f j) x
  rw [htx, hsx]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  change P.v t x j • w.val (valueIndex2 K) x j =
    cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable P.drift_bounded t j (d j) x
  rw [hfx j, hdx j]
  simp only [dataCoefficients, molecularCoefficients, Complex.real_smul]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The finite higher-source coefficients are exactly the original molecular weak form. -/

theorem dataGeneratorForm_apply (P : MolecularData) (t : ℝ) (u z : TorusHk 1 ℂ) :
    dataGeneratorForm P t u z =
    -(∑ j : Fin 2, ∑ k : Fin 2, P.G t j k * inner ℝ (cellDerivativeCLM j u) (cellDerivativeCLM k z)) -
    ∑ j : Fin 2, inner ℝ (cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable
      P.drift_bounded t j (cellDerivativeCLM j u)) (torusHkValueCLM z) := by
  simp only [dataGeneratorForm, molecularGeneratorForm, sub_apply, sum_apply,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply, molecularDiffusionForm_apply]
  rfl

theorem dataFiniteSource_pairing (N K : ℕ) (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c z : FiniteMolecularCoefficients N) (S : TorusHk K ℂ) :
    (∑ r, plainSourceCoefficients N (fun _ : Unit => K)
      (fun _ => dataFiniteFlux N K P t c)
      (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb c) r * z r) =
    dataGeneratorForm P t (coupledPlainSynthesis N Unit.unit 1 c)
      (coupledPlainSynthesis N Unit.unit 1 z) +
      inner ℝ (S.val (valueIndex2 K)) (torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1 z)) := by
  rw [plainSourceCoefficients_pairing]
  simp only [Fintype.sum_unique]
  have hsub : (S - dataFiniteTransport N K P t Cv hCv hv hp hb c).val (valueIndex2 K) =
      S.val (valueIndex2 K) -
        (dataFiniteTransport N K P t Cv hCv hv hp hb c).val (valueIndex2 K) := rfl
  rw [hsub, inner_sub_left, dataFiniteTransport_value]
  simp only [dataFiniteFlux_coordinate, real_inner_smul_left, sum_inner,
    dataGeneratorForm_apply]
  change inner ℝ (S.val (valueIndex2 K)) (torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1 z)) -
      (∑ j : Fin 2, inner ℝ (cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable
        P.drift_bounded t j (cellDerivativeCLM j (coupledPlainSynthesis N Unit.unit 1 c)))
        (torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1 z))) -
      (∑ k : Fin 2, ∑ j : Fin 2, P.G t j k *
        inner ℝ (cellDerivativeCLM j (coupledPlainSynthesis N Unit.unit 1 c))
          (cellDerivativeCLM k (coupledPlainSynthesis N Unit.unit 1 z))) = _
  rw [Finset.sum_comm (f := fun k j : Fin 2 => P.G t j k *
    inner ℝ (cellDerivativeCLM j (coupledPlainSynthesis N Unit.unit 1 c))
      (cellDerivativeCLM k (coupledPlainSynthesis N Unit.unit 1 z)))]
  ring

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! A jointly measurable classical representative of the actual trace solves the public equation. -/

theorem dataWeakHilbert_classical_solution {a b : ℝ} (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun r => dataDualDerivative P r
      (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)))
    (c : ℝ → Vec 2 → ℝ) (hc : ∀ t, ContDiff ℝ (1 : ℕ∞) (c t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (c t)) (hm : Measurable (Function.uncurry c))
    (he : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (c t x : ℂ)) :
    IsCellSolution (Icc a b) (dataCoefficients P) src F
      (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c) := by
  let E := fun t => complexFiniteJet 1 (c t)
  have hjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] E t j := by
    filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    apply classicalFirstJet_of_H1_value (c t) (hc t) (hp t) (slice t)
    exact (he t hti).symm.trans (Filter.EventuallyEq.of_eq
      (congrArg (fun q : ComplexCellL2 => (q : Vec 2 → ℂ)) ht))
  have hjoint : ∀ j, MemLp (fun p : ℝ × Vec 2 => E p.1 j p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
    obtain ⟨f, hf, hfj⟩ := cellBochner_exists_joint_jet (Icc a b) slice h.state
    intro j
    apply cellProduct_memLp_of_sections (Icc a b) (f j) (fun t x => E t j x) (hf j)
      (complexFiniteJet_joint_measurable 1 c hc hm j)
    filter_upwards [hfj, hjet] with t ht hj
    exact (ht j).symm.trans (hj j)
  have hE : IsCellSolution (Icc a b) (dataCoefficients P) src F E := by
    refine ⟨ordConnected_Icc, Filter.Eventually.of_forall
      (fun t => complexFiniteJet_periodicWeak 1 (c t) (hc t) (hp t)), ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact ⟨(Lp.memLp (u t)).ae_eq (he t ht),
        (complexFiniteJet_periodicWeak 1 (c t) (hc t) (hp t)).1 (valueIndex2 1)⟩
    · intro j
      exact (hjoint j).aestronglyMeasurable
    · exact cellRaw_trace_continuous (Icc a b) u h.trace (cellValue E) he
    · intro s hs t ht
      exact cellRawGradient_energy_finite E hjoint s hs t ht
    · intro s hs t ht hst ψ
      exact dataWeakHilbert_raw_identity P src F hsrc hF u slice h E he hjet s hs t ht hst ψ
  have hEq : cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c = E := by
    funext t
    exact cellJetOfField_id_eq_finite c t
  rw [hEq]
  exact hE

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Small finite source identities separate the additional flux from the generator. -/

theorem molecularSourceFlux_add (N K : ℕ)
    (F H : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) (S : TorusHk K ℂ) :
    plainSourceCoefficients N (fun _ : Unit => K) (fun _ => F + H) (fun _ => S) =
      plainSourceCoefficients N (fun _ : Unit => K) (fun _ => H) (fun _ => S) +
      plainSourceCoefficients N (fun _ : Unit => K) (fun _ => F) (fun _ => 0) := by
  funext r
  let L := plainFluxForcingCLM (h := fun _ : Unit => ℂ) N r Unit.unit K
  let M := plainValueForcingCLM (h := fun _ : Unit => ℂ) N r Unit.unit K
  simp only [plainSourceCoefficients, Fintype.sum_unique, Pi.add_apply]
  change M S - L (F + H) = (M S - L H) + (M 0 - L F)
  rw [L.map_add, M.map_zero]
  ring

theorem molecularSourceFlux_pairing (N K : ℕ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) (z : FiniteMolecularCoefficients N) :
    (∑ r, plainSourceCoefficients N (fun _ : Unit => K) (fun _ => F) (fun _ => 0) r * z r) =
      -∑ k : Fin 2, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) (F.val (valueIndex2 K)))
        (cellDerivativeCLM k (coupledPlainSynthesis N Unit.unit 1 z)) := by
  rw [plainSourceCoefficients_pairing]
  simp only [Fintype.sum_unique]
  change inner ℝ (0 : ComplexCellL2) _ - _ = _
  rw [inner_zero_left, zero_sub]
  rfl

/-! Coordinate identification for the original molecular finite variational equation. -/

def dataFiniteTest (N : ℕ) (z : FiniteMolecularCoefficients N) :
    CellGalerkinSpace (E := ℂ) N :=
  ⟨coupledPlainSynthesis N Unit.unit 1 z, ⟨coupledPlainSynthesis N Unit.unit 1 z,
    plainSynthesis_galerkin_fixed N (fun _ : Unit => 1) z Unit.unit⟩⟩

theorem dataFourierCoordinates_reconstruct (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    coupledPlainSynthesis N Unit.unit 1 (dataFourierCoordinatesCLM N (cellGalerkinValue N u)) =
      u.val := by
  simpa only [dataFourierHighCLM, ContinuousLinearMap.comp_apply,
    dataPlainSynthesisCLM_apply] using dataFourierHigh_one N u

theorem dataFinite_dual_coordinates (N K : ℕ) (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (u du : CellGalerkinSpace (E := ℂ) N) (S : TorusHk K ℂ)
    (heq : ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N du) (cellGalerkinValue N z) =
        dataGeneratorForm P t u.val z.val + inner ℝ (S.val (valueIndex2 K)) (cellGalerkinValue N z)) :
    dataFourierCoordinatesCLM N (cellGalerkinValue N du) =
      plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => dataFiniteFlux N K P t (dataFourierCoordinatesCLM N (cellGalerkinValue N u)))
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb
          (dataFourierCoordinatesCLM N (cellGalerkinValue N u))) := by
  have hd (z : FiniteMolecularCoefficients N) :
      (∑ r, dataFourierCoordinatesCLM N (cellGalerkinValue N du) r * z r) =
      (∑ r, plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => dataFiniteFlux N K P t (dataFourierCoordinatesCLM N (cellGalerkinValue N u)))
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb
          (dataFourierCoordinatesCLM N (cellGalerkinValue N u))) r * z r) := by
    rw [← plainSynthesis_mass_pairing N (fun _ : Unit => 1), dataFiniteSource_pairing]
    simp only [Fintype.sum_unique, dataFourierCoordinates_reconstruct]
    change inner ℝ (torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1
      (dataFourierCoordinatesCLM N (cellGalerkinValue N du)))) _ = _
    rw [dataFourierCoordinates_reconstruct]
    exact heq (dataFiniteTest N z)
  funext r
  simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hd (Pi.single r 1)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Exact finite pairing for the molecular equation with regular divergence sources. -/

theorem dataFiniteSource_flux_pairing (N K : ℕ) (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c z : FiniteMolecularCoefficients N) (S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) :
    (∑ r, plainSourceCoefficients N (fun _ : Unit => K)
      (fun _ => F + dataFiniteFlux N K P t c)
      (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb c) r * z r) =
    dataGeneratorForm P t (coupledPlainSynthesis N Unit.unit 1 c)
      (coupledPlainSynthesis N Unit.unit 1 z) +
      inner ℝ (S.val (valueIndex2 K)) (torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1 z)) -
      ∑ k : Fin 2, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) (F.val (valueIndex2 K)))
        (cellDerivativeCLM k (coupledPlainSynthesis N Unit.unit 1 z)) := by
  rw [molecularSourceFlux_add]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [dataFiniteSource_pairing, molecularSourceFlux_pairing]
  ring

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! The request reserves admit a concrete weak allocation. -/

/-- The request reserves with the producer offset one grade lower. -/
def requestedWeakAllocation (k : InvConsts) (L : ℕ) : InvConsts :=
  { k with c₀ := 1, G0 := k.G0 - 1, mEnv := 0, Lker := max k.Lker L }

theorem requestedWeakAllocation_valid (k : InvConsts) (L : ℕ) (hG0 : 1 ≤ k.G0) :
    (requestedWeakAllocation k L).c₀ = 1 ∧
    IsWeakAllocation (requestedWeakAllocation k L) k L := by
  refine ⟨rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_, rfl, le_rfl, ?_,
    Nat.le_max_right _ _⟩
  · change k.G0 - 1 + 1 ≤ k.G0
    omega
  · change (0 : ℝ) < 1 / ((k.Hprod : ℝ) + 1)
    positivity

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Coordinate identification retains the literal regular divergence source. -/

theorem dataFinite_flux_dual_coordinates (N K : ℕ) (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (u du : CellGalerkinSpace (E := ℂ) N) (S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (heq : ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N du) (cellGalerkinValue N z) =
        dataGeneratorForm P t u.val z.val + inner ℝ (S.val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ k : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
              2 (volume.restrict AVenhance.unitCube)) (F.val (valueIndex2 K)))
            (cellDerivativeCLM k z.val)) :
    dataFourierCoordinatesCLM N (cellGalerkinValue N du) =
      plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => F + dataFiniteFlux N K P t (dataFourierCoordinatesCLM N (cellGalerkinValue N u)))
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb
          (dataFourierCoordinatesCLM N (cellGalerkinValue N u))) := by
  have hd (z : FiniteMolecularCoefficients N) :
      (∑ r, dataFourierCoordinatesCLM N (cellGalerkinValue N du) r * z r) =
      (∑ r, plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => F + dataFiniteFlux N K P t (dataFourierCoordinatesCLM N (cellGalerkinValue N u)))
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb
          (dataFourierCoordinatesCLM N (cellGalerkinValue N u))) r * z r) := by
    rw [← plainSynthesis_mass_pairing N (fun _ : Unit => 1), dataFiniteSource_flux_pairing]
    simp only [Fintype.sum_unique, dataFourierCoordinates_reconstruct]
    change inner ℝ (torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1
      (dataFourierCoordinatesCLM N (cellGalerkinValue N du)))) _ = _
    rw [dataFourierCoordinates_reconstruct]
    exact heq (dataFiniteTest N z)
  funext r
  simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hd (Pi.single r 1)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Parabolic.FourierGalerkin AVenhance.Infra.Classical
namespace AVRegularity.EntryWeakProofs

/-! Constant tests are retained by every molecular Galerkin cutoff. -/

def molecularConstantCoefficients (N : ℕ) (c : ℂ) : FiniteMolecularCoefficients N :=
  fun a => if a.2.1 = realFourierIndexEquivFin N none then
    inner ℝ ((stdOrthonormalBasis ℝ ℂ) a.2.2) c else 0

theorem molecularConstantSynthesis_value (N : ℕ) (c : ℂ) :
    torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1 (molecularConstantCoefficients N c)) =
      cellConstantCLM c := by
  apply Lp.ext
  filter_upwards [coupledPlainSynthesis_jet_ae N Unit.unit 1
    (molecularConstantCoefficients N c) (valueIndex2 1), cellConstantCLM_ae c] with x hx hc
  change torusHkValueCLM _ x = _ at hx
  rw [hx, hc]
  simp only [coupledPlainRawJet, molecularConstantCoefficients, coupledModeJet,
    Fintype.sum_sigma, Fintype.sum_prod_type, Fintype.sum_unique, dite_true,
    coupledModeScalarDerivative, smoothLiftWord, AVenhance.Infra.Classical.classicalWordDerivative,
    valueIndex2, valueIndex, Fin.val_zero]
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [coupledModeScalar, Equiv.symm_apply_apply, realFourierModeAmbient, one_smul]
  exact (stdOrthonormalBasis ℝ ℂ).sum_repr' c

theorem molecularConstantSynthesis_eq (N : ℕ) (c : ℂ) :
    coupledPlainSynthesis N Unit.unit 1 (molecularConstantCoefficients N c) =
      cellH1Scalar c cellH1One := by
  apply TorusHk.ext_value
  change torusHkValueCLM (coupledPlainSynthesis N Unit.unit 1 (molecularConstantCoefficients N c)) =
    torusHkValueCLM (cellH1Scalar c cellH1One)
  rw [molecularConstantSynthesis_value, cellH1Scalar_value, cellH1One_value]
  apply Lp.ext
  filter_upwards [cellConstantCLM_ae c, cellScalarCLM_ae c (cellConstantCLM 1),
    cellConstantCLM_ae 1] with x hc hs h1
  rw [hc, hs, h1, mul_one]

theorem molecularConstant_galerkin_fixed (N : ℕ) (c : ℂ) :
    galerkinProj N (cellH1Scalar c cellH1One) = cellH1Scalar c cellH1One := by
  have h := plainSynthesis_galerkin_fixed N (fun _ : Unit => 1)
    (molecularConstantCoefficients N c) Unit.unit
  simpa only [molecularConstantSynthesis_eq] using h

theorem molecularH1Scalar_one (z : TorusHk 1 ℂ) : cellH1Scalar 1 z = z := by
  apply TorusHk.ext_value
  change torusHkValueCLM (cellH1Scalar 1 z) = torusHkValueCLM z
  rw [cellH1Scalar_value]
  change (1 : ℂ) • torusHkValueCLM z = torusHkValueCLM z
  exact one_smul _ _

theorem molecularOne_galerkin_fixed (N : ℕ) : galerkinProj N cellH1One = cellH1One := by
  simpa only [molecularH1Scalar_one] using molecularConstant_galerkin_fixed N 1

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Actual child Piola factors reduce to ordinary offset Jacobians and their inverses. -/

theorem weak_offsetJacobian_det_isUnit {g : ChainGeom} (hg : GeomSpatialSmooth g)
    (hi : ChainGeometry.InvLaw g) (u r : ℝ) (x : Vec 2) :
    IsUnit (jacMatrix (fun y => g.1 u y r) x).det := by
  have he : (fun y => g.1 r y u) ∘ (fun y => g.1 u y r) = id := by
    funext y
    exact hi r u y
  have hJ := CycleReference.jacMatrix_comp (f := fun y => g.1 r y u)
    (g := fun y => g.1 u y r) x ((hg r u).differentiable (by simp) _)
    ((hg u r).differentiable (by simp) _)
  rw [he, CycleReference.jacMatrix_identity] at hJ
  exact Matrix.isUnit_det_of_left_inverse hJ.symm

theorem weak_famJac_det_isUnit (D : OCData) (A : RealChain) (t : ℝ) :
    IsUnit (A.famJac D t).det :=
  weak_offsetJacobian_det_isUnit (geomSpatialSmooth_geom D A)
    (actualOffset_inverse_law D A) t (A.geom D).2.2 (A.geom D).2.1

theorem weak_childTransition_inverse_eq (D : OCData) (slot : ℤ) (t : ℝ)
    (A : RealChain) (z : Vec 2) :
    (childTransition D slot t A z)⁻¹ =
      (A.famJac D t)⁻¹ * (A.appendChild D slot t z).famJac D t := by
  unfold childTransition
  rw [Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (weak_famJac_det_isUnit D _ t)]

/-! Actual recentered metrics are smooth in slow labels and measurable in the cell clock. -/

theorem metric_recenter_formula (D : OCData) (A : RealChain)
    (hl : A.slots.length = A.children.length + 1) (u : ℝ) (h : Vec 2) :
    (A.recenter D h).famMetric D u =
      (jacMatrix (fun y => (A.geom D).1 u y (A.geom D).2.2) ((A.geom D).2.1 + h))⁻¹ *
        Matrix.transpose (jacMatrix (fun y => (A.geom D).1 u y (A.geom D).2.2)
          ((A.geom D).2.1 + h))⁻¹ := by
  unfold RealChain.famMetric RealChain.famJac
  rw [geom_recenter D A hl h]

theorem recentered_metric_entry_smooth (D : OCData) (A : RealChain)
    (hl : A.slots.length = A.children.length + 1) (ρ u : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun X => (A.recenter D (ρ • X)).famMetric D u i j) := by
  have hg := geomSpatialSmooth_geom D A
  have hi := actualOffset_inverse_law D A
  have hs (v w : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun X => (jacMatrix (fun y => (A.geom D).1 u y (A.geom D).2.2)
        ((A.geom D).2.1 + ρ • X))⁻¹ v w) :=
    (offsetJacobian_inverse_entry_smooth hg hi u (A.geom D).2.2 v w).comp
      (contDiff_const.add (contDiff_id.const_smul ρ))
  simp_rw [metric_recenter_formula D A hl u]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  exact ((hs i 0).mul (hs j 0)).add ((hs i 1).mul (hs j 1))

theorem recentered_metric_entry_continuous_time (D : OCData) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (h : Vec 2) (i j : Fin 2) :
    Continuous (fun u => (A.recenter D h).famMetric D u i j) := by
  have hc := geomC1_geom D hζ A
  have hi := actualOffset_inverse_law D A
  have hj := jac_continuous
    (f := fun u x => (A.geom D).1 u x (A.geom D).2.2)
    (hc (A.geom D).2.2) ((A.geom D).2.1 + h)
  have ha := continuous_inv_of_det hj
    (fun u => jac_isUnit_det hi hc u (A.geom D).2.2 ((A.geom D).2.1 + h))
  have he (v w : Fin 2) : Continuous (fun u =>
      (jacMatrix (fun y => (A.geom D).1 u y (A.geom D).2.2)
        ((A.geom D).2.1 + h))⁻¹ v w) :=
    (continuous_apply w).comp ((continuous_apply v).comp ha)
  simp_rw [metric_recenter_formula D A hl]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  exact ((he i 0).mul (he j 0)).add ((he i 1).mul (he j 1))

theorem familyLiftData_metric_entry_smooth {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (m : ℕ) (slot : ℤ) (A : RealChain)
    (hl : A.slots.length = A.children.length + 1) (ρ : ℝ)
    (edge : ConstituentEdges Dm h) (s : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun X => (familyLiftData D m slot A ρ edge).G s X i j) :=
  recentered_metric_entry_smooth D A hl ρ (D.cellScaleSq m * s) i j

theorem familyLiftData_metric_measurable {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (A : RealChain)
    (hl : A.slots.length = A.children.length + 1) (ρ : ℝ)
    (edge : ConstituentEdges Dm h) (X : Vec 2) (i j : Fin 2) :
    Measurable (fun s => (familyLiftData D m slot A ρ edge).G s X i j) :=
  ((recentered_metric_entry_continuous_time D hζ A hl (ρ • X) i j).comp
    (continuous_const.mul continuous_id)).measurable

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Genuine scalar lift coefficients give good and centered literal exponential test fields. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalarLiftTest_goodField (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (A : Vec 2 →L[ℝ] ℝ) (u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v w,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v w 1)) (t : ℝ) :
    GoodField H (liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u (1 : ℝ)) t) := by
  let Qs := fun v => normalizedScalarLiftTestReserve H n c A v u
    (fun m α w => Qc m α v w)
  let Qwhole := jointSourcePiReserve H
    (fun v t z Y => normalizedLiftTestField c n A u v 1 t Y z) Qs
  have hg := Qwhole.exponentialGoodField A t
  rw [normalizedLiftTestField_exp_cancel] at hg
  exact hg

theorem scalarLiftTest_centField (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (A : Vec 2 →L[ℝ] ℝ) (u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v w,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v w 1))
    (hmean : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ t Y v w ξ,
      fieldCellMean (fun z => c m α t Y z v w ξ) = 0) (t : ℝ) :
    CoefField True H (liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u (1 : ℝ)) t) := by
  let f : ℝ → Vec 2 → ι → ℝ := fun _ Y => Real.exp (A Y) • Pi.single u (1 : ℝ)
  let Φ : Vec 2 → Vec 2 → ι → ℝ := liftApply n c f t
  have hg : GoodField H Φ := scalarLiftTest_goodField H n c A u Qc t
  change CoefField True H Φ
  refine ⟨hg, ?_⟩
  intro _ Y
  funext v
  have hm : fieldCellMean (fun z => Φ Y z v) = 0 :=
    scalarLiftApply_component_mean_zero H n c f Qc hmean t Y v
  exact (fieldCellMean_pi_apply (Φ Y) (hg.continuous_slice Y) v).symm.trans hm

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Molecular ellipticity follows from a backward offset-flow Jacobian estimate. -/

theorem recentered_metric_ellipticity_of_backward_jacobian
    (D : OCData) (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (u : ℝ) (h : Vec 2)
    (hj : ∀ i j,
      |jacMatrix (fun y => (A.geom D).1 (A.geom D).2.2 y u)
        ((A.geom D).1 u ((A.geom D).2.1 + h) (A.geom D).2.2) i j -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 / 32) (ξ : Vec 2) :
    (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, (A.recenter D h).famMetric D u i j * ξ i * ξ j ∧
    ∑ i, ∑ j, (A.recenter D h).famMetric D u i j * ξ i * ξ j ≤
      (5 / 4) * ∑ i, ξ i ^ 2 := by
  rw [metric_recenter_formula D A hl u h]
  rw [offsetJacobian_inverse_eq (geomSpatialSmooth_geom D A)
    (actualOffset_inverse_law D A)]
  exact gram_close_ellipticity _ hj ξ

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The actual finite source vector has exactly the higher Sobolev energy pairing. -/

theorem molecularFiniteSource_energy_identity (N K : ℕ) (ρ : ℝ)
    (c : FiniteMolecularCoefficients N)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) (S : TorusHk K ℂ) :
    inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N Unit.unit K
        (plainSourceCoefficients N (fun _ : Unit => K) (fun _ => F) (fun _ => S))).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N Unit.unit K c).val) =
    inner ℝ (factorialWeightedJet ρ S.val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N Unit.unit K c).val) -
    inner ℝ (factorialWeightedJet ρ F.val)
      (factorialWeightedJet ρ (coupledPlainGradientHk N c Unit.unit K).val) := by
  rw [factorialWeightedJet_inner]
  have he (j : Fin (K + 1)) (w : DerivativeWord2 j.val) :=
    (plainEnergyTest_pairing (Nat.le_of_lt_succ j.isLt) N Unit.unit w c
      (plainSourceCoefficients N (fun _ : Unit => K) (fun _ => F) (fun _ => S))).symm.trans
        (plainSourceCoefficients_energy_pairing N (fun _ : Unit => K) Unit.unit
          (Nat.le_of_lt_succ j.isLt) w (fun _ => F) (fun _ => S) c)
  simp_rw [he, Finset.sum_sub_distrib, mul_sub]
  rw [Finset.sum_sub_distrib, ← factorialWeightedJet_inner]
  rw [plainFlux_factorial_pairing (h := fun _ : Unit => ℂ) N c Unit.unit K ρ F]

theorem molecularFiniteSource_energy_bound (N K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c : FiniteMolecularCoefficients N) (S : TorusHk K ℂ) :
    2 * inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N Unit.unit K (plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => dataFiniteFlux N K P t c)
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb c))).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N Unit.unit K c).val) +
      gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1) c).val ≤
    (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ^ 2) *
      factorialNormSq ρ (coupledPlainSynthesis N Unit.unit K c).val + factorialNormSq ρ S.val := by
  rw [molecularFiniteSource_energy_identity]
  have hsub : (S - dataFiniteTransport N K P t Cv hCv hv hp hb c).val =
    S.val - (dataFiniteTransport N K P t Cv hCv hv hp hb c).val := rfl
  rw [hsub]
  simp only [sub_eq_add_neg, factorialWeightedJet_add, factorialWeightedJet_neg,
    inner_add_left, inner_neg_left]
  rw [dataFiniteFlux, molecularMetric_factorial_pairing,
    ← coupledPlainGradientHk_factorialNormSq N c Unit.unit K ρ]
  have hh := dataHigher_spatial_energy_bound K ρ hρ P.G P.metric_coercive t (P.v t) Cv hCv hv hp hb
    (coupledPlainSynthesis N Unit.unit K c) S (coupledPlainGradientHk N c Unit.unit K)
  dsimp only [dataFiniteTransport]
  convert hh using 1; ring

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.CycleReference AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Spatial smoothness, periodicity, and the actual weak divergence identity for pulse drifts. -/

private theorem unitCosine_periodic (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun z : Vec 2 => Real.cos (2 * Real.pi * z i)) := by
  intro n z
  have he : 2 * Real.pi * (z + AVenhance.latticeShift n) i =
      2 * Real.pi * z i + (n i : ℝ) * (2 * Real.pi) := by
    simp only [Pi.add_apply, AVenhance.latticeShift]
    ring
  change Real.cos (2 * Real.pi * (z + AVenhance.latticeShift n) i) = _
  rw [he]
  exact Real.cos_add_int_mul_two_pi _ _

theorem normalizedPulseDrift_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : Odd k) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ocPulseCellDrift α q Λ ζ m ν k t) := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  rcases hk4 with h1 | h3
  · have he := funext (normalizedPulseDrift_horizontal (α := α) (q := q) (m := m) (ζ := ζ) hΛ hν h1 t)
    rw [he]
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (0 : ℝ))
      fun_prop
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)) * Real.cos (2 * Real.pi * x 0))
      fun_prop
  · have he := funext (normalizedPulseDrift_vertical (α := α) (q := q) (m := m) (ζ := ζ) hΛ hν h3 t)
    rw [he]
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => -((ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)) * Real.cos (2 * Real.pi * x 1)))
      fun_prop
    · change ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (0 : ℝ))
      fun_prop

theorem normalizedPulseDrift_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : Odd k) (t : ℝ) :
    AVenhance.IsZ2Periodic (ocPulseCellDrift α q Λ ζ m ν k t) := by
  intro n z
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  rcases hk4 with h1 | h3
  · rw [normalizedPulseDrift_horizontal hΛ hν h1, normalizedPulseDrift_horizontal hΛ hν h1,
      show Real.cos (2 * Real.pi * (z + AVenhance.latticeShift n) 0) =
        Real.cos (2 * Real.pi * z 0) from unitCosine_periodic 0 n z]
  · rw [normalizedPulseDrift_vertical hΛ hν h3, normalizedPulseDrift_vertical hΛ hν h3,
      show Real.cos (2 * Real.pi * (z + AVenhance.latticeShift n) 1) =
        Real.cos (2 * Real.pi * z 1) from unitCosine_periodic 1 n z]

theorem normalizedPulseDrift_divergence {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : Odd k) (t : ℝ)
    (ψ : TorusHkFunction 1 ℝ) :
    (∫ z in AVenhance.unitCube, ∑ i : Fin 2,
      ocPulseCellDrift α q Λ ζ m ν k t z i * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ z) = 0 := by
  apply classical_divergence_free_weak
  · intro i
    exact contDiff_pi.mp ((normalizedPulseDrift_contDiff hΛ hν hk t).of_le (by simp)) i
  · intro i n z
    exact congrArg (fun w : Vec 2 => w i) (normalizedPulseDrift_periodic hΛ hν hk t n z)
  · intro z
    have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
    rcases hk4 with h1 | h3
    · have he := funext (normalizedPulseDrift_horizontal (α := α) (q := q) (m := m) (ζ := ζ) hΛ hν h1 t)
      rw [he]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      simpa [AVenhance.spaceGrad] using
        AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate
          ((ocEpsilon q Λ m ^ (1 + α) / ν) *
            (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t))) (2 * Real.pi) 0 1 z
    · have he := funext (normalizedPulseDrift_vertical (α := α) (q := q) (m := m) (ζ := ζ) hΛ hν h3 t)
      rw [he]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      have hh := AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate
        (-((ocEpsilon q Λ m ^ (1 + α) / ν) *
          (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)))) (2 * Real.pi) 1 0 z
      simpa [AVenhance.spaceGrad, neg_mul] using hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Removing empty high-order sources preserves the original lift relation at its retained menu. -/

variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)]
  [∀ i, FiniteDimensional ℝ (hv i)] {D : ℕ}

theorem isLiftSequenceOn_restrict_effective_order (Ω : Set (Vec 2)) (K : ℕ) (hKD : K ≤ D)
    (Q : LiftOperatorData ι hv D) (hz : ∀ v u d, K < d.val → Q.edge v u d = [])
    (sX sZ N R : ℕ) (hNK : N ≤ K) (a b : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι hv)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N R Cc) :
    IsLiftSequenceOn Ω (restrictLiftData K hKD Q) sX sZ a b N R Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X hX
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X hX
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t _
  funext z
  exact congrFun (congrFun (liftCellSource_restrict_effective_order K hKD Q hz Cc
    (fun _ => f) hh n (hnN.trans hNK) t) X) z

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! Every actual odd normalized pulse satisfies the admissible cell drift predicate. -/

theorem normalizedPulseDrift_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) :
    Continuous (fun p : ℝ × Vec 2 => ocPulseCellDrift α q Λ ζ m ν k p.1 p.2) := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  have hp : Continuous (fun p : ℝ × Vec 2 => ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1)) :=
    (ocPulse_continuous hζ k).comp (by fun_prop)
  apply continuous_pi
  intro i
  rcases hk4 with h1 | h3
  · have he : (fun p : ℝ × Vec 2 => ocPulseCellDrift α q Λ ζ m ν k p.1 p.2 i) =
        fun p => (![0, (ocEpsilon q Λ m ^ (1 + α) / ν) *
          (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1)) *
            Real.cos (2 * Real.pi * p.2 0)] : Vec 2) i := by
      funext p
      rw [normalizedPulseDrift_horizontal hΛ hν h1]
    rw [he]
    fin_cases i
    · change Continuous (fun _ : ℝ × Vec 2 => (0 : ℝ))
      fun_prop
    · change Continuous (fun p : ℝ × Vec 2 => (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1)) * Real.cos (2 * Real.pi * p.2 0))
      fun_prop
  · have he : (fun p : ℝ × Vec 2 => ocPulseCellDrift α q Λ ζ m ν k p.1 p.2 i) =
        fun p => (![-((ocEpsilon q Λ m ^ (1 + α) / ν) *
          (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1)) *
            Real.cos (2 * Real.pi * p.2 1)), 0] : Vec 2) i := by
      funext p
      rw [normalizedPulseDrift_vertical hΛ hν h3]
    rw [he]
    fin_cases i
    · change Continuous (fun p : ℝ × Vec 2 => -((ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1)) * Real.cos (2 * Real.pi * p.2 1)))
      fun_prop
    · change Continuous (fun _ : ℝ × Vec 2 => (0 : ℝ))
      fun_prop

theorem normalizedPulseDrift_component_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν)
    {k : ℤ} (hk : Odd k) (t : ℝ) (i : Fin 2) :
    Continuous (fun z => ocPulseCellDrift α q Λ ζ m ν k t z i) := by
  exact continuous_pi_iff.mp (normalizedPulseDrift_contDiff hΛ hν hk t).continuous i

theorem normalizedPulseDrift_isCellDrift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) : IsCellDrift (ocPulseCellDrift α q Λ ζ m ν k) := by
  let B := (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg
      (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le)
      (by positivity)
  refine ⟨(normalizedPulseDrift_joint_continuous hΛ hν hζ hk).measurable,
    ⟨2 * B, ?_⟩, normalizedPulseDrift_periodic hΛ hν hk,
    normalizedPulseDrift_divergence hΛ hν hk⟩
  intro t z
  have hb (i : Fin 2) : (ocPulseCellDrift α q Λ ζ m ν k t z i) ^ 2 ≤ B ^ 2 := by
    have hh := (norm_le_pi_norm (ocPulseCellDrift α q Λ ζ m ν k t z) i).trans
      (normalizedPulseDrift_norm_le hΛ hν hζ hk t z)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [Fin.sum_univ_two]
  nlinarith [hb 0, hb 1, sq_nonneg B]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The full vector drift budget, needed by the lift setting, retains the same Pe factor. -/

theorem normalizedPulseDrift_vector_fast_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) (K n : ℕ) (hn : n ≤ K) (t : ℝ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (ocPulseCellDrift α q Λ ζ m ν k t) z‖ ≤
      (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant K := by
  have hPe : 0 ≤ ocEpsilon q Λ m ^ (1 + α) / ν := div_nonneg
    (Real.rpow_nonneg (AVRegularity.Construction.Stream.ocEpsilon_pos
      (q := q) (n := m) hΛ).le _) hν.le
  have hC := mul_nonneg hPe (pulseFastDerivativeConstant_nonneg K)
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro w
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))).mpr
  intro i
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hd : ContDiff ℝ (⊤ : ℕ∞) (ocPulseCellDrift α q Λ ζ m ν k t) :=
    normalizedPulseDrift_contDiff hΛ hν hk t
  have he := L.iteratedFDeriv_comp_left
    (hd.contDiffAt (x := z)) (by simp : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
  have hev := congrArg (fun F => F w) he
  change iteratedFDeriv ℝ n (fun y => ocPulseCellDrift α q Λ ζ m ν k t y i) z w =
    (iteratedFDeriv ℝ n (ocPulseCellDrift α q Λ ζ m ν k t) z w) i at hev
  rw [← hev]
  exact (ContinuousMultilinearMap.le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right (normalizedPulseDrift_fast_bound hΛ hν hζ hk K n hn t z i)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))

/-! The actual odd pulse points along its parallel coordinate. -/

def pulseParallel (k : ℤ) : Fin 2 := if k % 4 = 1 then 1 else 0

end AVRegularity.EntryWeakProofs
end
