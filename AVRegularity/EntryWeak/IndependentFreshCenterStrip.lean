-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentLiftFluxCrossAffine
import AVRegularity.EntryWeak.MolecularUlFluxNormBound
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Both parts of the first cross forcing retain the full independent parameter reserve. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentNormalizedCellB1Source (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → P → E) (t : ℝ) (z : Vec 2) (Y : P) : E :=
  (∑ i : Fin 2, (Real.sqrt η * v t z i) • independentSourceCovariantSlow L A i f t z Y) +
    (-Real.sqrt η) • (∑ p : Fin 2 × Fin 2,
      (G t Y p.1 p.2 • fderiv ℝ (fun y => independentSourceCovariantSlow L A p.2 f t y Y) z (basisVec p.1) +
        independentSourceCovariantSlow L A p.1
          (fun t z Y => G t Y p.1 p.2 • fderiv ℝ (fun y => f t y Y) z (basisVec p.2)) t z Y))

def independentNormalizedCellB1SourceReserve (H : ℕ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → P → E)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Qf : IndependentParameterSourceReserve (H + 2) f) :
    IndependentParameterSourceReserve H (independentNormalizedCellB1Source L A η G v f) := by
  let C := fun i => independentSourceCovariantSlow L A i f
  let QC := fun i => Qf.covariantSlow (H + 1) (by omega) L hL A i
  let Pp := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 •
    fderiv ℝ (fun y => f t y Y) z (basisVec p.2)
  let QP := fun p : Fin 2 × Fin 2 =>
    (QG p.1 p.2).scalarProduct (Qf.fastPartial (H + 1) (by omega) p.2)
  let D := fun (i : Fin 2) t z Y => (Real.sqrt η * v t z i) • C i t z Y
  let QD := fun i => ((Qv i).map (Real.sqrt η • ContinuousLinearMap.id ℝ ℝ)).scalarProduct
    ((QC i).restrictOrder H (by omega))
  let SD := IndependentParameterSourceReserve.fintypeSum H D QD
  let B := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 •
    fderiv ℝ (fun y => C p.2 t y Y) z (basisVec p.1) +
      independentSourceCovariantSlow L A p.1 (Pp p) t z Y
  let QB := fun p : Fin 2 × Fin 2 =>
    (((QG p.1 p.2).restrictOrder H (by omega)).scalarProduct
      ((QC p.2).fastPartial H (by omega) p.1)).add
      ((QP p).covariantSlow H (by omega) L hL A p.1)
  let SB := IndependentParameterSourceReserve.fintypeSum H B QB
  exact SD.add (SB.map ((-Real.sqrt η) • ContinuousLinearMap.id ℝ E))

theorem independent_normalized_cellB1_affine_slice (H : ℕ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → P → E)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : IndependentParameterSourceReserve (H + 2) f)
    (a : P) (t : ℝ) (z X : Vec 2) :
    normalizedCellB1Source A η (fun t X => G t (L X + a)) v
      (fun t z X => f t z (L X + a)) t z X =
      independentNormalizedCellB1Source L A η G v f t z (L X + a) := by
  let fs := fun t z X => f t z (L X + a)
  let Gs := fun t X => G t (L X + a)
  let Qfs := Qf.affineSlice L hL a
  let Ci := fun i => independentSourceCovariantSlow L A i f
  let QC := fun i => Qf.covariantSlow (H + 1) (by omega) L hL A i
  let Cs := fun i => sourceCovariantSlow A i fs
  let Pi := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 •
    fderiv ℝ (fun y => f t y Y) z (basisVec p.2)
  let QP := fun p : Fin 2 × Fin 2 =>
    (QG p.1 p.2).scalarProduct (Qf.fastPartial (H + 1) (by omega) p.2)
  let Ps := fun (p : Fin 2 × Fin 2) t z X => Gs t X p.1 p.2 •
    AVRegularity.fastPartial p.2 (fun X y => fs t y X) X z
  have heC i : Cs i = fun t z X => Ci i t z (L X + a) := by
    funext t z X
    exact independent_covariant_slow_affine_slice Qf (by omega) L A a i t z X
  have heP p : Ps p = fun t z X => Pi p t z (L X + a) := rfl
  have hds t z X : DifferentiableAt ℝ (fs t z) X :=
    (((Qfs.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hdf t X z : DifferentiableAt ℝ (fun y => fs t y X) z :=
    (((Qfs.regular t).comp₂ contDiff_id (contDiff_const (c := X))).differentiable (by simp)) z
  have hdC i t X z : DifferentiableAt ℝ (fun y => Cs i t y X) z := by
    rw [heC]
    exact (((((QC i).affineSlice L hL a).regular t).comp₂ contDiff_id
      (contDiff_const (c := X))).differentiable (by simp)) z
  have hdP p t z X : DifferentiableAt ℝ (Ps p t z) X := by
    rw [heP]
    exact (((((QP p).affineSlice L hL a).regular t).comp₂
      (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hslow i : AVRegularity.slowPartial i
      (fun X y => Real.exp (A X) • fs t y X) = fun X y => Real.exp (A X) • Cs i t y X := by
    funext X y
    exact slowPartial_exp_smul A i fs t y X (hds t y X)
  have hprod (p : Fin 2 × Fin 2) :
      (fun X y => Gs t X p.1 p.2 • AVRegularity.fastPartial p.2
        (fun Y w => Real.exp (A Y) • fs t w Y) X y) =
      fun X y => Real.exp (A X) • Ps p t y X := by
    funext X y
    rw [fastPartial_exp_smul A p.2 fs t y X (hdf t X y)]
    exact smul_comm _ _ _
  have hdrift i : (Real.exp (A X))⁻¹ • ((Real.sqrt η * v t z i) • AVRegularity.slowPartial i
      (fun X y => Real.exp (A X) • fs t y X) X z) =
      (Real.sqrt η * v t z i) • Ci i t z (L X + a) := by
    rw [smul_comm, normalized_slowPartial_exp_smul A i fs t z X (hds t z X)]
    change (Real.sqrt η * v t z i) • Cs i t z X = _
    rw [heC]
  have hcross (p : Fin 2 × Fin 2) :
      (Real.exp (A X))⁻¹ • (Gs t X p.1 p.2 • AVRegularity.fastPartial p.1
        (AVRegularity.slowPartial p.2 (fun X y => Real.exp (A X) • fs t y X)) X z +
        AVRegularity.slowPartial p.1 (fun X y => Gs t X p.1 p.2 •
          AVRegularity.fastPartial p.2 (fun X y => Real.exp (A X) • fs t y X) X y) X z) =
      G t (L X + a) p.1 p.2 • fderiv ℝ (fun y => Ci p.2 t y (L X + a)) z (basisVec p.1) +
        independentSourceCovariantSlow L A p.1 (Pi p) t z (L X + a) := by
    rw [smul_add, smul_comm, hslow, hprod,
      normalized_fastPartial_exp_smul A p.1 (Cs p.2) t z X (hdC p.2 t X z),
      normalized_slowPartial_exp_smul A p.1 (Ps p) t z X (hdP p t z X)]
    rw [heC, heP, independent_covariant_slow_affine_slice (QP p) (by omega) L A a p.1 t z X]
    rfl
  change (Real.exp (A X))⁻¹ • AVRegularity.cellB1 η Gs v t
    (fun X y => Real.exp (A X) • fs t y X) X z = _
  rw [AVRegularity.cellB1, sub_eq_add_neg, smul_add, smul_neg, ← neg_smul, smul_comm]
  simp only [Finset.smul_sum, independentNormalizedCellB1Source, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact hdrift i
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simpa only [neg_smul, smul_neg] using
      congrArg (fun e : E => (-Real.sqrt η) • e) (hcross (i, j))
end

/-! The second cross forcing spends intrinsic slow words within the full independent reserve. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentNormalizedCellB2Source (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → P → E)
    (t : ℝ) (z : Vec 2) (Y : P) : E :=
  (-η) • ∑ p : Fin 2 × Fin 2, independentSourceCovariantSlow L A p.1
    (fun t z Y => G t Y p.1 p.2 • independentSourceCovariantSlow L A p.2 f t z Y) t z Y

def independentNormalizedCellB2SourceReserve (H : ℕ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → P → E)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : IndependentParameterSourceReserve (H + 2) f) :
    IndependentParameterSourceReserve H (independentNormalizedCellB2Source L A η G f) := by
  let F := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 •
    independentSourceCovariantSlow L A p.2 f t z Y
  let QP := fun p : Fin 2 × Fin 2 => (QG p.1 p.2).scalarProduct
    (Qf.covariantSlow (H + 1) (by omega) L hL A p.2)
  let Q := IndependentParameterSourceReserve.fintypeSum H
    (fun p => independentSourceCovariantSlow L A p.1 (F p))
    (fun p => (QP p).covariantSlow H (by omega) L hL A p.1)
  exact Q.map ((-η) • ContinuousLinearMap.id ℝ E)

theorem independent_normalized_cellB2_affine_slice (H : ℕ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → P → E)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : IndependentParameterSourceReserve (H + 2) f)
    (a : P) (t : ℝ) (z X : Vec 2) :
    normalizedCellB2Source A η (fun t X => G t (L X + a))
      (fun t z X => f t z (L X + a)) t z X =
      independentNormalizedCellB2Source L A η G f t z (L X + a) := by
  let fs := fun t z X => f t z (L X + a)
  let Gs := fun t X => G t (L X + a)
  let Qfs := Qf.affineSlice L hL a
  let Ps := fun (p : Fin 2 × Fin 2) t z X => Gs t X p.1 p.2 • sourceCovariantSlow A p.2 fs t z X
  let Fi := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 • independentSourceCovariantSlow L A p.2 f t z Y
  let Qi := fun p : Fin 2 × Fin 2 => (QG p.1 p.2).scalarProduct
    (Qf.covariantSlow (H + 1) (by omega) L hL A p.2)
  have he p : Ps p = fun t z X => Fi p t z (L X + a) := by
    funext t z X
    dsimp only [Ps]
    rw [independent_covariant_slow_affine_slice Qf (by omega) L A a p.2 t z X]
  have hdf t z X : DifferentiableAt ℝ (fs t z) X :=
    (((Qfs.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hdp p t z X : DifferentiableAt ℝ (Ps p t z) X := by
    rw [he]
    exact (((((Qi p).affineSlice L hL a).regular t).comp₂
      (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hprod (p : Fin 2 × Fin 2) :
      (fun X y => Gs t X p.1 p.2 • AVRegularity.slowPartial p.2
        (fun Y w => Real.exp (A Y) • fs t w Y) X y) =
      fun X y => Real.exp (A X) • Ps p t y X := by
    funext X y
    rw [slowPartial_exp_smul A p.2 fs t y X (hdf t y X)]
    exact smul_comm _ _ _
  have ht p : (Real.exp (A X))⁻¹ • AVRegularity.slowPartial p.1
      (fun X y => Gs t X p.1 p.2 • AVRegularity.slowPartial p.2
        (fun X y => Real.exp (A X) • fs t y X) X y) X z =
      independentSourceCovariantSlow L A p.1 (Fi p) t z (L X + a) := by
    rw [hprod]
    rw [normalized_slowPartial_exp_smul A p.1 (Ps p) t z X (hdp p t z X), he p]
    exact independent_covariant_slow_affine_slice (Qi p) (by omega) L A a p.1 t z X
  change (Real.exp (A X))⁻¹ • AVRegularity.cellB2 η Gs t
    (fun Y y => Real.exp (A Y) • fs t y Y) X z = _
  rw [AVRegularity.cellB2, ← neg_smul, smul_comm]
  simp only [Finset.smul_sum, independentNormalizedCellB2Source, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun y : E => (-η) • y) (ht (i, j))
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Finite intrinsic slow words retain their single stored amplitude inside independent parameters. -/

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem IndependentParameterSourceReserve.covariantWord_budget_le {H : ℕ}
    {f : ℝ → Vec 2 → V → E} (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (n R : ℕ) (hNR : n + R ≤ H) (L : Vec 2 →L[ℝ] V) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (α : DerivativeWord2 n) (r : ℕ) (hr : r ≤ R) :
    (Q.covariantWord n R hNR L hL A α).budget r ≤ (1 + ‖A‖) ^ n * (θ * B) := by
  induction n generalizing R r with
  | zero =>
      change Q.budget r ≤ (1 + ‖A‖) ^ 0 * (θ * B)
      rw [pow_zero, one_mul]
      exact hQ r (by omega)
  | succ n ih =>
      let P := Q.covariantWord n (R + 1) (by omega) L hL A (fun i => α i.castSucc)
      change (P.covariantSlow R (by omega) L hL A (α (Fin.last n))).budget r ≤ _
      rw [IndependentParameterSourceReserve.covariantSlow_budget]
      have h1 : P.budget (1 + r) ≤ (1 + ‖A‖) ^ n * (θ * B) :=
        ih (R + 1) (by omega) (fun i => α i.castSucc) (1 + r) (by omega)
      have h0 : P.budget r ≤ (1 + ‖A‖) ^ n * (θ * B) :=
        ih (R + 1) (by omega) (fun i => α i.castSucc) r (by omega)
      have hm := mul_le_mul (covariant_scalar_map_norm_le (E := E) A (α (Fin.last n))) h0
        (P.budget_nonneg r) (norm_nonneg A)
      apply (add_le_add h1 hm).trans_eq
      rw [pow_succ]
      ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.EntryWeakProofs

/-! Windowing genuine independent sources preserves prices and centering and supplies past support. -/

variable {d H : ℕ}

def IndependentParameterSourceReserve.timeWindow
    {f : ℝ → Vec 2 → Vec d → ℝ} (Q : IndependentParameterSourceReserve H f)
    (I : Set ℝ) (hI : MeasurableSet I) :
    IndependentParameterSourceReserve H (independentTimeWindowSource I f) :=
  windowIndependentSourceReserve H I hI f (fun t _ => Q.regular t)
    (fun t _ => Q.periodic t) Q.measurable Q.budget Q.budget_nonneg
    (fun n hn t _ X => Q.derivative_bound n hn t X)

theorem IndependentParameterSourceReserve.timeWindow_budget
    {f : ℝ → Vec 2 → Vec d → ℝ} (Q : IndependentParameterSourceReserve H f)
    (I : Set ℝ) (hI : MeasurableSet I) (r : ℕ) :
    (Q.timeWindow I hI).budget r = Q.budget r := rfl

theorem independent_time_window_Ioc_past_zero {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Vec 2 → Vec d → E) (a b t : ℝ) (ht : t ≤ a) (z : Vec 2) (Y : Vec d) :
    independentTimeWindowSource (Set.Ioc a b) f t z Y = 0 := by
  exact ite_eq_right (fun h => (not_lt_of_ge ht) h.1)

theorem independent_time_window_Ioc_ae_eq {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Vec 2 → Vec d → E) (a b : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), independentTimeWindowSource (Set.Ioc a b) f t = f t := by
  filter_upwards [ae_restrict_of_ae (volume.ae_ne a), ae_restrict_mem measurableSet_Icc] with t hn ht
  have hi : t ∈ Set.Ioc a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
  funext z Y
  exact ite_eq_left hi

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Zero-start full planar production as a bounded measurable higher carrier. -/

theorem source_window_carrier_exists {a b : ℝ} (hab : a < b)
    {P : MolecularData} {K : ℕ} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData (Icc a b) K src flux)
    (V : MolecularFiniteDriftBudget P K)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∃ w : ℝ → TorusHk K ℂ, StronglyMeasurable w ∧
      (∀ t, ‖w t‖ ≤ fluxProductionConstant K * (Q.Ns + Q.Nf)) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue D t := by
  apply rawHigherWindowCarrier_exists hab.le D hD K
    (fluxProductionConstant K * (Q.Ns + Q.Nf))
  · exact mul_nonneg (fluxProductionConstant_nonneg K)
      (add_nonneg Q.scalar_budget_nonneg Q.flux_budget_nonneg)
  · exact Q.zero_production hab V D hD hi

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Strong induction produces every actual reserved coordinate-word inverse derivative. -/

variable {d H : ℕ}

theorem coordinate_word_inverse_family_derivatives (K : ℕ) (hK : K + 2 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y)) :
    ∀ w, w.length < K → ∀ Y i,
      Tendsto (fun h : ℝ => cellEnergyNorm univ
        (h⁻¹ • (c w (Y + h • basisVec i) - c w Y) - c (i :: w) Y))
        (𝓝[≠] 0) (𝓝 0) := by
  intro w hw
  generalize he : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    intro Y i
    apply coordinate_word_inverse_derivative_step K hK QG Qf QF hv c hsol w hw Y i
    intro p hp
    have hl := (independentWordForcing_lengths w p hp).2.2
    exact ih p.2.length (by omega) p.2 (by omega) rfl Y i

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The first independent forcing has no metric contribution for the initial constant test. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independentNormalizedCellB1Source_const
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : E) (t : ℝ) (z : Vec 2) (Y : P) :
    independentNormalizedCellB1Source L A η G v (fun _ _ _ => c) t z Y =
      ∑ i : Fin 2, (Real.sqrt η * v t z i) • (A (basisVec i) • c) := by
  simp only [independentNormalizedCellB1Source, independentSourceCovariantSlow,
    fderiv_const_apply, zero_apply, zero_add, smul_zero, add_zero, Finset.sum_const_zero]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Every produced coordinate-word inverse has zero initial data from the genuine source support. -/

variable {d H : ℕ}

theorem coordinate_word_inverse_past_zero (N : ℕ)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ N → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (a : ℝ) (hf : ∀ t, t ≤ a → ∀ z Y, f t z Y = 0)
    (hF : ∀ t, t ≤ a → ∀ z Y, F t z Y = 0) :
    ∀ Y w, w.length ≤ N → ∀ t, t ≤ a →
      cellValue (c w Y) t =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  intro Y
  apply independent_word_inverse_before_start_zero N (fun p => coordinateMetricWord G p Y)
    (fun w => coordinateSourceWord f w Y) (fun w => coordinateSourceWord F w Y) (fun w => c w Y)
    (by rw [coordinateMetricWord_nil]; exact QG.metric Y) hv
    (fun w hw => by rw [coordinateMetricWord_nil]; exact hsol Y w hw) a
  · intro w _
    apply ae_restrict_of_forall_mem measurableSet_Iic
    intro t ht
    exact Filter.Eventually.of_forall fun z => coordinate_source_word_zero t z (hf t ht z) w Y
  · intro w _
    apply ae_restrict_of_forall_mem measurableSet_Iic
    intro t ht
    exact Filter.Eventually.of_forall fun z => coordinate_source_word_zero t z (hF t ht z) w Y

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Finite norm jets in every independent real coordinate, produced from actual primitive reserves. -/

variable {d H : ℕ}

def IsCoordinateWordNormJetFamily {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : E → ℝ≥0∞) (K : ℕ) (J : List (Fin d) → Vec d → E) : Prop :=
  (∀ w, w.length ≤ K → ∀ Y, Tendsto (fun X => N (J w X - J w Y)) (𝓝 Y) (𝓝 0)) ∧
  ∀ w, w.length < K → ∀ Y i,
    Tendsto (fun h : ℝ => N (h⁻¹ • (J w (Y + h • basisVec i) - J w Y) - J (i :: w) Y))
      (𝓝[≠] 0) (𝓝 0)

theorem coordinate_word_inverse_norm_jet_family_exists (K : ℕ) (hK : K + 2 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) :
    ∃ c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ,
      IsCoordinateWordNormJetFamily (cellEnergyNorm univ) K c ∧
      ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
        (fun t => cellQ0 (coordinateSourceWord f w Y t))
        (coordinateSourceWord F w Y + independentWordMetricFlux
          (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y) := by
  obtain ⟨c, hc⟩ := coordinate_word_inverse_family_exists QG Qf QF hv
  have hsol Y w (hw : w.length ≤ K) := hc Y w (hw.trans (by omega : K ≤ H))
  exact ⟨c, ⟨coordinate_word_inverse_family_continuous K (by omega) QG Qf QF hv c hsol,
    coordinate_word_inverse_family_derivatives K hK QG Qf QF hv c hsol⟩, hsol⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The first diagonal drift forcing retains its genuine response amplitude in every family jet. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentFirstDriftReserve (H : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (v : ℝ → Vec 2 → Vec 2) (c : ℝ)
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i)) :
    IndependentParameterSourceReserve H
      (fun t z (_ : P) => ∑ i : Fin 2,
        ((A (basisVec i) * c) • ContinuousLinearMap.id ℝ ℝ) (v t z i)) :=
  IndependentParameterSourceReserve.fintypeSum H _
    (fun i => (Qv i).map ((A (basisVec i) * c) • ContinuousLinearMap.id ℝ ℝ))

theorem independentFirstDriftReserve_budget (H : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (v : ℝ → Vec 2 → Vec 2) (c θ B : ℝ)
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (hQ : ∀ i r, r ≤ H → (Qv i).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (independentFirstDriftReserve H A v c Qv).budget r ≤
      θ * (B * ∑ i : Fin 2, |A (basisVec i) * c|) := by
  rw [independentFirstDriftReserve, IndependentParameterSourceReserve.fintypeSum_budget]
  calc
    _ ≤ ∑ i : Fin 2, |A (basisVec i) * c| * (θ * B) := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(A (basisVec i) * c) • ContinuousLinearMap.id ℝ ℝ‖ * (Qv i).budget r ≤ _
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hQ i r hr) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent lift coefficients act on coarse fields by the literal finite intrinsic words. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentLiftApplySource (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → P → ι → ℝ) (v : ι)
    (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  ∑ m : Fin (n + 1), ∑ α : DerivativeWord2 m.val, ∑ u : ι,
    c m.val α t z Y v u • independentSourceCovariantWord L A
      (fun t _ Y => f t Y u) m.val α t z Y

def independentLiftApplySourceReserve (H n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (f : ℝ → P → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (Qf : ∀ u, IndependentParameterSourceReserve (H + n) (fun t _ Y => f t Y u)) :
    IndependentParameterSourceReserve H (independentLiftApplySource n c L A f v) :=
  IndependentParameterSourceReserve.fintypeSum H _ (fun m =>
    IndependentParameterSourceReserve.fintypeSum H _ (fun α =>
      IndependentParameterSourceReserve.fintypeSum H _ (fun u =>
        (Qc m α u).scalarProduct ((Qf u).covariantWord m.val H (by omega) L hL A α))))
end

/-! Independent left application agrees with actual lift coefficients wherever their values are identified. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ℕ}

theorem independent_lift_apply_affine_slice (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (C : LiftCoeff ι (fun _ => ℝ))
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (offset : P) (A : Vec 2 →L[ℝ] ℝ)
    (f : ℝ → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + n) (fun t _ Y => f t Y u))
    (v : ι) (t : ℝ) (z X : Vec 2)
    (hcopy : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      C m.val α t X z v u 1 = c m.val α t z (L X + offset) v u) :
    (Real.exp (A X))⁻¹ • liftApply n C
      (fun t X => Real.exp (A X) • f t (L X + offset)) t X z v =
      independentLiftApplySource n c L A f v t z (L X + offset) := by
  let Qs := fun u => (Qf u).affineSlice L hL offset
  let Qwhole := jointSourcePiReserve (H + n)
    (fun u t _ X => f t (L X + offset) u) Qs
  unfold liftApply independentLiftApplySource
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  have hreg : ContDiff ℝ (m.val : ℕ∞)
      (fun X => Real.exp (A X) • f t (L X + offset)) :=
    (Real.contDiff_exp.comp A.contDiff).smul
      (((Qwhole.regular t).comp₂ (contDiff_const (c := (0 : Vec 2))) contDiff_id).of_le
        (by exact_mod_cast (show m.val ≤ H + n by omega)))
  rw [ChartTransport.orderedDerivative_apply α hreg u X]
  simp only [Pi.smul_apply]
  have hd := orderedDerivative_exp_smul_covariantWord (Qs u) m.val (by omega) A α t z X
  rw [hd, map_smul, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hc (y : ℝ) : C m.val α t X z v u y = y • C m.val α t X z v u 1 := by
    simpa only [smul_eq_mul, mul_one] using (C m.val α t X z v u).map_smul y 1
  rw [hc, hcopy]
  rw [independent_covariant_word_affine_slice (Qf u) m.val (by omega) L hL A offset α t z X]
  exact mul_comm _ _
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The independent second cross forcing retains the same uniform finite cost and stored amplitude. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem independentNormalizedCellB2SourceReserve_uniform_budget (H : ℕ)
    (L : Vec 2 →L[ℝ] V) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → V → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → V → ℝ)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : IndependentParameterSourceReserve (H + 2) f)
    (θ BG BF : ℝ) (hθ : 0 ≤ θ) (hBG : 0 ≤ BG) (hBF : 0 ≤ BF)
    (hG : ∀ i j r, r ≤ H + 1 → (QG i j).budget r ≤ BG)
    (hf : ∀ r ≤ H + 2, Qf.budget r ≤ θ * BF) (r : ℕ) (hr : r ≤ H) :
    (independentNormalizedCellB2SourceReserve H L hL A η G f QG Qf).budget r ≤
      θ * normalizedCellB2UniformBudget H A η BG BF := by
  let CP := ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ (H + 1) * BG * ((1 + ‖A‖) * BF)
  let P := fun p : Fin 2 × Fin 2 =>
    (QG p.1 p.2).scalarProduct (Qf.covariantSlow (H + 1) (by omega) L hL A p.2)
  have hP (p : Fin 2 × Fin 2) (j : ℕ) (hj : j ≤ H + 1) :
      (P p).budget j ≤ θ * CP := by
    have hc := Qf.covariantSlow_uniform_budget θ BF hf (H + 1) (by omega) L hL A p.2
    have hb := (QG p.1 p.2).bilinear_budget_le
      (Qf.covariantSlow (H + 1) (by omega) L hL A p.2) (ContinuousLinearMap.lsmul ℝ ℝ)
      1 θ BG ((1 + ‖A‖) * BF) zero_le_one hBG
      (fun j hj => by simpa only [one_mul] using hG p.1 p.2 j hj) hc j hj
    rw [one_mul] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hθ
    dsimp only [CP]
    have hp : (2 : ℝ) ^ j ≤ 2 ^ (H + 1) := pow_le_pow_right₀ (by norm_num) hj
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)))) hBG)
      (mul_nonneg (add_nonneg zero_le_one (norm_nonneg A)) hBF)
  have hF (p : Fin 2 × Fin 2) :
      ((P p).covariantSlow H (by omega) L hL A p.1).budget r ≤ θ * ((1 + ‖A‖) * CP) :=
    (P p).covariantSlow_uniform_budget θ CP (hP p) H (by omega) L hL A p.1 r hr
  unfold independentNormalizedCellB2SourceReserve
  change ‖(-η) • ContinuousLinearMap.id ℝ ℝ‖ *
    (IndependentParameterSourceReserve.fintypeSum H _ (fun p : Fin 2 × Fin 2 =>
      (P p).covariantSlow H (by omega) L hL A p.1)).budget r ≤ _
  rw [IndependentParameterSourceReserve.fintypeSum_budget]
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hF p)
  apply (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold normalizedCellB2UniformBudget
  dsimp only [CP]
  ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The literal normalized exponential polynomial preserves genuine independent coefficient reserves. -/

variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]

def independentNormalizedLiftTestReserve (H n : ℕ)
    (c : P → LiftCoeff ι (fun _ => ℝ)) (x : P → Vec 2)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val,
      IndependentParameterSourceReserve H (fun t z Y => c Y m.val α t (x Y) z v u 1)) :
    IndependentParameterSourceReserve H
      (fun t z Y => normalizedLiftTestField (c Y) n A u v 1 t (x Y) z) := by
  let L := fun m (α : DerivativeWord2 m) =>
    ((List.ofFn α).map (fun j => A (basisVec j))).prod • ContinuousLinearMap.id ℝ ℝ
  let f := fun (m : Fin (n + 1)) (α : DerivativeWord2 m.val) t z Y =>
    L m.val α (c Y m.val α t (x Y) z v u 1)
  let Q := IndependentParameterSourceReserve.fintypeSum H
    (fun m t z Y => ∑ α : DerivativeWord2 m.val, f m α t z Y)
    (fun m => IndependentParameterSourceReserve.fintypeSum H (f m)
      (fun α => (Qc m α).map (L m.val α)))
  have he : (fun t z Y => ∑ m : Fin (n + 1), ∑ α : DerivativeWord2 m.val, f m α t z Y) =
      fun t z Y => normalizedLiftTestField (c Y) n A u v 1 t (x Y) z := by
    funext t z Y
    have hp := normalized_exponential_lift_polynomial n (c Y) A t (x Y) z v u 1 1
    simp only [one_smul, one_pow] at hp
    rw [← Fin.sum_univ_eq_sum_range] at hp
    exact hp.symm
  exact Q.congrSource he

theorem independentNormalizedLiftTestReserve_budget (H n : ℕ)
    (c : P → LiftCoeff ι (fun _ => ℝ)) (x : P → Vec 2)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val,
      IndependentParameterSourceReserve H (fun t z Y => c Y m.val α t (x Y) z v u 1)) (r : ℕ) :
    (independentNormalizedLiftTestReserve H n c x A v u Qc).budget r =
      ∑ m : Fin (n + 1), ∑ α : DerivativeWord2 m.val,
        ‖((List.ofFn α).map (fun j => A (basisVec j))).prod • ContinuousLinearMap.id ℝ ℝ‖ *
          (Qc m α).budget r := by
  unfold independentNormalizedLiftTestReserve
  rw [IndependentParameterSourceReserve.congrSource_budget,
    IndependentParameterSourceReserve.fintypeSum_budget]
  apply Finset.sum_congr rfl
  intro m _
  exact IndependentParameterSourceReserve.fintypeSum_budget H _ _ r

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Actual weak eddy coefficients have the exact dimensional amplitude of their response mean. -/

theorem actualWeakEddyFlux_fluxCoeff {Dm : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (hm : D.term < m) (slot : ℤ) (hslot : Odd slot) (A : RealChain)
    (ρ : ℝ) (hρ : 0 < ρ) (edge : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))
    (sX sZ N H : ℕ) (a b : ℝ) (Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hseq : IsLiftSequence (familyLiftData D m slot A ρ edge) sX sZ a b N H Cc)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (α : DerivativeWord2 (d - 1)) (t : ℝ) (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc a b)
    (y : Vec 2) :
    fluxCoeff (weakEddyFlux D m ρ (familyLiftData D m slot A ρ edge) Cc n t) d α y = fun k =>
      -(D.κ D.term * D.eps m ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ))) *
        fieldCellMean (fun z => ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) slot
          ((D.cellScaleSq m)⁻¹ * t) z k •
          Cc 0 (n - 1) (d - 1) α ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z 0 0 1) := by
  let Q := familyLiftData D m slot A ρ edge
  have hη : Q.η = 1 := weakData_family_contrast D hΛ hζ hκ m hm slot A ρ edge
  have hs : ∀ (β : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
      Cc 0 (n - 1) (d - 1) (β ∘ σ) = Cc 0 (n - 1) (d - 1) β :=
    fun β σ => hseq.2.2.2.2.1 0 (Nat.zero_le _) (n - 1) (d - 1) β σ
  have hv : ∀ k, Continuous (fun z => Real.sqrt Q.η * Q.v ((D.cellScaleSq m)⁻¹ * t) z k) := by
    intro k
    rw [hη, Real.sqrt_one]
    simp only [one_mul]
    exact normalizedPulseDrift_component_continuous hΛ (weakData_kap_pos D hΛ hζ hκ m)
      hslot ((D.cellScaleSq m)⁻¹ * t) k
  have hc : Continuous (fun z => fun v : Fin 1 =>
      Cc 0 (n - 1) (d - 1) α ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z v 0 1) := by
    apply continuous_pi
    intro v
    have hb := (hseq.2.2.2.2.2.1 0 (Nat.zero_le _) (n - 1) (d - 1) α v 0 _ ht).1
    exact (hb.1 (ρ⁻¹ • y)).continuous.clm_apply continuous_const
  rw [weakEddyFlux_fluxCoeff D m n d ρ hρ.ne' Q Cc (by omega) hs α t y hv hc]
  funext k
  rw [hη, Real.sqrt_one]
  simp only [one_mul, neg_mul]
  rw [weakData_flux_dimensional_count D hΛ hζ hκ m hm ρ hρ n d hn hd]
  rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Full independent physical flux cross terms retain each exact stored matrix amplitude. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independentLiftFluxCrossSourceReserve_uniform_budget (H : ℕ) (J : Vec 2 →L[ℝ] P) (hJ : ‖J‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → P → ℝ)
    (QG : ∀ i j, IndependentParameterSourceReserve H (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Q₁ : IndependentParameterSourceReserve (H + 1) f₁) (Q₂ : IndependentParameterSourceReserve (H + 1) f₂)
    (k : Fin 2) (θ BG BV BF₁ BF₂ : ℝ)
    (hθ : 0 ≤ θ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBF₁ : 0 ≤ BF₁) (hBF₂ : 0 ≤ BF₂)
    (hG : ∀ i j r, r ≤ H → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (h₁ : ∀ r ≤ H + 1, Q₁.budget r ≤ θ * BF₁)
    (h₂ : ∀ r ≤ H + 1, Q₂.budget r ≤ θ * BF₂) (r : ℕ) (hr : r ≤ H) :
    (independentLiftFluxCrossSourceReserve H J hJ A η G v f₁ f₂ QG Qv Q₁ Q₂ k).budget r ≤
      θ * normalizedLiftFluxCrossBudget H A η BG BV BF₁ BF₂ := by
  let T := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  let L : ℝ →L[ℝ] ℝ := Real.sqrt η • ContinuousLinearMap.id ℝ ℝ
  let LF : ℝ →L[ℝ] ℝ := (-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ
  let LS : ℝ →L[ℝ] ℝ := (-η) • ContinuousLinearMap.id ℝ ℝ
  let CD := ‖T‖ * 2 ^ H * (‖L‖ * BV) * BF₁
  let CF := ‖T‖ * 2 ^ H * BG * BF₁
  let CS := ‖T‖ * 2 ^ H * BG * ((1 + ‖A‖) * BF₂)
  let D := ((Qv k).map L).scalarProduct (Q₁.restrictOrder H (Nat.le_succ H))
  let F := fun j : Fin 2 => (QG k j).scalarProduct (Q₁.fastPartial H (by omega) j)
  let S := fun j : Fin 2 => (QG k j).scalarProduct (Q₂.covariantSlow H (by omega) J hJ A j)
  have hD : D.budget r ≤ θ * CD := by
    have h := ((Qv k).map L).bilinear_uniform_budget (Q₁.restrictOrder H (Nat.le_succ H)) T
      1 θ (‖L‖ * BV) BF₁ zero_le_one hθ (mul_nonneg (norm_nonneg L) hBV) hBF₁
      (fun j hj => by
        have hb := (Qv k).map_uniform_budget L 1 BV
          (fun l hl => by simpa only [one_mul] using hv k l hl)
        simpa only [one_mul] using hb j hj)
      (fun j hj => h₁ j (hj.trans (Nat.le_succ H))) r hr
    simpa only [one_mul, D, CD, T, IndependentParameterSourceReserve.scalarProduct] using h
  have hF j : (F j).budget r ≤ θ * CF := by
    have h := (QG k j).bilinear_uniform_budget (Q₁.fastPartial H (by omega) j) T
      1 θ BG BF₁ zero_le_one hθ hBG hBF₁
      (fun l hl => by simpa only [one_mul] using hG k j l hl)
      (Q₁.fastPartial_uniform_budget θ BF₁ h₁ H (by omega) j) r hr
    simpa only [one_mul, F, CF, T, IndependentParameterSourceReserve.scalarProduct] using h
  have hS j : (S j).budget r ≤ θ * CS := by
    have h := (QG k j).bilinear_uniform_budget (Q₂.covariantSlow H (by omega) J hJ A j) T
      1 θ BG ((1 + ‖A‖) * BF₂) zero_le_one hθ hBG
      (mul_nonneg (add_nonneg zero_le_one (norm_nonneg A)) hBF₂)
      (fun l hl => by simpa only [one_mul] using hG k j l hl)
      (Q₂.covariantSlow_uniform_budget θ BF₂ h₂ H (by omega) J hJ A j) r hr
    simpa only [one_mul, S, CS, T, IndependentParameterSourceReserve.scalarProduct] using h
  unfold independentLiftFluxCrossSourceReserve
  rw [IndependentParameterSourceReserve.congrSource_budget]
  change D.budget r + ‖LF‖ * (IndependentParameterSourceReserve.fintypeSum H _ F).budget r +
    ‖LS‖ * (IndependentParameterSourceReserve.fintypeSum H _ S).budget r ≤ _
  rw [IndependentParameterSourceReserve.fintypeSum_budget, IndependentParameterSourceReserve.fintypeSum_budget]
  have hFs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hF j)
  have hSs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hS j)
  apply (add_le_add (add_le_add hD (mul_le_mul_of_nonneg_left hFs (norm_nonneg LF)))
    (mul_le_mul_of_nonneg_left hSs (norm_nonneg LS))).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp only [normalizedLiftFluxCrossBudget, CD, CF, CS, T, L, LF, LS]
  ring

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! High regularity of the actual trace supplies a classical solution on the closed window. -/

theorem dataRegular_classical_solution {a b : ℝ} (P : MolecularData)
    (K r : ℕ) (hr : r + 2 ≤ K) (hr1 : 1 ≤ r)
    (src : ℝ → Vec 2 → ℂ)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (hu : Continuous u)
    (h : CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative P t
      (slice t) (cellSourceSlice src t)
      (fun j => cellSourceSlice (fun _ _ => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)))
    (hh : ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t)
    (hreal : ∀ t ∈ Icc a b, (fun x => ((u t x).re : ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] u t) :
    (∀ t, ContDiff ℝ (r : ℕ∞) (cellClassicalWindow a b u t)) ∧
    IsCellSolution (Icc a b) (dataCoefficients P) src (fun _ _ => 0)
      (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) (cellClassicalWindow a b u)) ∧
    (∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (cellClassicalWindow a b u t x : ℂ)) := by
  have hc := cellClassicalWindow_contDiff a b K r hr u hh hreal
  have he := cellClassicalWindow_value_ae a b K (by omega) u hh hreal
  refine ⟨hc, ?_, he⟩
  exact dataWeakHilbert_classical_solution P src (fun _ _ => 0) hsrc MemLp.zero
    u slice h (cellClassicalWindow a b u)
    (fun t => (hc t).of_le (by exact_mod_cast hr1))
    (cellClassicalWindow_periodic a b u) (cellClassicalWindow_measurable a b u hu) he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Independent first cross forcing keeps the same finite direction cost and stored amplitude. -/

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem independentNormalizedCellB1SourceReserve_uniform_budget (H : ℕ)
    (S : Vec 2 →L[ℝ] V) (hS : ‖S‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → V → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → V → ℝ)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : V) => v t z i))
    (Qf : IndependentParameterSourceReserve (H + 2) f)
    (θ BG BV BF : ℝ) (hθ : 0 ≤ θ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBF : 0 ≤ BF)
    (hG : ∀ i j r, r ≤ H + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (hf : ∀ r ≤ H + 2, Qf.budget r ≤ θ * BF) (r : ℕ) (hr : r ≤ H) :
    (independentNormalizedCellB1SourceReserve H S hS A η G v f QG Qv Qf).budget r ≤
      θ * normalizedCellB1UniformBudget H A η BG BV BF := by
  let T := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  let Ls : ℝ →L[ℝ] ℝ := Real.sqrt η • ContinuousLinearMap.id ℝ ℝ
  let L : ℝ →L[ℝ] ℝ := (-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ
  let QC := fun i : Fin 2 => Qf.covariantSlow (H + 1) (by omega) S hS A i
  let QP := fun p : Fin 2 × Fin 2 =>
    (QG p.1 p.2).scalarProduct (Qf.fastPartial (H + 1) (by omega) p.2)
  let QD := fun i : Fin 2 => ((Qv i).map Ls).scalarProduct ((QC i).restrictOrder H (by omega))
  let QB := fun p : Fin 2 × Fin 2 =>
    (((QG p.1 p.2).restrictOrder H (by omega)).scalarProduct ((QC p.2).fastPartial H (by omega) p.1)).add
      ((QP p).covariantSlow H (by omega) S hS A p.1)
  let CC := (1 + ‖A‖) * BF
  let CP := ‖T‖ * 2 ^ (H + 1) * BG * BF
  let CD := ‖T‖ * 2 ^ H * (‖Ls‖ * BV) * CC
  let CB := ‖T‖ * 2 ^ H * BG * CC + (1 + ‖A‖) * CP
  have hCC : 0 ≤ CC := mul_nonneg (add_nonneg zero_le_one (norm_nonneg A)) hBF
  have hQC (i : Fin 2) (j : ℕ) (hj : j ≤ H + 1) : (QC i).budget j ≤ θ * CC :=
    Qf.covariantSlow_uniform_budget θ BF hf (H + 1) (by omega) S hS A i j hj
  have hQP (p : Fin 2 × Fin 2) (j : ℕ) (hj : j ≤ H + 1) : (QP p).budget j ≤ θ * CP := by
    have h := (QG p.1 p.2).bilinear_uniform_budget
      (Qf.fastPartial (H + 1) (by omega) p.2) T 1 θ BG BF zero_le_one hθ hBG hBF
      (fun j hj => by simpa only [one_mul] using hG p.1 p.2 j hj)
      (Qf.fastPartial_uniform_budget θ BF hf (H + 1) (by omega) p.2) j hj
    rw [one_mul] at h
    change (QP p).budget j ≤ θ * CP at h
    exact h
  have hQD (i : Fin 2) : (QD i).budget r ≤ θ * CD := by
    have h := ((Qv i).map Ls).bilinear_uniform_budget ((QC i).restrictOrder H (by omega))
      T 1 θ (‖Ls‖ * BV) CC zero_le_one hθ (mul_nonneg (norm_nonneg _) hBV) hCC
      (fun j hj => by simpa only [one_mul] using
        (Qv i).map_uniform_budget Ls 1 BV (fun j hj => by simpa only [one_mul] using hv i j hj) j hj)
      (fun j hj => hQC i j (by omega)) r hr
    rw [one_mul] at h
    change (QD i).budget r ≤ θ * CD at h
    exact h
  have hQB (p : Fin 2 × Fin 2) : (QB p).budget r ≤ θ * CB := by
    have h1 := ((QG p.1 p.2).restrictOrder H (by omega)).bilinear_uniform_budget
      ((QC p.2).fastPartial H (by omega) p.1) T 1 θ BG CC zero_le_one hθ hBG hCC
      (fun j hj => by
        change (QG p.1 p.2).budget j ≤ 1 * BG
        rw [one_mul]
        exact hG p.1 p.2 j (by omega))
      ((QC p.2).fastPartial_uniform_budget θ CC (hQC p.2) H (by omega) p.1) r hr
    rw [one_mul] at h1
    have h2 := (QP p).covariantSlow_uniform_budget θ CP (hQP p) H (by omega) S hS A p.1 r hr
    exact (add_le_add h1 h2).trans_eq (mul_add θ _ _).symm
  unfold independentNormalizedCellB1SourceReserve
  change (IndependentParameterSourceReserve.fintypeSum H _ QD).budget r +
    ‖L‖ * (IndependentParameterSourceReserve.fintypeSum H _ QB).budget r ≤ _
  rw [IndependentParameterSourceReserve.fintypeSum_budget, IndependentParameterSourceReserve.fintypeSum_budget]
  have hsD := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hQD i)
  have hsB := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hQB p)
  apply (add_le_add hsD (mul_le_mul_of_nonneg_left hsB (norm_nonneg L))).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold normalizedCellB1UniformBudget
  dsimp only [T, L, Ls, CD, CB, CP, CC]
  ring
end

/-! Centered chart values are controlled by derivatives on their native segment. -/

theorem centeredGeometryChart_zero (g : ChainGeom) (ρ u : ℝ) :
    centeredGeometryChart g ρ u 0 = 0 := by
  simp only [centeredGeometryChart, smul_zero, add_zero, sub_self]

/-! Fresh independent chain parameters retain an arbitrary fixed older history. -/

/-- Only the new children vary; the older real chain is a discrete input. -/
def independentFreshChain {r : ℕ} (A : RealChain) (slots : Fin r → ℤ)
    (birthLength : Fin r → ℝ) (Y : Vec (4 * r)) : RealChain :=
  { A with
    slots := A.slots ++ List.ofFn slots
    children := A.children ++ List.ofFn (fun j => independentFreshChild birthLength j Y) }

theorem independentFreshChain_wellSlotted {r : ℕ} (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (Y : Vec (4 * r)) :
    (independentFreshChain A slots birthLength Y).WellSlotted := by
  change (A.slots ++ List.ofFn slots).length =
    (A.children ++ List.ofFn (fun j => independentFreshChild birthLength j Y)).length + 1
  simp only [List.length_append, List.length_ofFn]
  change A.slots.length = A.children.length + 1 at hA
  omega

theorem independentFreshChain_ctxLevel {r : ℕ} (A : RealChain) (slots : Fin r → ℤ)
    (birthLength : Fin r → ℝ) (Y : Vec (4 * r)) :
    (independentFreshChain A slots birthLength Y).ctxLevel = A.ctxLevel + r := by
  simp only [independentFreshChain, RealChain.ctxLevel, RealChain.lastLevel,
    List.length_append, List.length_ofFn]
  omega

theorem independentFreshChain_reconstruct {r : ℕ} (A : RealChain) (slots : Fin r → ℤ)
    (birthLength : Fin r → ℝ) (hbirth : ∀ j, birthLength j ≠ 0) (c : Fin r → ChainChild) :
    independentFreshChain A slots birthLength (independentFreshChildPacking birthLength c) =
      { A with slots := A.slots ++ List.ofFn slots, children := A.children ++ List.ofFn c } := by
  have he : (fun j => independentFreshChild birthLength j
      (independentFreshChildPacking birthLength c)) = c := by
    funext j
    exact independentFreshChildPacking_reconstruct birthLength hbirth c j
  unfold independentFreshChain
  rw [he]

/-! Every indexed child center of a fresh family is a constant or linear coordinate. -/

theorem independentFreshChain_child_getD_center_contDiff {r : ℕ} (A : RealChain)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun P : Vec (4 * r) =>
      ((independentFreshChain A slots birthLength P).children.getD j ⟨0, 0⟩).center) := by
  by_cases hj : j < A.children.length
  · have he : (fun P : Vec (4 * r) =>
        ((independentFreshChain A slots birthLength P).children.getD j ⟨0, 0⟩).center) =
        fun _ => (A.children.getD j ⟨0, 0⟩).center := by
      funext P
      exact congrArg ChainChild.center (List.getD_append _ _ _ _ hj)
    rw [he]
    exact contDiff_const
  · have hp : A.children.length ≤ j := Nat.le_of_not_gt hj
    simp only [independentFreshChain, List.getD_append_right _ _ _ _ hp]
    by_cases hn : j - A.children.length < r
    · have he : (fun P : Vec (4 * r) =>
          ((List.ofFn (fun k : Fin r => independentFreshChild birthLength k P)).getD
            (j - A.children.length) ⟨0, 0⟩).center) =
          fun P => birthLength ⟨j - A.children.length, hn⟩ •
            independentFreshChildProjection ⟨j - A.children.length, hn⟩ false P := by
        funext P
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hn)]
        simp only [List.getElem_ofFn, independentFreshChild_center]
      rw [he]
      exact (independentFreshChildProjection ⟨j - A.children.length, hn⟩ false).contDiff.const_smul _
    · have he : (fun P : Vec (4 * r) =>
          ((List.ofFn (fun k : Fin r => independentFreshChild birthLength k P)).getD
            (j - A.children.length) ⟨0, 0⟩).center) = fun _ => (0 : Vec 2) := by
        funext P
        rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hn)]
      rw [he]
      exact contDiff_const

/-! A depth equality only changes coordinate indices, preserving every literal reconstructed child. -/

theorem independentFreshChild_ofFn_cast (r s : ℕ) (hrs : r = s)
    (birth : Fin r → ℝ) (birth' : Fin s → ℝ)
    (hb : ∀ j, birth j = birth' (Fin.cast hrs j)) (P : Vec (4 * r)) :
    List.ofFn (fun j => independentFreshChild birth j P) =
      List.ofFn (fun j => independentFreshChild birth' j (hrs ▸ P)) := by
  subst s
  have he : birth = birth' := funext hb
  rw [he]

/-! Prefix projections separate the last fresh child without enlarging the parameter norm. -/

def independentFreshPrefixProjection (r : ℕ) : Vec (4 * (r + 1)) →L[ℝ] Vec (4 * r) :=
  ContinuousLinearMap.pi (fun k => ContinuousLinearMap.proj (Fin.castLE (by omega) k))

theorem independentFreshPrefixProjection_apply (r : ℕ) (Y : Vec (4 * (r + 1))) (k : Fin (4 * r)) :
    independentFreshPrefixProjection r Y k = Y (Fin.castLE (by omega) k) := rfl

theorem independentFreshPrefixProjection_norm_le (r : ℕ) :
    ‖independentFreshPrefixProjection r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
  intro k
  exact norm_le_pi_norm Y (Fin.castLE (by omega) k)

theorem independentFreshPrefixProjection_component {r : ℕ} (j : Fin r) (phase : Bool)
    (Y : Vec (4 * (r + 1))) :
    independentFreshChildProjection j phase (independentFreshPrefixProjection r Y) =
      independentFreshChildProjection j.castSucc phase Y := rfl

theorem independentFreshPrefixProjection_child {r : ℕ} (birthLength : Fin (r + 1) → ℝ)
    (j : Fin r) (Y : Vec (4 * (r + 1))) :
    independentFreshChild (fun i => birthLength i.castSucc) j (independentFreshPrefixProjection r Y) =
      independentFreshChild birthLength j.castSucc Y := rfl

/-! Identical literal family geometries have identical recentered molecular metrics. -/

theorem realChain_recenter_geom_eq_of_geom_eq (D : OCData) (A B : RealChain)
    (hA : A.WellSlotted) (hB : B.WellSlotted) (hg : A.geom D = B.geom D) (h : Vec 2) :
    (A.recenter D h).geom D = (B.recenter D h).geom D := by
  rw [geom_recenter D A hA h, geom_recenter D B hB h, hg]

theorem realChain_recenter_metric_eq_of_geom_eq (D : OCData) (A B : RealChain)
    (hA : A.WellSlotted) (hB : B.WellSlotted) (hg : A.geom D = B.geom D) (h : Vec 2) (u : ℝ) :
    (A.recenter D h).famMetric D u = (B.recenter D h).famMetric D u := by
  unfold RealChain.famMetric RealChain.famJac
  rw [realChain_recenter_geom_eq_of_geom_eq D A B hA hB hg h]

/-! The independent center strip bounds centers while leaving every phase unrestricted. -/

def independentFreshCenterStrip {r : ℕ} (Y : Vec (4 * r)) : Prop :=
  ∀ j : Fin r, ‖independentFreshChildProjection j false Y‖ ≤ 1

theorem independentFreshCenterStrip_prefix {r : ℕ} (Y : Vec (4 * (r + 1)))
    (hY : independentFreshCenterStrip Y) :
    independentFreshCenterStrip (independentFreshPrefixProjection r Y) := by
  intro j
  rw [independentFreshPrefixProjection_component]
  exact hY j.castSucc

theorem independentFreshCenterStrip_last {r : ℕ} (Y : Vec (4 * (r + 1)))
    (hY : independentFreshCenterStrip Y) :
    ‖independentFreshChildProjection (Fin.last r) false Y‖ ≤ 1 := hY _

end AVRegularity.EntryWeakProofs
end
