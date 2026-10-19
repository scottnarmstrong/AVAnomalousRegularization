-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.AmbientPairedCoefficientDataOfTests
public import AVRegularity.EntryWeak.NormalizedSourceFluxMatrixReserve
import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy
import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Full source-flux mean arrays preserve genuine coefficient germs on an open carrier. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {D : ℕ} {U : Set (Vec 2)}

theorem sourceFluxMeanCoefficient_slow_local_congr (hU : IsOpen U)
    (edge : ConstituentEdges D hv) (η t : ℝ) (n : ℕ) (c d : ℕ → LiftCoeff ι hv)
    (he : ∀ q ≤ n, ∀ m ≤ q, ∀ α X, X ∈ U → ∀ z v u,
      c q m α t X z v u = d q m α t X z v u)
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (X : Vec 2) (hX : X ∈ U)
    (z : Vec 2) (v u : ι) :
    sourceFluxMeanCoefficient edge η t n c k m α t X z v u =
      sourceFluxMeanCoefficient edge η t n d k m α t X z v u := by
  apply leftTermsMeanBlockCoefficient_slow_local_congr _ _ ?_ m α t X hX z v u
  intro v
  unfold sourceFluxConvolutionLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro j _
  exact sourceFluxLeftTerms_slow_local_congr hU edge η t (n - j) (c (n - j)) (d (n - j)) k j v
    (he (n - j) (Nat.sub_le n j))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The higher carrier is the metric perturbation flux of the original raw solution. -/

theorem metricGradientCarrier_raw_flux_ae (K : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (w : TorusHk (K + 1) ℂ) (D : RawJet2 1 ℂ) (hD : HasPeriodicOrderedWeakJet D)
    (hw : torusHkValueCLM w =ᵐ[volume.restrict AVenhance.unitCube] D (valueIndex2 1)) :
    torusHkValueCLM (metricGradientCarrier K A w) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => cellMetricFluxVector A (cellGradient D x) := by
  exact (metricGradientCarrier_value_ae K A w).trans
    ((higherTrace_gradient_ae K w D hD hw).fun_comp (cellMetricFluxVector A))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Tags and the effective finite degree cap hold at every stage, including the empty root. -/

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : ℕ → GenStage D (fun _ => ℝ) Dm bw j₀}

theorem weakConstruction_stage_hasTags (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (hc : IsWeakConstruction D P Mn M J rW r G)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) : (G i).HasTags P := by
  by_cases he : i = M + J
  · subst i
    intro v u γ
    let := hc.2.1.2.2.1 v u
    exact isEmptyElim γ
  · have hp := (hc.2.2 (i + 1) (by omega) (by omega)).2
    simpa only [Nat.add_sub_cancel] using hp

theorem weakConstruction_stage_maxOrderBound (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (hc : IsWeakConstruction D P Mn M J rW r G)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) :
    (G i).maxOrderBound (1 + J * Mn.N) := by
  by_cases he : i = M + J
  · subst i
    intro v u γ
    let := hc.2.1.2.2.1 v u
    exact isEmptyElim γ
  · exact weakConstruction_output_maxOrder_bound P Mn M J rW r G hc i hi (by omega)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Native source means read only constituent germs inside the admissible carrier. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)]
  {D : ℕ} {U : Set (Vec 2)}

omit [DecidableEq ι] in
theorem sourceFluxLeftTerms_slow_local_edge_congr (hU : IsOpen U)
    (edge edge' : ConstituentEdges D hv) (η t : ℝ) (n : ℕ)
    (c d : LiftCoeff ι hv) (k : Fin 2) (j : ℕ) (v : ι)
    (hΓ : SlowOpenEdgeEq U t edge edge')
    (he : ∀ m ≤ n, ∀ α X, X ∈ U → ∀ z u u',
      c m α t X z u u' = d m α t X z u u') :
    List.Forall₂ (LeftTermSlowEq U) (sourceFluxLeftTerms edge η t n c k j v)
      (sourceFluxLeftTerms edge' η t n d k j v) := by
  unfold sourceFluxLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro u _
  apply leftTermSlowEq_flatMap_same
  intro e _
  apply List.rel_flatMap (hΓ v u e)
  intro γ γ' hγ
  apply leftTermSlowEq_flatMap_same
  intro α _
  exact constituentLeftTerms_slow_local_replacement hU η (List.ofFn α) j _ _
    (liftComponentLeftTerms_slow_local_congr n c d t u
      (fun m hm α X hX z u' => he m hm α X hX z u u'))
    γ.map γ'.map hγ.1 (fun X z => γ.coeff α t X z k)
    (fun X z => γ'.coeff α t X z k)
    (fun X hX z => congrFun (hγ.2 α X hX z) k)

theorem sourceFluxMeanCoefficient_slow_local_edge_congr (hU : IsOpen U)
    (edge edge' : ConstituentEdges D hv) (η t : ℝ) (n : ℕ)
    (c d : ℕ → LiftCoeff ι hv) (hΓ : SlowOpenEdgeEq U t edge edge')
    (he : ∀ q ≤ n, ∀ m ≤ q, ∀ α X, X ∈ U → ∀ z v u,
      c q m α t X z v u = d q m α t X z v u)
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (X : Vec 2) (hX : X ∈ U)
    (z : Vec 2) (v u : ι) :
    sourceFluxMeanCoefficient edge η t n c k m α t X z v u =
      sourceFluxMeanCoefficient edge' η t n d k m α t X z v u := by
  apply leftTermsMeanBlockCoefficient_slow_local_congr _ _ ?_ m α t X hX z v u
  intro v
  unfold sourceFluxConvolutionLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro j _
  exact sourceFluxLeftTerms_slow_local_edge_congr hU edge edge' η t
    (n - j) (c (n - j)) (d (n - j)) k j v hΓ (he (n - j) (Nat.sub_le n j))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Weak chart thresholds are fixed from the menu and scale parameters before the actual data. -/

theorem uniform_finite_weak_chart_eventually_close (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ base ≥ M, ∀ (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild),
      (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (base + 1 + n) (p (n + 1)) (p n)) →
      ∀ n ≤ J, ∀ u r,
        |u - D.slotAnchor (base + 1 + n) (p n)| ≤
          finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
        |r - D.slotAnchor (base + 1 + n) (p n)| ≤
          finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
        ∀ x, ‖fderiv ℝ (fun y => (finiteWeakChainGeom D base Y p c n).1 u y r) x -
          ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 / 32 := by
  obtain ⟨δ, hδ, _, hbδ⟩ := finiteChartBudget_small J
  obtain ⟨M, hM, hprim⟩ := weak_finite_chart_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq
    Λ hΛ (2 * (J : ℝ) + 1) δ (by positivity) hδ
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq
  have hα₀' : 0 < D.α := by rw [hDα]; exact hα₀
  have hα₁' : D.α < 1 / 3 := by rw [hDα]; exact hα₁
  have hs₁' : s < (1 - D.α) / 2 := by rw [hDα]; exact hs₁
  have hq' : IsAdmissibleQ D.α s D.q := by rw [hDα, hDq]; exact hq
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hseq' : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by
    rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  have hprim' : ∀ m ≥ M,
      2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m ≤
        (2 : ℝ) ^ (-25 : ℤ) * (ocA D.α D.q D.Λ (m - 1))⁻¹ ∧
      2 ^ 23 * (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m) *
        ocA D.α D.q D.Λ (m - 1) ≤ δ ∧
      (4 * Real.pi ^ 2) * (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m) *
        ocA D.α D.q D.Λ (m - 1) ≤ δ := by
    rw [hDα, hDq, hDΛ]
    exact hprim
  intro base hbase Y p c hp hs n hn u r hu hr x
  have hprimitive : WeakPrimitiveChartSmall D base J δ :=
    fun m hm => hprim' m (by omega)
  have hb := finite_weak_chart_bound_of_small_windows D s hα₀' hα₁' hs₀ hs₁' hq' hΛ' hζ' hseq'
    base J (by omega) Y p c hp hs δ hprimitive n hn u r hu hr x
  exact hb.trans ((finiteChartBudget_mono_order hδ.le hn).trans hbδ)


theorem uniform_finite_weak_chart_eventually_bounded_jets (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J K : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ base ≥ M, ∀ (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild),
      (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (base + 1 + n) (p (n + 1)) (p n)) →
      ∀ ρ, 0 < ρ → ρ ≤ D.eps (base + J) → ∀ n ≤ J, ∀ u r,
        |u - D.slotAnchor (base + 1 + n) (p n)| ≤
          finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
        |r - D.slotAnchor (base + 1 + n) (p n)| ≤
          finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
        ∀ a, 1 ≤ a → a ≤ K → ∀ x,
          ‖iteratedFDeriv ℝ a (rescaledChart ρ (fun y =>
            (finiteWeakChainGeom D base Y p c n).1 u y r)) x‖ ≤ weakChartJetBudget K n := by
  obtain ⟨M, hM, hprim⟩ := weak_finite_chart_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq
    Λ hΛ (2 * (J : ℝ) + 1) 1 (by positivity) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq
  have hα₀' : 0 < D.α := by rw [hDα]; exact hα₀
  have hα₁' : D.α < 1 / 3 := by rw [hDα]; exact hα₁
  have hs₁' : s < (1 - D.α) / 2 := by rw [hDα]; exact hs₁
  have hq' : IsAdmissibleQ D.α s D.q := by rw [hDα, hDq]; exact hq
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hseq' : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by
    rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  have hprim' : ∀ m ≥ M,
      2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m ≤
        (2 : ℝ) ^ (-25 : ℤ) * (ocA D.α D.q D.Λ (m - 1))⁻¹ ∧
      2 ^ 23 * (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m) *
        ocA D.α D.q D.Λ (m - 1) ≤ 1 ∧
      (4 * Real.pi ^ 2) * (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m) *
        ocA D.α D.q D.Λ (m - 1) ≤ 1 := by
    rw [hDα, hDq, hDΛ]
    exact hprim
  intro base hbase Y p c hp hs ρ hρ hρe
  exact finite_weak_chart_jets_of_small_windows D s hα₀' hα₁' hs₀ hs₁' hq' hΛ' hζ' hseq'
    base J (by omega) Y p c hp hs K ρ hρ hρe (fun m hm => hprim' m (by omega))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

/-! Unit-determinant planar inverse Gram matrices are smooth without reciprocal determinant estimates. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem planar_inverse_gram_contDiff (J : P → Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (hdet : ∀ Z, (J Z).det = 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Z => (J Z)⁻¹ * Matrix.transpose (J Z)⁻¹) := by
  have hs i j : ContDiff ℝ (⊤ : ℕ∞) (fun Z => (J Z)⁻¹ i j) := by
    have he : (fun Z => (J Z)⁻¹ i j) = fun Z => (if i = j then 1 else -1) * J Z j.rev i.rev :=
      funext (fun Z => planar_inverse_entry_formula (J Z) (hdet Z) i j)
    rw [he]
    exact contDiff_const.mul ((contDiff_apply_apply ℝ ℝ j.rev i.rev).comp hJ)
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  exact ((hs i 0).mul (hs j 0)).add ((hs i 1).mul (hs j 1))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The path-matrix endpoint is the literal witness stored in the weak inherited provenance. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def stagePathStoredWeight (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h)
    (j : ℕ) : ℝ :=
  if hj : j < h then (G.fam.identity _ _ (π.step ⟨j, hj⟩).2.2).record.size else 0

theorem stagePathStoredWeight_nonneg (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (j : ℕ) : 0 ≤ stagePathStoredWeight G π j := by
  unfold stagePathStoredWeight
  split
  · exact (G.fam.identity _ _ (π.step _).2.2).record.size_nonneg
  · exact le_refl _

theorem stagePathStoredMatrix_nonneg (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (v u : Fin (h + 1)) :
    0 ≤ weightedPathMatrix h (stagePathStoredWeight G π) v u := by
  unfold weightedPathMatrix
  split_ifs
  · exact stagePathStoredWeight_nonneg G π _
  · exact le_refl _

theorem stagePathStoredMatrix_endpoint (G : GenStage D hr Dm b j₀)
    (P : ProvParams) (ht : G.HasTags P) {h : ℕ} (π : StagePath G h) :
    finiteMatrixPower (weightedPathMatrix h (stagePathStoredWeight G π)) h
      ⟨h, by omega⟩ 0 = (π.provList.map (fun x => (x.2.2.tags P).witness)).prod := by
  rw [weightedPathMatrix_power_column_zero]
  simp only [ite_true]
  rw [← Fin.prod_univ_eq_prod_range, stagePath_stored_witness_product G P ht π]
  apply Finset.prod_congr rfl
  intro j _
  simp only [stagePathStoredWeight, dite_eq_left j.isLt]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The literal centered lift recurrence retains the genuine reserves of its lower-degree terms. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftASource (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (z Y : Vec 2) : ι → ℝ :=
  (Real.exp (A Y))⁻¹ • liftA Q Cc f hh n t Y z

def normalizedLiftCellSource (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (z Y : Vec 2) : ι → ℝ :=
  (Real.exp (A Y))⁻¹ • liftCellSource Q Cc f hh n t Y z

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The terminal diffusivity supplies the actual weak molecular contrast and a positive cell clock. -/

theorem weakData_kap_pos (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) : 0 < D.kap m :=
  bandChain_pos hΛ hζ hκ (Nat.min_le_right m D.term)

theorem weakData_kap_terminal (D : OCData) (m : ℕ) (hm : D.term ≤ m) :
    D.kap m = D.κ D.term := by
  unfold OCData.kap
  rw [Nat.min_eq_right hm]

theorem weakData_cellScaleSq_pos (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) : 0 < D.cellScaleSq m := by
  unfold OCData.cellScaleSq OCData.eps
  exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) (weakData_kap_pos D hΛ hζ hκ m)

theorem weakData_family_contrast {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (hm : D.term < m)
    (slot : ℤ) (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm h) :
    (familyLiftData D m slot A ρ edge).η = 1 := by
  change D.kap m / D.kap (m - 1) = 1
  rw [weakData_kap_terminal D m (by omega), weakData_kap_terminal D (m - 1) (by omega)]
  exact div_self (bandChain_pos hΛ hζ hκ le_rfl).ne'

theorem weakData_lift_window (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (slot : ℤ) :
    D.slotStart m slot / D.cellScaleSq m ≤
      ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  apply div_le_div_of_nonneg_right _ (weakData_cellScaleSq_pos D hΛ hζ hκ m).le
  unfold OCData.slotStart
  exact mul_le_mul_of_nonneg_right (by linarith) (Construction.Stream.ocTau_pos hΛ).le

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The outer divergence retains the composed scalar matrix grade with one finite forcing constant. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedSourceArrayMatrixBudget (H D L : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η BE BF : ℝ) : ℝ :=
  (Fintype.card (Fin 2) : ℝ) * sourceCovariantWordConstant A η *
    normalizedSourceFluxMatrixBudget (H + 1) D L A η BE BF

theorem normalizedSourceArrayMatrixBudget_nonneg (H D L : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BE BF : ℝ) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF) :
    0 ≤ normalizedSourceArrayMatrixBudget H D L A η BE BF :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (zero_le_one.trans (sourceCovariantWordConstant_one_le A η)))
    (normalizedSourceFluxMatrixBudget_nonneg _ _ _ _ _ _ _ hBE hBF)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The actual weak lift clock has a strictly positive finite inverse window. -/

theorem weakData_lift_window_strict (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (slot : ℤ) :
    D.slotStart m slot / D.cellScaleSq m <
      ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  apply (div_lt_div_iff_of_pos_right (weakData_cellScaleSq_pos D hΛ hζ hκ m)).mpr
  unfold OCData.slotStart
  exact mul_lt_mul_of_pos_right (by linarith) (Construction.Stream.ocTau_pos hΛ)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The actual weak molecular clock gives precisely the requested dimensional coefficient factor. -/

theorem weakData_dStar (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (hm : D.term < m) :
    ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) = D.eps m := by
  have hpos := weakData_kap_pos D hΛ hζ hκ m
  have hprev : D.kap (m - 1) = D.kap m := by
    rw [weakData_kap_terminal D (m - 1) (by omega), weakData_kap_terminal D m (by omega)]
  unfold ocDStar
  rw [hprev, div_self hpos.ne', Real.sqrt_one, mul_one]
  rfl

theorem weakData_flux_dimensional_count (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (hm : D.term < m)
    (ρ : ℝ) (hρ : 0 < ρ) (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
        ρ ^ (d - 1) = D.κ D.term * D.eps m ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ)) := by
  rw [weakData_dStar D hΛ hζ hκ m hm]
  unfold OCData.cellScaleSq
  rw [weakData_kap_terminal D m (by omega)]
  exact weakFlux_dimensional_count (D.eps m) ρ (D.κ D.term)
    (Construction.Stream.ocEpsilon_pos hΛ) hρ n d hn hd

/-! Centering and ordered recurrence corrections retain the individual scalar matrix entry reserves. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftCellSourceComponentReserve (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (v : ι)
    (QA : ∀ u, JointSourceReserve H (fun t z Y => normalizedLiftASource Q Cc f hh n A t z Y u))
    (QT : ∀ j ∈ Finset.Icc 1 (n - 2),
      ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
        liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t Y z v)) :
    JointSourceReserve H (fun t z Y => normalizedLiftCellSource Q Cc f hh n A t z Y v) := by
  let Qwhole := jointSourcePiReserve H
    (fun u t z Y => normalizedLiftASource Q Cc f hh n A t z Y u) QA
  let T := fun j (ab : ℕ × ℕ) t z Y => (Real.exp (A Y))⁻¹ •
    liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t Y z v
  let S := JointSourceReserve.finsetSum (Finset.Icc 1 (n - 2)) H
    (fun j t z Y => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab t z Y)
    (fun j hj => JointSourceReserve.finsetSum (Finset.HasAntidiagonal.antidiagonal hh) H
      (T j) (QT j hj))
  let L : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  have hmean (t : ℝ) (Y : Vec 2) :
      fieldCellMean (fun z => normalizedLiftASource Q Cc f hh n A t z Y v) =
        (Real.exp (A Y))⁻¹ • liftMean Q Cc f hh n t Y v := by
    have hp := fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) v)
      (Qwhole.fast_contDiff t Y).continuous
    change fieldCellMean (fun z => normalizedLiftASource Q Cc f hh n A t z Y v) =
      fieldCellMean (fun z => normalizedLiftASource Q Cc f hh n A t z Y) v at hp
    rw [hp]
    simp only [normalizedLiftASource, fieldCellMean_smul, liftMean, Pi.smul_apply]
  have he : (fun t z Y => normalizedLiftCellSource Q Cc f hh n A t z Y v) =
      fun t z Y => L (normalizedLiftASource Q Cc f hh n A t z Y v -
        fieldCellMean (fun w => normalizedLiftASource Q Cc f hh n A t w Y v)) +
        ∑ j ∈ Finset.Icc 1 (n - 2),
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab t z Y := by
    funext t z Y
    rw [hmean]
    simp only [normalizedLiftCellSource, liftCellSource, smul_add, smul_neg, smul_sub,
      Finset.smul_sum, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply,
      Pi.smul_apply, L, neg_apply, ContinuousLinearMap.id_apply, normalizedLiftASource, T]
  exact (((QA v).center.map L).add S).congrSource he.symm
end

/-! The slow mean in an ordered lift composition retains its individual matrix-entry budget. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftMeanComponentReserve (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (v : ι)
    (QA : ∀ u, JointSourceReserve H (fun t z Y => normalizedLiftASource Q Cc f hh n A t z Y u)) :
    JointSourceReserve H (fun t _ Y => (Real.exp (A Y))⁻¹ • liftMean Q Cc f hh n t Y v) := by
  let Qwhole := jointSourcePiReserve H
    (fun u t z Y => normalizedLiftASource Q Cc f hh n A t z Y u) QA
  have he : (fun t (_ : Vec 2) Y => fieldCellMean
      (fun z => normalizedLiftASource Q Cc f hh n A t z Y v)) =
      fun t (_ : Vec 2) Y => (Real.exp (A Y))⁻¹ • liftMean Q Cc f hh n t Y v := by
    funext t z Y
    have hp := fieldCellMean_clm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) v)
      (Qwhole.fast_contDiff t Y).continuous
    change fieldCellMean (fun z => normalizedLiftASource Q Cc f hh n A t z Y v) =
      fieldCellMean (fun z => normalizedLiftASource Q Cc f hh n A t z Y) v at hp
    rw [hp]
    simp only [normalizedLiftASource, fieldCellMean_smul, liftMean, Pi.smul_apply]
  exact (QA v).mean.congrSource he
end

/-! Dimensionalizing the actual weak transfer cancels precisely its coarse normalization. -/

theorem weak_transferAt_dimensionalization (D : OCData) (m : ℕ) (pc : ℤ) (lam : ℝ)
    (Dγ : ℕ) (fop : FamFluxOp) (t : ℝ) (ch : RealChain) (z : Vec 2)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (hν : D.kap (m - 1) ≠ 0) (he : D.eps (m - 1) ≠ 0) :
    (D.kap (m - 1) * D.eps (m - 1) ^ (d - 2)) • transferAt D m pc lam Dγ fop t ch z d word =
      lam • ∑ᶠ (slot : ℤ) (_ : Odd slot ∧ IsScheduledIn D (m - 1) slot pc),
        ocCutoff D.α D.q D.Λ m slot t • transportedCoeff
          (fun h => (childTransition D slot t (ch.recenter D h)
            (z + (D.eps (m - 1))⁻¹ • h))⁻¹) Dγ
          (fun d I => fluxCoeff (fop slot t (ch.appendChild D slot t z)) d I 0)
          (d - 1) word 0 := by
  unfold transferAt
  rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hν (pow_ne_zero _ he)), one_mul]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The canonical real readout agrees with every produced higher carrier of an actual solution. -/

theorem realCellRawReadout_high_eq (K : ℕ) (w : TorusHk K ℂ)
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hm : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hw : torusHkValueCLM w =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    realCellClassicalReadout (cellRawTrace D t) =
      realClassicalLift K (mapTorusHk Complex.reCLM w) := by
  have he : torusHkValueCLM w = cellRawTrace D t :=
    Lp.ext (hw.trans (cellRawTrace_ae D t hm).symm)
  rw [← he]
  exact realCellClassicalReadout_high_eq K w

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The physical slow-flux mean is intrinsic to centered predecessors and genuine source regularity. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftFluxX_cell_mean_intrinsic (Q : LiftOperatorData ι h D) (hD : 1 ≤ D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (Y : Vec 2) (k : Fin 2)
    (hG : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun Y => Q.G t Y i j))
    (hv : Continuous (Q.v t))
    (hΦ : GoodField 1 (liftApply (n - 1) (Cc hh (n - 1)) f t))
    (hΨ : CoefField True 1 (liftApply (n - 2) (Cc hh (n - 2)) f t))
    (hgood : ∀ q, GoodField D (liftApply q (Cc (hh - 1) q) f t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z)) :
    fieldCellMean (fun z => liftFluxX Q Cc f hh n t Y z k) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k) •
        liftApply (n - 1) (Cc hh (n - 1)) f t Y z) -
      Real.sqrt Q.η • fieldCellMean (fun z =>
        ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
          sourceFluxCoefficientArray Q.edge Q.η t
            (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) f t) k j Y z) := by
  let Φ := liftApply (n - 1) (Cc hh (n - 1)) f t
  let Ψ := liftApply (n - 2) (Cc hh (n - 2)) f t
  let C : Vec 2 → ∀ i, h i := fun z =>
    ((Real.sqrt Q.η * Q.v t z k) • Φ Y z -
      Real.sqrt Q.η • ∑ j : Fin 2, Q.G t Y k j • fastPartial j Φ Y z) -
      Q.η • ∑ j : Fin 2, Q.G t Y k j • slowPartial j Ψ Y z
  let T : Vec 2 → ∀ i, h i := fun z =>
    ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
      sourceFluxCoefficientArray Q.edge Q.η t
        (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) f t) k j Y z
  have hF : Continuous (fun z => ∑ j : Fin 2, Q.G t Y k j • fastPartial j Φ Y z) :=
    continuous_finsetSum _ (fun j _ =>
      ((hΦ.fastPartial j).continuous_slice Y).const_smul (Q.G t Y k j))
  have hS : Continuous (fun z => ∑ j : Fin 2, Q.G t Y k j • slowPartial j Ψ Y z) :=
    continuous_finsetSum _ (fun j _ =>
      ((hΨ.slowPartial j).1.continuous_slice Y).const_smul (Q.G t Y k j))
  have hC : Continuous C :=
    (((continuous_const.mul ((continuous_apply k).comp hv)).smul
      (hΦ.continuous_slice Y)).sub (hF.const_smul (Real.sqrt Q.η))).sub (hS.const_smul Q.η)
  have hT : Continuous T := continuous_finsetSum _ (fun j _ =>
    (sourceFluxCoefficientArray_good Q.edge hD Q.η t _ (hgood (n - 1 - j)) hΓ k j).continuous_slice Y)
  have he : (fun z => liftFluxX Q Cc f hh n t Y z k) =
      fun z => C z - Real.sqrt Q.η • T z := by
    funext z
    simp only [liftFluxX, ite_eq_left hn, ite_eq_right hhpos]
    rw [liftFluxTaylor_convolution_identity Q.edge hD Q.η t
      (fun q => liftApply q (Cc (hh - 1) q) f t) hgood n (by omega) k Y z]
    change (_ - _) + -_ - _ = (_ - _ - _) - _
    simp only [sub_eq_add_neg]
    rfl
  calc
    _ = fieldCellMean C - fieldCellMean (fun z => Real.sqrt Q.η • T z) := by
      rw [he]
      exact fieldCellMean_sub hC (hT.const_smul (Real.sqrt Q.η))
    _ = _ := by
      rw [fieldCellMean_smul, liftFluxCross_cell_mean Q.η (Q.G t) (Q.v t) Φ Ψ hG hv hΦ hΨ Y k]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Public raw complex weak identities from the actual Hilbert cell equation. -/

/-- Every raw realization of the actual weak Hilbert solution satisfies the literal public identity. -/
theorem dataWeakHilbert_raw_identity {a b : ℝ}
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun r => dataDualDerivative P r
      (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)))
    (D : ℝ → RawJet2 1 ℂ)
    (htrace : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ a,
      ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t a)
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (ψ : TorusHkFunction 1 ℂ) :
    CellWeakIdentity (dataCoefficients P) s t (cellValue D s) (cellValue D t) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (cellValue D)
      (fun r j => cellGradComp (D r) j) src F := by
  let g := fun r => dataDualDerivative P r (slice r) (cellSourceSlice src r)
    (fun j => cellSourceSlice (fun t x => F t x j) r)
  let R := fun r => cellLiteralRHS (dataCoefficients P) r (cellValue D r) (cellGradComp (D r))
    (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src r) (F r)
  have hFlux (j : Fin 2) := cellSource_memLp_slices (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have hgood : ∀ᵐ r ∂volume.restrict (Ioc s t),
      Integrable (R r) (volume.restrict AVenhance.unitCube) ∧
        (∫ x in AVenhance.unitCube, R r x) = cellDualComplexPair (g r) (cellRawTest ψ) := by
    have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
    have hj := hjet.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hS := (cellSource_memLp_slices (Icc a b) src hsrc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hQ := (ae_all_iff.mpr hFlux).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hj, hS, hQ] with r hr hsr hfr
    exact dataRawSpatial_equation P r (slice r) (D r) hr ψ _ _ (src r) (F r)
      (cellSourceSlice_ae src r hsr) (fun j => cellSourceSlice_ae _ r (hfr j))
  have hi := cellDualComplexPair_intervalIntegrable hs ht hst g h.dual (cellRawTest ψ)
  have hti : Integrable (fun r => cellDualComplexPair (g r) (cellRawTest ψ))
      (volume.restrict (Ioc s t)) := by
    have hh := intervalIntegrable_iff.mp hi
    rw [uIoc_of_le hst] at hh
    exact hh
  have he : (fun r => ∫ x in AVenhance.unitCube, R r x) =ᵐ[volume.restrict (Ioc s t)]
      fun r => cellDualComplexPair (g r) (cellRawTest ψ) := hgood.mono (fun _ hr => hr.2)
  have htime := hti.congr he.symm
  have hinc := h.complex_increment s hs t ht hst (cellRawTest ψ)
  rw [cellRawTest_pairing_integral ψ (u t) _ (htrace t ht),
    cellRawTest_pairing_integral ψ (u s) _ (htrace s hs), intervalIntegral.integral_of_le hst] at hinc
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) _ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) _ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) _) ∧
    Integrable (fun r => ∫ x in AVenhance.unitCube, R r x) (volume.restrict (Ioc s t)) ∧
    (∫ x in AVenhance.unitCube, cellValue D t x * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, cellValue D s x * ψ.jet (valueIndex2 1) x) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x
  exact ⟨cellRawTest_pairing_integrable ψ _ _ (htrace t ht),
    cellRawTest_pairing_integrable ψ _ _ (htrace s hs),
    hgood.mono (fun _ hr => hr.1), htime, hinc.trans (integral_congr_ae he).symm⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Literal path edges preserve their unit maps and the selected stored witness matrix. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem pathEdges_maps_bound (G : GenStage D hr Dm bw j₀) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c : StageCtx D bw j₀ G.level p)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ)
    (hγ : γ ∈ pathEdges G π p c v u d) : ‖γ.map‖ ≤ 1 := by
  unfold pathEdges at hγ
  split at hγ
  · split at hγ
    · simp only [List.mem_singleton] at hγ
      subst γ
      exact le_of_eq (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := ℝ))
    · exact False.elim (List.not_mem_nil hγ)
  · exact False.elim (List.not_mem_nil hγ)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Pointwise limits of actual finite weak cell test moments. -/

variable {a b : ℝ} {hab : a ≤ b} {P : MolecularData}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- Each full H¹ test moment of the finite traces converges pointwise to the PDE primitive. -/
theorem MolecularGalerkinLimitData.moment_primitive_tendsto
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => inner ℝ
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)) atTop
      (𝓝 (inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t,
        dataGeneratorForm P r (D.limit r) z + cellRawSourceFunctional 0 src F r z)) := by
  have hgen := D.generator_integral_tendsto z t ht
  have hq := cellRawSource_integral_fourier_tendsto ⟨le_rfl, hab⟩ ht ht.1 0 src F hsrc hF
    D.subsequence D.monotone z
  have hinit : Tendsto (fun n => inner ℝ initial
      (torusHkValueCLM (galerkinProj (D.subsequence n) z))) atTop
      (𝓝 (inner ℝ initial (torusHkValueCLM z))) :=
    (tendsto_const_nhds (x := initial)).inner
      (((torusHkValueCLM (E := ℂ) (K := 1)).continuous.tendsto z).comp
        ((galerkinProj_tendsto z).comp D.monotone.tendsto_atTop))
  have hlim := hinit.add (hgen.add hq)
  have hgint := dataGenerator_pairing_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 P z D.limit (Lp.memLp D.limit)
  have hqint := cellRawSourceFunctional_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 0 src F hsrc hF z
  rw [← intervalIntegral.integral_add hgint hqint] at hlim
  apply hlim.congr'
  filter_upwards with n
  let N := D.subsequence n
  have he := cellGalerkin_full_test_primitive hab N (dataGeneratorB P)
    (cellRawSourceFunctional 0 src F) _ _ (D.variational N) initial (D.initial_value N) z t ht
  change inner ℝ (cellGalerkinValue N (extendCurve hab (D.curve N) t)) (torusHkValueCLM z) =
    inner ℝ initial (torusHkValueCLM (galerkinProj N z)) + ∫ r in a..t,
      dataGeneratorForm P r (D.state N r) (galerkinProj N z) +
        cellRawSourceFunctional 0 src F r (galerkinProj N z) at he
  rw [intervalIntegral.integral_add
    (dataGenerator_pairing_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 P
      (galerkinProj N z) (D.state N) (D.stateLp N))
    (cellRawSourceFunctional_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 0 src F hsrc hF
      (galerkinProj N z))] at he
  exact he.symm

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Mean-free earlier coefficient extensions center the literal normalized recurrence globally. -/

section
variable {ι : Type*} [Fintype ι] {D : ℕ}

theorem normalizedLiftCellSource_component_mean_zero_of_predecessors
    (H : ℕ) (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (f : ℝ → Vec 2 → ι → ℝ) (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (QA : JointSourceReserve H (normalizedLiftASource Q Cc f hh n A))
    (hcoef : ∀ j ∈ Finset.Icc 1 (n - 2),
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ m ≤ j,
      ∀ α : DerivativeWord2 m, ∀ t X v u,
        Continuous (fun z => Cc p.1 j m α t X z v u) ∧
        ∀ ξ : ℝ, fieldCellMean (fun z => Cc p.1 j m α t X z v u ξ) = 0)
    (t : ℝ) (X : Vec 2) (v : ι) :
    fieldCellMean (fun z => normalizedLiftCellSource Q Cc f hh n A t z X v) = 0 := by
  have he : (fun z => liftA Q Cc f hh n t X z) =
      fun z => Real.exp (A X) • normalizedLiftASource Q Cc f hh n A t z X := by
    funext z
    simp only [normalizedLiftASource, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hA : Continuous (fun z => liftA Q Cc f hh n t X z) := by
    rw [he]
    exact (QA.fast_contDiff t X).continuous.const_smul (Real.exp (A X))
  have hm := CycleComparison.Lift.liftCellSource_component_mean_zero_of_predecessors
    Q Cc hh n f t X v (fun j hj p hp m hm α u => hcoef j hj p hp m hm α t X v u) hA
  change fieldCellMean (fun z => (Real.exp (A X))⁻¹ • liftCellSource Q Cc f hh n t X z v) = 0
  rw [fieldCellMean_smul, hm, smul_zero]
end

/-! Genuine normalized forward and inverse chart jets bound the physical inverse-Piola matrix. -/

theorem physical_chart_inverse_jacobian_scaled_jets
    (X : Vec 2 ≃ₜ Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) ⇑X)
    (hG : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hFj : ∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y,
      ‖iteratedFDeriv ℝ n (rescaledChart ρ ⇑X) y‖ ≤ B)
    (hGj : ∀ n, 1 ≤ n → n ≤ N → ∀ y,
      ‖iteratedFDeriv ℝ n (rescaledChart ρ ⇑X.symm) y‖ ≤ B)
    (a b : Fin 2) (n : ℕ) (hn : n ≤ N) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => chartInvJacobian ⇑X.symm y a b) x‖ ≤
      positiveJetCompositionBudget N B := by
  have hK : ContDiff ℝ (⊤ : ℕ∞) (fun y => chartInvJacobian ⇑X.symm y a b) :=
    CycleJointProofs.chartInvJacobian_homeomorph_smooth X hF hG a b
  have he : (fun Y => chartInvJacobian ⇑X.symm (ρ • Y) a b) =
      fun Y => jacMatrix (rescaledChart ρ ⇑X) (rescaledChart ρ ⇑X.symm Y) a b := by
    funext Y
    rw [CycleJointProofs.chartInvJacobian_homeomorph_symm X (hF.differentiable (by simp)) (hG.differentiable (by simp)),
      rescaledChart_jacMatrix ρ hρ ⇑X hF]
    dsimp only [rescaledChart]
    rw [smul_inv_smul₀ hρ.ne']
    rfl
  have hb := composed_chart_jacobian_entry_jet_bound
    (rescaledChart ρ ⇑X) (rescaledChart ρ ⇑X.symm)
    (rescaledChart_smooth ρ ⇑X hF) (rescaledChart_smooth ρ ⇑X.symm hG)
    N n hn B B hB hFj hGj a b (ρ⁻¹ • x)
  rw [max_self] at hb
  have hs := CycleWords.normalizedJet_rescaling_eq n (hK.of_le (by simp)) 1 ρ (ρ⁻¹ • x)
  simp only [one_pow, one_mul, abs_of_pos hρ, smul_inv_smul₀ hρ.ne'] at hs
  rw [← hs, he]
  exact hb

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Uniform finite-trace bounds for identification of the weak Galerkin limit. -/

variable {a b : ℝ} {hab : a ≤ b} {P : MolecularData}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The actual finite traces have a nonnegative square budget uniform in time and cutoff. -/
theorem MolecularGalerkinLimitData.uniform_trace_bound
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N t, t ∈ Icc a b →
      ‖cellGalerkinValue N (extendCurve hab (D.curve N) t)‖ ^ 2 ≤ E := by
  let S := cellSourceSlice src
  let Q := fun r j => cellSourceSlice (fun t x => F t x j) r
  have hS := cellSourceSlice_memLp (Icc a b) src hsrc
  have hQ (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  let E := (‖initial‖ ^ 2 + ∫ r in a..b, ‖S r‖ ^ 2 + 4 * ∑ j, ‖Q r j‖ ^ 2) *
    Real.exp ((1 + 8 * P.V ^ 2) * (b - a))
  have hbound : ∀ N t, t ∈ Icc a b →
      ‖cellGalerkinValue N (extendCurve hab (D.curve N) t)‖ ^ 2 ≤ E := by
    intro N t ht
    have he := dataFinite_energy_sup_bound hab N P S Q hS hQ _ _ _
      (D.stateLp N) (D.variational N) t ht
    have hn := cellGalerkinL2Initial_norm_le N initial
    have hn2 : ‖cellGalerkinValue N (extendCurve hab (D.curve N) a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
      rw [D.initial_value N]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    exact he.trans (mul_le_mul_of_nonneg_right (add_le_add hn2 le_rfl) (Real.exp_nonneg _))
  exact ⟨E, (sq_nonneg _).trans (hbound 0 a ⟨le_rfl, hab⟩), hbound⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Actual dual time derivatives associated with arbitrary public raw solutions. -/

/-- The actual Riesz dual derivative of a public raw trajectory. -/
def dataRawSolutionDual (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ) : TorusHk 1 ℂ :=
  dataDualDerivative P t (cellH1Slice D t) (cellSourceSlice src t)
    (fun j => cellSourceSlice (fun r x => F r x j) t)

/-- Every public solution has the actual dual derivative in temporal L². -/
theorem dataSolution_dual_memLp {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) (dataCoefficients P) src F D) :
    MemLp (dataRawSolutionDual P src F D) 2 (volume.restrict (Icc a b)) :=
  dataDualDerivative_memLp P (cellH1Slice D) (cellSolution_slice_memLp hab h)
    _ (cellSourceSlice_memLp (Icc a b) src hsrc) _
    (fun j => cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! The original molecular solving interval maps exactly into the physical pulse window. -/

theorem weak_lift_clock_in_pulse_window (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (slot : ℤ) (s : ℝ)
    (hs : s ∈ Set.Icc (D.slotStart m slot / D.cellScaleSq m)
      ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)) :
    D.cellScaleSq m * s ∈ ocPulseWindow D.α D.q D.Λ m slot := by
  have hc := weakData_cellScaleSq_pos D hΛ hζ hband m
  constructor
  · have h := (div_le_iff₀ hc).mp hs.1
    simpa only [OCData.slotStart, mul_comm] using h
  · have h := (le_div_iff₀ hc).mp hs.2
    simpa only [mul_comm] using h

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Higher carriers and finite bounds for the literal triangular metric-jet flux. -/

def metricJetFluxCarrier (K : ℕ) (Gj : ℕ × ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (w : ℕ × ℕ → TorusHk (K + 1) ℂ) (α : ℕ × ℕ) : TorusHk K ComplexCellVector :=
  ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ) •
    metricGradientCarrier K (Gj β) (w (α.1 - β.1, α.2 - β.2))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Natural lower-state carrier data for a triangular parameter-jet equation. -/

structure MetricJetCarrierData (I : Set ℝ) (K : ℕ)
    (Gj : ℕ × ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) where
  w : ℕ × ℕ → ℝ → TorusHk (K + 1) ℂ
  B : ℕ × ℕ → ℝ
  R : ℕ × ℕ → ℝ
  metric_measurable : ∀ β ∈ cellJetFluxIndices α, ∀ i j, Measurable (fun t => Gj β t i j)
  carrier_measurable : ∀ β ∈ cellJetFluxIndices α, StronglyMeasurable (w (α.1 - β.1, α.2 - β.2))
  state_weak : ∀ β ∈ cellJetFluxIndices α, ∀ᵐ t ∂volume.restrict I,
    HasPeriodicOrderedWeakJet (cj (α.1 - β.1, α.2 - β.2) t)
  carrier_value : ∀ β ∈ cellJetFluxIndices α, ∀ᵐ t ∂volume.restrict I,
    torusHkValueCLM (w (α.1 - β.1, α.2 - β.2) t) =ᵐ[volume.restrict AVenhance.unitCube]
      cj (α.1 - β.1, α.2 - β.2) t (valueIndex2 1)
  metric_nonneg : ∀ β ∈ cellJetFluxIndices α, 0 ≤ B β
  state_nonneg : ∀ β ∈ cellJetFluxIndices α, 0 ≤ R β
  metric_bound : ∀ t β, β ∈ cellJetFluxIndices α → ∀ i j, |Gj β t i j| ≤ B β
  state_bound : ∀ t β, β ∈ cellJetFluxIndices α → ‖w (α.1 - β.1, α.2 - β.2) t‖ ≤ R β

def MetricJetCarrierData.carrier {I K Gj cj α} (Q : MetricJetCarrierData I K Gj cj α) :=
  fun t => metricJetFluxCarrier K (fun β => Gj β t) (fun β => Q.w β t) α

def MetricJetCarrierData.budget {I K Gj cj α} (Q : MetricJetCarrierData I K Gj cj α) : ℝ :=
  ∑ β ∈ cellJetFluxIndices α,
    (cellJetChoose α β : ℝ) * (Q.B β * metricGradientCarrierConstant K * Q.R β)

theorem MetricJetCarrierData.budget_nonneg {I K Gj cj α} (Q : MetricJetCarrierData I K Gj cj α) :
    0 ≤ Q.budget := by
  apply Finset.sum_nonneg
  intro β hβ
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (mul_nonneg (Q.metric_nonneg β hβ) (metricGradientCarrierConstant_nonneg K))
    (Q.state_nonneg β hβ))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Construct public raw cell solutions from the actual weak Hilbert equation. -/

/-- A solution of the actual Hilbert cell equation produces the public raw energy solution. -/
theorem dataWeakHilbert_exists_raw_solution {a b : ℝ}
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun r => dataDualDerivative P r
      (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r))) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Icc a b) (dataCoefficients P) src F D ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) := by
  obtain ⟨D, hweak, htrace, hjoint, hjet, hper⟩ :=
    cellWeak_exists_raw_realization (Icc a b) u slice h.state h.agrees
  refine ⟨D, ⟨ordConnected_Icc, hweak, ?_, ?_, ?_, ?_, ?_⟩, htrace⟩
  · intro t _
    exact ⟨(Lp.memLp (u t)).ae_eq (htrace t), hper t _⟩
  · intro j
    exact (hjoint j).aestronglyMeasurable
  · exact cellRaw_trace_continuous (Icc a b) u h.trace (cellValue D) (fun t _ => htrace t)
  · intro s hs t ht
    exact cellRawGradient_energy_finite D hjoint s hs t ht
  · intro s hs t ht hst ψ
    exact dataWeakHilbert_raw_identity P src F hsrc hF u slice h D
      (fun t _ => htrace t) hjet s hs t ht hst ψ

end AVRegularity.EntryWeakProofs
end
end
