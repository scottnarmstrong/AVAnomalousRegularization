-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.ParameterCoefficientJetMeasurable
public import AVRegularity.EntryWeak.SourceLocalMetricCongruence
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Construction.StrainPhysical.Context
public import AVRegularity.CycleComparison.Lift.CellScalarSourceSeries
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! A zero value of an actual periodic weak jet forces its gradient to vanish. -/

theorem weakJet_zero_value_coordinate (D : RawJet2 1 ℂ)
    (hD : HasPeriodicOrderedWeakJet D)
    (h0 : D (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (j : JetIndex2 1) : D j =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  let w : TorusHk 1 ℂ := (⟨D, hD⟩ : TorusHkFunction 1 ℂ).toHk
  have hv : torusHkValueCLM w = 0 := Lp.ext
    ((torusJetToL2_ae D hD.2.1 (valueIndex2 1)).trans
      (h0.trans (Lp.coeFn_zero (E := ℂ) (p := 2)
        (μ := volume.restrict AVenhance.unitCube)).symm))
  have hw : w = 0 := cellH1Value_injective (hv.trans (map_zero _).symm)
  have hj := torusJetToL2_ae D hD.2.1 j
  change (w.val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D j at hj
  rw [hw] at hj
  exact hj.symm.trans (Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := volume.restrict AVenhance.unitCube))

theorem weakJet_zero_value_gradient (D : RawJet2 1 ℂ)
    (hD : HasPeriodicOrderedWeakJet D)
    (h0 : D (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    cellGradient D =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  have hh := Filter.eventually_all.2 (fun j : Fin 2 =>
    weakJet_zero_value_coordinate D hD h0 ⟨⟨1, by decide⟩, fun _ => j⟩)
  filter_upwards [hh] with x hx
  apply PiLp.ext
  intro j
  exact hx j

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.Classical
namespace AVRegularity.EntryWeakProofs

/-! Finite classical data have bounded jointly measurable ordered Sobolev jets. -/

theorem classicalWordDerivative_eq_ordered (n : ℕ) (w : DerivativeWord2 n)
    (q : Vec 2 → ℝ) :
    classicalWordDerivative (smoothLiftWord n w) q = orderedDerivative w q := by
  induction n with
  | zero => simp [smoothLiftWord, classicalWordDerivative, orderedDerivative]
  | succ n ih =>
    rw [smoothLiftWord, classicalWordDerivative, ih, orderedDerivative_succ]
    rfl

theorem classicalFiniteJet_norm_le (l : ℕ) (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (l : ℕ∞) q) (a : JetIndex2 l) (x : Vec 2) :
    ‖classicalFiniteJet l q a x‖ ≤ ‖iteratedFDeriv ℝ a.1.val q x‖ := by
  rw [classicalFiniteJet, classicalWordDerivative_eq_ordered]
  exact ChartTransport.norm_orderedDerivative_le
    (hq.of_le (by exact_mod_cast Nat.le_of_lt_succ a.1.isLt)) a.2 x

theorem classicalFiniteJet_joint_measurable (l : ℕ) (q : ℝ → Vec 2 → ℝ)
    (hq : ∀ t, ContDiff ℝ (l : ℕ∞) (q t))
    (hm : Measurable (Function.uncurry q)) (a : JetIndex2 l) :
    Measurable (fun p : ℝ × Vec 2 => classicalFiniteJet l (q p.1) a p.2) := by
  simp only [classicalFiniteJet, classicalWordDerivative_eq_ordered]
  exact Weighted.parameter_orderedDerivative_joint_measurable l a.1.val
    (Nat.le_of_lt_succ a.1.isLt) q
    (fun x => hm.comp (measurable_id.prodMk measurable_const)) hq a.2

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! The actual recurrence depends only on earlier coefficient germs on its open carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_slow_open_congr_predecessors {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m ≤ q, ∀ α X, X ∈ U → ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    SlowOpenFieldEq U (liftA Q Cc f hh n t) (liftA Q Dc f hh n t) := by
  have hop (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) :
      SlowOpenFieldEq U (liftApply q (Cc p q) f t) (liftApply q (Dc p q) f t) :=
    liftApply_slow_open_congr hU q t _ _ f f (he p q hpq) (fun _ _ => rfl)
  have h1 := (hop hh (n - 1) (Or.inr ⟨rfl, by omega⟩)).cellB1 hU Q.η Q.G Q.v t
  intro X hX z
  have h2 : (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) f t) X z else 0) =
      (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Dc hh (n - 2)) f t) X z else 0) := by
    by_cases hn2 : 2 ≤ n
    · rw [ite_eq_left hn2, ite_eq_left hn2]
      exact (hop hh (n - 2) (Or.inr ⟨rfl, by omega⟩)).cellB2 hU Q.η Q.G t X hX z
    · rw [ite_eq_right hn2, ite_eq_right hn2]
  have hS : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Dc (hh - 1) (n - j)) f t) X z) := by
    by_cases hhh : hh = 0
    · rw [ite_eq_left hhh, ite_eq_left hhh]
    · rw [ite_eq_right hhh, ite_eq_right hhh]
      apply Finset.sum_congr rfl
      intro j _
      exact (hop (hh - 1) (n - j) (Or.inl (by omega))).sourceCoeff hU Q.edge Q.η t j X hX z
  change _ + _ - _ = _ + _ - _
  rw [h1 X hX z, h2, hS]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The finite real spatial jet embedded into the complex cell carrier. -/

def complexFiniteJet (l : ℕ) (q : Vec 2 → ℝ) : RawJet2 l ℂ :=
  mapRawJet Complex.ofRealCLM (classicalFiniteJet l q)

theorem complexFiniteJet_periodicWeak (l : ℕ) (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (l : ℕ∞) q) (hp : AVenhance.IsZ2Periodic q) :
    HasPeriodicOrderedWeakJet (complexFiniteJet l q) :=
  mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _ (classicalFiniteJet_periodicWeak l q hq hp)

theorem complexFiniteJet_norm_le (l : ℕ) (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (l : ℕ∞) q) (a : JetIndex2 l) (x : Vec 2) :
    ‖complexFiniteJet l q a x‖ ≤ ‖iteratedFDeriv ℝ a.1.val q x‖ := by
  change ‖(classicalFiniteJet l q a x : ℂ)‖ ≤ _
  rw [Complex.norm_real]
  exact classicalFiniteJet_norm_le l q hq a x

theorem complexFiniteJet_joint_measurable (l : ℕ) (q : ℝ → Vec 2 → ℝ)
    (hq : ∀ t, ContDiff ℝ (l : ℕ∞) (q t))
    (hm : Measurable (Function.uncurry q)) (a : JetIndex2 l) :
    Measurable (fun p : ℝ × Vec 2 => complexFiniteJet l (q p.1) a p.2) :=
  Complex.ofRealCLM.continuous.measurable.comp (classicalFiniteJet_joint_measurable l q hq hm a)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Copy-adapt the global predecessor congruence to an open slow carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftCellSource_slow_open_congr_predecessors {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m ≤ q, ∀ α X, X ∈ U → ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    SlowOpenFieldEq U (liftCellSource Q Cc f hh n t) (liftCellSource Q Dc f hh n t) := by
  have ha := liftA_slow_open_congr_predecessors hU Q Cc Dc f hh n hn t he
  have hm := ha.fieldCellMean
  intro X hX z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Dc p.1 j) (liftMean Q Dc f p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro p hp
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hm' : ∀ Y ∈ U, liftMean Q Cc f p.2 (n - j) t Y =
        liftMean Q Dc f p.2 (n - j) t Y := by
      have ha' := liftA_slow_open_congr_predecessors hU Q Cc Dc f p.2 (n - j)
        (by omega) t (by
          intro r s hrs
          apply he r s
          rcases hrs with hrs | ⟨hrs, hsn⟩
          · exact Or.inl (by omega)
          · by_cases hr : r < hh
            · exact Or.inl hr
            · exact Or.inr ⟨by omega, by omega⟩)
      exact fun Y hY => ha'.fieldCellMean Y hY 0
    exact liftApply_slow_open_congr hU j t (Cc p.1 j) (Dc p.1 j)
      (liftMean Q Cc f p.2 (n - j)) (liftMean Q Dc f p.2 (n - j))
      (he p.1 j (by
        by_cases hlt : p.1 < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩)) hm' X hX z
  change -(liftA Q Cc f hh n t X z - liftMean Q Cc f hh n t X) + _ = _
  rw [ha X hX z, show liftMean Q Cc f hh n t X = liftMean Q Dc f hh n t X from hm X hX z,
    hsum]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Literal bounded measurable time matrices are admissible cell coefficient fields. -/

theorem bounded_matrix_field_admissible (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (hb : ∀ t i j, |G t i j| ≤ B)
    (hm : ∀ i j, Measurable (fun t => G t i j)) :
    cellMetricSupNorm (fun t (_ : Vec 2) => G t) < ⊤ ∧
      Measurable (Function.uncurry (fun t (_ : Vec 2) => G t)) := by
  have hs : cellMetricSupNorm (fun t (_ : Vec 2) => G t) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro t
    apply iSup_le
    intro z
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hb t i j)
  refine ⟨hs.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (hm i j).comp measurable_fst

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.Classical
namespace AVRegularity.EntryWeakProofs

/-! A classical periodic representative has exactly the weak gradient of its H¹ value class. -/

theorem classicalFirstJet_of_H1_value (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (1 : ℕ∞) q) (hp : AVenhance.IsZ2Periodic q) (u : TorusHk 1 ℂ)
    (he : (fun x => (q x : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => u.val (valueIndex2 1) x) :
    ∀ a, (fun x => u.val a x) =ᵐ[volume.restrict AVenhance.unitCube] complexFiniteJet 1 q a := by
  let hqj := complexFiniteJet_periodicWeak 1 q hq hp
  let v := (TorusHkFunction.mk (complexFiniteJet 1 q) hqj).toHk
  have hv : v.val (valueIndex2 1) = u.val (valueIndex2 1) := by
    apply Lp.ext
    exact (torusJetToL2_ae (complexFiniteJet 1 q) hqj.2.1 (valueIndex2 1)).trans he
  have h := TorusHk.ext_value hv
  intro a
  rw [← h]
  exact torusJetToL2_ae (complexFiniteJet 1 q) hqj.2.1 a

theorem cellJetOfField_id_eq_finite (c : ℝ → Vec 2 → ℝ) (t : ℝ) :
    cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c t = complexFiniteJet 1 (c t) := by
  funext a x
  rcases a with ⟨j, w⟩
  fin_cases j
  · rfl
  · simp only [cellJetOfField, complexFiniteJet, mapRawJet, classicalFiniteJet,
      smoothLiftWord, classicalWordDerivative, ContinuousLinearMap.id_apply]
    rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Replacing pinned edge fields by smooth local extensions preserves the literal recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_edge_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (edge : ConstituentEdges D h)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (hΓ : SlowOpenEdgeEq U t Q.edge edge) :
    SlowOpenFieldEq U (liftA Q Cc f hh n t)
      (liftA {Q with edge := edge} Cc f hh n t) := by
  intro X hX z
  have hS : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z) := by
    by_cases hhh : hh = 0
    · rw [ite_eq_left hhh, ite_eq_left hhh]
    · rw [ite_eq_right hhh, ite_eq_right hhh]
      apply Finset.sum_congr rfl
      intro j _
      exact sourceCoeff_slow_open_congr hU (fun _ _ _ => rfl) Q.η t hΓ j X hX z
  change _ + _ - _ = _ + _ - _
  rw [hS]

theorem liftCellSource_edge_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (edge : ConstituentEdges D h)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (hΓ : SlowOpenEdgeEq U t Q.edge edge) :
    SlowOpenFieldEq U (liftCellSource Q Cc f hh n t)
      (liftCellSource {Q with edge := edge} Cc f hh n t) := by
  have ha := liftA_edge_slow_open_congr hU Q edge Cc f hh n t hΓ
  have hm := ha.fieldCellMean
  intro X hX z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean {Q with edge := edge} Cc f p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    exact liftApply_slow_open_congr hU j t (Cc p.1 j) (Cc p.1 j)
      (liftMean Q Cc f p.2 (n - j)) (liftMean {Q with edge := edge} Cc f p.2 (n - j))
      (fun _ _ _ _ _ _ _ _ => rfl)
      (fun Y hY => (liftA_edge_slow_open_congr hU Q edge Cc f p.2 (n - j) t hΓ).fieldCellMean Y hY 0)
      X hX z
  change -(liftA Q Cc f hh n t X z - liftMean Q Cc f hh n t X) + _ = _
  rw [ha X hX z, show liftMean Q Cc f hh n t X =
    liftMean {Q with edge := edge} Cc f hh n t X from hm X hX z, hsum]
  rfl
end

/-! Metric extensions on an open slow carrier preserve the literal ordered mean recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (hG : ∀ X ∈ U, Q.G t X = G t X) :
    SlowOpenFieldEq U (liftA Q Cc f hh n t) (liftA {Q with G := G} Cc f hh n t) := by
  have h1 := cellB1_metric_slow_open_congr hU Q.η Q.G G Q.v t hG
    (liftApply (n - 1) (Cc hh (n - 1)) f t)
  intro X hX z
  have h2 : (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) f t) X z else 0) =
      (if 2 ≤ n then cellB2 Q.η G t (liftApply (n - 2) (Cc hh (n - 2)) f t) X z else 0) := by
    by_cases hn : 2 ≤ n
    · rw [ite_eq_left hn, ite_eq_left hn]
      exact cellB2_metric_slow_open_congr hU Q.η Q.G G t hG _ X hX z
    · rw [ite_eq_right hn, ite_eq_right hn]
  change _ + _ - _ = _ + _ - _
  rw [h1 X hX z, h2]

theorem liftCellSource_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (hG : ∀ X ∈ U, Q.G t X = G t X) :
    SlowOpenFieldEq U (liftCellSource Q Cc f hh n t)
      (liftCellSource {Q with G := G} Cc f hh n t) := by
  have ha := liftA_metric_slow_open_congr hU Q G Cc f hh n t hG
  have hm := ha.fieldCellMean
  intro X hX z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean {Q with G := G} Cc f p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    exact liftApply_slow_open_congr hU j t (Cc p.1 j) (Cc p.1 j)
      (liftMean Q Cc f p.2 (n - j)) (liftMean {Q with G := G} Cc f p.2 (n - j))
      (fun _ _ _ _ _ _ _ _ => rfl)
      (fun Y hY => (liftA_metric_slow_open_congr hU Q G Cc f p.2 (n - j) t hG).fieldCellMean Y hY 0)
      X hX z
  change -(liftA Q Cc f hh n t X z - liftMean Q Cc f hh n t X) + _ = _
  rw [ha X hX z, show liftMean Q Cc f hh n t X =
    liftMean {Q with G := G} Cc f hh n t X from hm X hX z, hsum]
  rfl
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Componentwise left application composes the stored matrix grades through every covariant test word. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def liftApplyFiniteWordCount (n : ℕ) : ℕ :=
  ∑ m : Fin (n + 1), Fintype.card (DerivativeWord2 m.val)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Genuine time-measurable higher source carriers from literal smooth periodic fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem finite_fast_ordered_jet_measurable (f : ℝ → Vec 2 → E) (n : ℕ)
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t)) (hm : Measurable (Function.uncurry f))
    (w : DerivativeWord2 n) :
    Measurable (fun p : ℝ × Vec 2 => orderedDerivative w (f p.1) p.2) := by
  have he : (fun p : ℝ × Vec 2 => orderedDerivative w (f p.1) p.2) =
      fun p => realParameterWordJet (f p.1) n (fun i => basisVec (w (Fin.rev i))) p.2 := by
    funext p
    rw [orderedDerivative_eq_iteratedFDeriv w (hf p.1)]
    rfl
  rw [he]
  exact finite_realParameterWordJet_measurable_joint f n hf hm _

theorem finiteBoundedSmoothPeriodicHk_stronglyMeasurable (K : ℕ) (f : ℝ → Vec 2 → E)
    (hf : ∀ t, ContDiff ℝ (K : ℕ∞) (f t)) (hp : ∀ t, AVenhance.IsZ2Periodic (f t))
    (hm : Measurable (Function.uncurry f)) (C : ℕ → ℝ)
    (hb : ∀ n, n ≤ K → ∀ t z, ‖iteratedFDeriv ℝ n (f t) z‖ ≤ C n) :
    StronglyMeasurable (fun t => finiteBoundedSmoothPeriodicHk K (f t) (hf t) (hp t) C
      (fun n hn z => hb n hn t z)) := by
  apply torusHk_stronglyMeasurable_of_raw_jets K _
    (fun t => smoothPeriodicRawJet K (f t))
  · intro a
    exact finite_fast_ordered_jet_measurable f a.1.val
      (fun t => (hf t).of_le (by exact_mod_cast (show a.1.val ≤ K by omega))) hm a.2
  · intro t a
    exact finiteSmoothPeriodicHk_jet_ae K (f t) (hf t) (hp t)
      (finite_smooth_periodic_jet_memLp K (f t) (hf t) C (fun n hn z => hb n hn t z)) a

theorem finiteBoundedSmoothPeriodicHk_memLp (a b : ℝ) (K : ℕ) (f : ℝ → Vec 2 → E)
    (hf : ∀ t, ContDiff ℝ (K : ℕ∞) (f t)) (hp : ∀ t, AVenhance.IsZ2Periodic (f t))
    (hm : Measurable (Function.uncurry f)) (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hb : ∀ n, n ≤ K → ∀ t z, ‖iteratedFDeriv ℝ n (f t) z‖ ≤ C n) :
    MemLp (fun t => finiteBoundedSmoothPeriodicHk K (f t) (hf t) (hp t) C
      (fun n hn z => hb n hn t z)) 2 (volume.restrict (Set.Icc a b)) :=
  MemLp.of_bound (finiteBoundedSmoothPeriodicHk_stronglyMeasurable K f hf hp hm C hb).aestronglyMeasurable
    (∑ a : JetIndex2 K, C a.1.val) (Filter.Eventually.of_forall fun t =>
      finiteBoundedSmoothPeriodicHk_norm_le K (f t) (hf t) (hp t) C hC (fun n hn z => hb n hn t z))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The genuine triangular metric flux for ordered independent parameter words. -/

variable {I : Type*}

def independentWordMetricFlux
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (w : List I) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  ((independentWordForcing w).map (fun p => cellMetricFlux (G p.1) (c p.2))).sum

theorem independentWordMetricFlux_nil
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) : independentWordMetricFlux G c [] = 0 := rfl

theorem independentWordMetricFlux_congr_lower
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c d : List I → ℝ → RawJet2 1 ℂ) (w : List I)
    (h : ∀ u, u.length < w.length → c u = d u) :
    independentWordMetricFlux G c w = independentWordMetricFlux G d w := by
  unfold independentWordMetricFlux
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [h p.2 (independentWordForcing_lengths w p hp).2.2]

theorem independent_flux_list_finite (l : List I)
    (F : I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hm : ∀ i ∈ l, AEStronglyMeasurable (Function.uncurry (F i))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hb : ∀ i ∈ l, cellUlNorm univ (F i) < ⊤) :
    AEStronglyMeasurable (Function.uncurry ((l.map F).sum))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      cellUlNorm univ ((l.map F).sum) < ⊤ := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact ⟨aestronglyMeasurable_zero, by rw [cellUlNorm_zero_field]; simp⟩
  | cons i l ih =>
    obtain ⟨ht, htb⟩ := ih (fun j hj => hm j (by simp [hj])) (fun j hj => hb j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    have hi := hm i (by simp)
    refine ⟨hi.add ht, ?_⟩
    exact (cellUlNorm_add univ _ _ hi ht).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hb i (by simp), htb⟩)

theorem independentWordMetricFlux_finite
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (w : List I)
    (hG : ∀ p ∈ independentWordForcing w, cellMetricSupNorm (G p.1) < ⊤)
    (hm : ∀ p ∈ independentWordForcing w, Measurable (Function.uncurry (G p.1)))
    (hb : ∀ p ∈ independentWordForcing w, cellEnergyNorm univ (c p.2) < ⊤)
    (hc : ∀ p ∈ independentWordForcing w, ∀ a,
      AEStronglyMeasurable (fun X : ℝ × Vec 2 => c p.2 X.1 a X.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (Function.uncurry (independentWordMetricFlux G c w))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      cellUlNorm univ (independentWordMetricFlux G c w) < ⊤ := by
  apply independent_flux_list_finite
  · intro p hp
    exact cellMetricFlux_aestronglyMeasurable univ _ _ (hm p hp) (hc p hp)
  · intro p hp
    exact (cellMetricFlux_ul_bound univ _ (hG p hp) (hm p hp) _ (hc p hp)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (hG p hp)) (hb p hp))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Ordered finite forcing sums preserve genuine uniformly local norm convergence. -/

variable {I P : Type*}

theorem independent_flux_list_tendsto (l : List I) (L : Filter P)
    (F : I → P → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (F0 : I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hm : ∀ i ∈ l, ∀ Y, AEStronglyMeasurable (Function.uncurry (F i Y))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hm0 : ∀ i ∈ l, AEStronglyMeasurable (Function.uncurry (F0 i))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc : ∀ i ∈ l, Tendsto (fun Y => cellUlNorm univ (F i Y - F0 i)) L (𝓝 0)) :
    (∀ Y, AEStronglyMeasurable (Function.uncurry ((l.map (fun i => F i Y)).sum))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) ∧
    AEStronglyMeasurable (Function.uncurry ((l.map F0).sum))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
    Tendsto (fun Y => cellUlNorm univ
      ((l.map (fun i => F i Y)).sum - (l.map F0).sum)) L (𝓝 0) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, sub_self, cellUlNorm_zero_field]
    exact ⟨fun _ => aestronglyMeasurable_zero, aestronglyMeasurable_zero, tendsto_const_nhds⟩
  | cons i l ih =>
    obtain ⟨htm, ht0, htc⟩ := ih (fun j hj => hm j (by simp [hj]))
      (fun j hj => hm0 j (by simp [hj])) (fun j hj => hc j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨fun Y => (hm i (by simp) Y).add (htm Y), (hm0 i (by simp)).add ht0, ?_⟩
    exact cellUlNorm_add_tendsto L (F i) (fun Y => (l.map (fun j => F j Y)).sum)
      (F0 i) (l.map F0).sum (hm i (by simp)) htm (hm0 i (by simp)) ht0
      (hc i (by simp)) htc

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Literal metric-word product-rule forcing and its exact successor identity. -/

variable {I : Type*}

theorem independent_list_map_sum_eq_fin_sum {E : Type*} [AddCommMonoid E]
    (l : List I) (f : I → E) : (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    congrArg (fun x : List I => (x.map f).sum) (List.ofFn_get l).symm

def independentWordMetricFluxDerivative
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (i : I) (w : List I) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  ((independentWordForcing w).map (fun p =>
    cellMetricFlux (G (i :: p.1)) (c p.2) + cellMetricFlux (G p.1) (c (i :: p.2)))).sum

theorem independentWordMetricFlux_cons
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (i : I) (w : List I) :
    independentWordMetricFlux G c (i :: w) = cellMetricFlux (G [i]) (c w) +
      independentWordMetricFluxDerivative G c i w :=
  independentWordForcing_cons_sum i w (fun a b => cellMetricFlux (G a) (c b))

theorem independentWordMetricFluxDerivative_finite
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (i : I) (w : List I)
    (hG : ∀ p ∈ independentWordForcing w,
      cellMetricSupNorm (G p.1) < ⊤ ∧ Measurable (Function.uncurry (G p.1)))
    (hG1 : ∀ p ∈ independentWordForcing w,
      cellMetricSupNorm (G (i :: p.1)) < ⊤ ∧ Measurable (Function.uncurry (G (i :: p.1))))
    (hc : ∀ p ∈ independentWordForcing w, cellEnergyNorm univ (c p.2) < ⊤ ∧ ∀ a,
      AEStronglyMeasurable (fun X : ℝ × Vec 2 => c p.2 X.1 a X.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc1 : ∀ p ∈ independentWordForcing w, cellEnergyNorm univ (c (i :: p.2)) < ⊤ ∧ ∀ a,
      AEStronglyMeasurable (fun X : ℝ × Vec 2 => c (i :: p.2) X.1 a X.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (Function.uncurry (independentWordMetricFluxDerivative G c i w))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      cellUlNorm univ (independentWordMetricFluxDerivative G c i w) < ⊤ := by
  have hm0 p hp := cellMetricFlux_aestronglyMeasurable univ _ _ (hG1 p hp).2 (hc p hp).2
  have hm1 p hp := cellMetricFlux_aestronglyMeasurable univ _ _ (hG p hp).2 (hc1 p hp).2
  apply independent_flux_list_finite
  · intro p hp
    exact (hm0 p hp).add (hm1 p hp)
  · intro p hp
    apply (cellUlNorm_add univ _ _ (hm0 p hp) (hm1 p hp)).trans_lt
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact (cellMetricFlux_ul_bound univ _ (hG1 p hp).1 (hG1 p hp).2 _ (hc p hp).2).trans_lt
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (hG1 p hp).1) (hc p hp).1)
    · exact (cellMetricFlux_ul_bound univ _ (hG p hp).1 (hG p hp).2 _ (hc1 p hp).2).trans_lt
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (hG p hp).1) (hc1 p hp).1)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Literal value readout of the smooth periodic higher carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

theorem finiteBoundedSmoothPeriodicHk_value_ae (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (C : ℕ → ℝ) (hb : ∀ n, n ≤ K → ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ C n) :
    (finiteBoundedSmoothPeriodicHk K f hf hp C hb).val (valueIndex2 K)
      =ᵐ[volume.restrict AVenhance.unitCube] f := by
  simpa [finiteBoundedSmoothPeriodicHk, valueIndex2, valueIndex, orderedDerivative] using
    finiteSmoothPeriodicHk_jet_ae K f hf hp (finite_smooth_periodic_jet_memLp K f hf C hb) (valueIndex2 K)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Natural finite higher-carrier data for a scalar and flux source. -/

structure HigherSourceCarrierData (I : Set ℝ) (K : ℕ)
    (src : ℝ → Vec 2 → ℂ) (flux : ℝ → Vec 2 → ComplexCellVector) where
  S : ℝ → TorusHk K ℂ
  F : ℝ → TorusHk K ComplexCellVector
  Ns : ℝ
  Nf : ℝ
  scalar_budget_nonneg : 0 ≤ Ns
  flux_budget_nonneg : 0 ≤ Nf
  scalar_memLp : MemLp (Function.uncurry src) 2
    ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))
  flux_memLp : MemLp (Function.uncurry flux) 2
    ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))
  scalar_carrier_memLp : MemLp S 2 (volume.restrict I)
  flux_carrier_memLp : MemLp F 2 (volume.restrict I)
  scalar_value : ∀ᵐ t ∂volume.restrict I,
    torusHkValueCLM (S t) =ᵐ[volume.restrict AVenhance.unitCube] src t
  scalar_mean_zero : ∀ᵐ t ∂volume.restrict I, cellMean (torusHkValueCLM (S t)) = 0
  flux_value : ∀ᵐ t ∂volume.restrict I,
    torusHkValueCLM (F t) =ᵐ[volume.restrict AVenhance.unitCube] flux t
  scalar_bound : ∀ t ∈ I, ‖S t‖ ≤ Ns
  flux_bound : ∀ t ∈ I, ‖F t‖ ≤ Nf

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Metric perturbations of actual all-time inverse states are admissible on every finite window. -/

theorem inverse_metric_flux_memLp_window
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : cellMetricSupNorm G < ⊤) (hGm : Measurable (Function.uncurry G))
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (a b : ℝ) :
    MemLp (Function.uncurry (cellMetricFlux G D)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hm := cellMetricFlux_aestronglyMeasurable univ G D hGm hD.1.2.2.2.1
  have hb := cellMetricFlux_ul_bound univ G hG hGm D hD.1.2.2.2.1
  have hf : cellUlNorm univ (cellMetricFlux G D) < ⊤ :=
    hb.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hG) hD.2.2)
  exact cellUl_memLp_product_interval_ae univ _ hm hf a b (subset_univ _)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Exact source replacement preserves the genuine higher carrier and both budgets. -/

def HigherSourceCarrierData.congrSources {I : Set ℝ} {K : ℕ}
    {src src' : ℝ → Vec 2 → ℂ} {flux flux' : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData I K src flux) (hs : src = src') (hf : flux = flux') :
    HigherSourceCarrierData I K src' flux' where
  S := Q.S
  F := Q.F
  Ns := Q.Ns
  Nf := Q.Nf
  scalar_budget_nonneg := Q.scalar_budget_nonneg
  flux_budget_nonneg := Q.flux_budget_nonneg
  scalar_memLp := hs ▸ Q.scalar_memLp
  flux_memLp := hf ▸ Q.flux_memLp
  scalar_carrier_memLp := Q.scalar_carrier_memLp
  flux_carrier_memLp := Q.flux_carrier_memLp
  scalar_value := hs ▸ Q.scalar_value
  scalar_mean_zero := Q.scalar_mean_zero
  flux_value := hf ▸ Q.flux_value
  scalar_bound := Q.scalar_bound
  flux_bound := Q.flux_bound

/-! Exact source equalities preserve literal higher carriers and their budgets. -/

def HigherSourceCarrierData.of_eq {I : Set ℝ} {K : ℕ}
    {src src' : ℝ → Vec 2 → ℂ} {flux flux' : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData I K src flux) (hs : src = src') (hf : flux = flux') :
    HigherSourceCarrierData I K src' flux' where
  S := Q.S
  F := Q.F
  Ns := Q.Ns
  Nf := Q.Nf
  scalar_budget_nonneg := Q.scalar_budget_nonneg
  flux_budget_nonneg := Q.flux_budget_nonneg
  scalar_memLp := by rw [← hs]; exact Q.scalar_memLp
  flux_memLp := by rw [← hf]; exact Q.flux_memLp
  scalar_carrier_memLp := Q.scalar_carrier_memLp
  flux_carrier_memLp := Q.flux_carrier_memLp
  scalar_value := by rw [← hs]; exact Q.scalar_value
  flux_value := by rw [← hf]; exact Q.flux_value
  scalar_mean_zero := Q.scalar_mean_zero
  scalar_bound := Q.scalar_bound
  flux_bound := Q.flux_bound

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! The molecular finite systems reuse the existing cell ODE and Fourier projection. -/

theorem molecularGalerkin_exists_timeH1 {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (CG V : ℝ)
    (hGm : ∀ i j, Measurable (fun t => G t i j))
    (hGb : ∀ t i j, |G t i j| ≤ CG)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hvb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (u₀ : ComplexCellL2) :
    let B := molecularGeneratorB G v V hv hvb
    let q := cellRawSourceFunctional 0 src F
    let A := fun t => cellGalerkinOperator N (B t)
    let f := fun t => cellGalerkinForcing N (q t)
    ∃ y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N),
      StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
        (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
        (fun t => cellGalerkinValue N (extendCurve hab y t))
        (fun t => cellGalerkinValue N (linearRhs A f (extendCurve hab y) t))
        (extendCurve hab y) ∧
      MemLp (fun t => cellGalerkinValue N (linearRhs A f (extendCurve hab y) t))
        2 (volume.restrict (Icc a b)) ∧
      MemLp (fun t => (extendCurve hab y t).val) 2 (volume.restrict (Icc a b)) ∧
      cellGalerkinValue N (extendCurve hab y a) = cellGalerkinValue N (cellGalerkinL2Initial N u₀) := by
  dsimp only
  obtain ⟨M, hM, hMb⟩ := molecularGalerkinOperator_bounded N G v CG V hGb hv hvb
  have hA := molecularGalerkinOperator_aestronglyMeasurable N G v V hGm hv hvb
  have hq := cellGalerkin_actualForcing_memLp N 0 src F
    (cellSource_memLp_product (Icc a b) src hsrcm hsrc)
    (cellSource_memLp_product (Icc a b) F hFm hF)
  obtain ⟨y, hy, hdy, hstate, hinit⟩ := cellGalerkin_exists_timeH1 hab N
    (molecularGeneratorB G v V hv hvb) (cellRawSourceFunctional 0 src F)
    (smoothFourierLift (K := 0) (L := 1) N (cellL2AsH0 u₀)) M hM hA hMb hq
  refine ⟨y, hy, hdy, hstate, ?_⟩
  change cellGalerkinValue N (extendCurve hab y a) = cellGalerkinValue N (cellL2FourierState N u₀)
    at hinit
  rw [← cellGalerkinL2Initial_eq_fourier] at hinit
  exact hinit

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The Jacobian of an offset flow and the window bounds of its molecular metric.

If `(u, x) ↦ 𝔛(u, x, s)` is `C¹` and the flow has the inverse law, then `F_u = D_x𝔛(u, x_𝒜, s)`
is continuous in `u` and invertible (its left inverse is the Jacobian of `𝔛(s, ·, u)`). The metric
`𝒢_u = F_u⁻¹F_u⁻ᵀ` is then continuous, and on a compact time window it is uniformly elliptic,
`𝒢 ≥ (4M²+1)⁻¹` with `M` a bound for the entries of `F`, with bounded entries. -/

/-- The Jacobian of the slice `y ↦ 𝔛(u, y, s)` is continuous in `u`. -/
theorem jac_continuous {f : ℝ → Vec 2 → Vec 2}
    (hf : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => f p.1 p.2)) (x : Vec 2) :
    Continuous (fun u => jacMatrix (f u) x) := by
  have hd : Differentiable ℝ (fun p : ℝ × Vec 2 => f p.1 p.2) := hf.differentiable (by norm_num)
  have hcf : Continuous (fun p : ℝ × Vec 2 => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) p) :=
    hf.continuous_fderiv (by norm_num)
  have hentry : ∀ i j : Fin 2, Continuous (fun u => jacMatrix (f u) x i j) := by
    intro i j
    have heq : (fun u => jacMatrix (f u) x i j) =
        fun u => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) (u, x) (0, basisVec j) i := by
      funext u
      simp only [jacMatrix, Matrix.of_apply]
      rw [AVRegularity.StrainPhysical.fderiv_slice_gen hd u x (basisVec j)]
    rw [heq]
    have h1 : Continuous (fun u : ℝ => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) (u, x)) :=
      hcf.comp (continuous_id.prodMk continuous_const)
    exact (continuous_apply i).comp (h1.clm_apply continuous_const)
  exact continuous_pi fun i => continuous_pi fun j => hentry i j

/-- Under the inverse law, the Jacobian of the slice has a left inverse, hence a unit
determinant. -/
theorem jac_isUnit_det {g : ChainGeom} (hinv : AVRegularity.ChainGeometry.InvLaw g)
    (hC : ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r)) (u s : ℝ) (x : Vec 2) :
    IsUnit (jacMatrix (fun y => g.1 u y s) x).det := by
  have hdiff : ∀ a r : ℝ, Differentiable ℝ (fun y => g.1 a y r) := by
    intro a r
    have h := (hC r).differentiable (by norm_num)
    exact h.comp ((differentiable_const a).prodMk differentiable_id)
  have hcomp : (fun w => g.1 s w u) ∘ (fun y => g.1 u y s) = id := by
    funext y
    exact hinv s u y
  have hJ := AVRegularity.CycleReference.jacMatrix_comp (f := fun w => g.1 s w u)
    (g := fun y => g.1 u y s) x (hdiff s u _) (hdiff u s x)
  rw [hcomp, AVRegularity.CycleReference.jacMatrix_identity] at hJ
  exact Matrix.isUnit_det_of_left_inverse hJ.symm

/-- The inverse of a continuous family of invertible matrices is continuous. -/
theorem continuous_inv_of_det {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F)
    (hdet : ∀ u, IsUnit (F u).det) : Continuous (fun u => (F u)⁻¹) := by
  have heq : (fun u => (F u)⁻¹) = fun u => ((F u).det)⁻¹ • (F u).adjugate := by
    funext u
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [heq]
  exact ((hF.matrix_det).inv₀ fun u => (hdet u).ne_zero).smul hF.matrix_adjugate

/-- A continuous function on a compact interval is bounded. -/
theorem exists_bound_Icc {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |φ t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  have := hM t ht
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Algebraic ellipticity: if `A F = 1` and the entries of `F` are bounded by `M`, then
`ξ·(AAᵀ)ξ ≥ (4M²+1)⁻¹|ξ|²`. -/
theorem metric_elliptic {F A : Matrix (Fin 2) (Fin 2) ℝ} (hAF : A * F = 1) {M : ℝ}
    (hM : ∀ i j, |F i j| ≤ M) (ξ : Fin 2 → ℝ) :
    (4 * M ^ 2 + 1)⁻¹ * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, (A * A.transpose) i j * ξ i * ξ j := by
  set η : Fin 2 → ℝ := fun k => ∑ i, A i k * ξ i with hη
  have hquad : ∑ i, ∑ j, (A * A.transpose) i j * ξ i * ξ j = ∑ k, η k ^ 2 := by
    simp only [hη, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  -- `ξ = Fᵀη`
  have hE : ∀ l i, A l 0 * F 0 i + A l 1 * F 1 i = if l = i then 1 else 0 := by
    intro l i
    have := congrFun (congrFun hAF l) i
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have e00 := hE 0 0
  have e01 := hE 0 1
  have e10 := hE 1 0
  have e11 := hE 1 1
  simp only [ite_true, show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    ite_false] at e00 e01 e10 e11
  have hξ0 : ξ 0 = ∑ k, F k 0 * η k := by
    simp only [hη, Fin.sum_univ_two]
    linear_combination (-(ξ 0)) * e00 - ξ 1 * e10
  have hξ1 : ξ 1 = ∑ k, F k 1 * η k := by
    simp only [hη, Fin.sum_univ_two]
    linear_combination (-(ξ 0)) * e01 - ξ 1 * e11
  have hξ : ∀ i, ξ i = ∑ k, F k i * η k := Fin.forall_fin_two.mpr ⟨hξ0, hξ1⟩
  have hMsq : ∀ i j, F i j ^ 2 ≤ M ^ 2 := fun i j => by
    have := hM i j
    have h0 : 0 ≤ |F i j| := abs_nonneg _
    nlinarith [sq_abs (F i j)]
  have hcs : ∀ i, ξ i ^ 2 ≤ 2 * M ^ 2 * ∑ k, η k ^ 2 := by
    intro i
    rw [hξ i]
    simp only [Fin.sum_univ_two]
    have h0 := hMsq 0 i
    have h1 := hMsq 1 i
    nlinarith [sq_nonneg (F 0 i * η 1 - F 1 i * η 0), sq_nonneg (η 0), sq_nonneg (η 1)]
  have hsum : ∑ i, ξ i ^ 2 ≤ 4 * M ^ 2 * ∑ k, η k ^ 2 := by
    simp only [Fin.sum_univ_two] at hcs ⊢
    nlinarith [hcs 0, hcs 1]
  rw [hquad]
  have hpos : 0 < 4 * M ^ 2 + 1 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  have hη0 : 0 ≤ ∑ k, η k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith

/-- Entry bound of `AAᵀ` from an entry bound of `A`. -/
theorem metric_entry_le {A : Matrix (Fin 2) (Fin 2) ℝ} {N : ℝ} (hN : ∀ i j, |A i j| ≤ N)
    (i j : Fin 2) : |(A * A.transpose) i j| ≤ 2 * N ^ 2 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN 0 0)
  calc |A i 0 * A j 0 + A i 1 * A j 1| ≤ |A i 0| * |A j 0| + |A i 1| * |A j 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ N * N + N * N := by
        gcongr <;> exact hN _ _
    _ = 2 * N ^ 2 := by ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Finite menus of produced uniform source budgets admit simultaneous carrier selection. -/

theorem uniform_word_higher_source_selection {Y J : Type*} (I : Set ℝ) (N H : ℕ)
    (src : Y → List J → ℝ → Vec 2 → ℂ)
    (flux : Y → List J → ℝ → Vec 2 → ComplexCellVector)
    (hp : ∀ α : List J, α.length ≤ N → ∀ K : ℕ, K + α.length ≤ H →
      ∃ Ns Nf : ℝ, 0 ≤ Ns ∧ 0 ≤ Nf ∧ ∀ y,
        ∃ Q : HigherSourceCarrierData I K (src y α) (flux y α), Q.Ns ≤ Ns ∧ Q.Nf ≤ Nf) :
    ∃ Ns Nf : (List J) → ℕ → ℝ,
      (∀ α K, 0 ≤ Ns α K) ∧ (∀ α K, 0 ≤ Nf α K) ∧
      ∃ Q : ∀ y (α : List J), α.length ≤ N → ∀ K : ℕ, K + α.length ≤ H →
        HigherSourceCarrierData I K (src y α) (flux y α),
      (∀ y α hα K hK, (Q y α hα K hK).Ns ≤ Ns α K) ∧
      (∀ y α hα K hK, (Q y α hα K hK).Nf ≤ Nf α K) := by
  classical
  have hall (α : List J) (K : ℕ) : ∃ Ns Nf : ℝ, 0 ≤ Ns ∧ 0 ≤ Nf ∧
      ∀ (_ : α.length ≤ N) (_ : K + α.length ≤ H) (y : Y),
        ∃ Q : HigherSourceCarrierData I K (src y α) (flux y α), Q.Ns ≤ Ns ∧ Q.Nf ≤ Nf := by
    by_cases hα : α.length ≤ N
    · by_cases hK : K + α.length ≤ H
      · obtain ⟨Ns, Nf, hNs, hNf, hQ⟩ := hp α hα K hK
        exact ⟨Ns, Nf, hNs, hNf, fun _ _ => hQ⟩
      · exact ⟨0, 0, le_rfl, le_rfl, fun _ hk => (hK hk).elim⟩
    · exact ⟨0, 0, le_rfl, le_rfl, fun ha => (hα ha).elim⟩
  choose Ns Nf hNs hNf Q hQs hQf using hall
  exact ⟨Ns, Nf, hNs, hNf, (fun y α hα K hK => Q α K hα hK y),
    (fun y α hα K hK => hQs α K hα hK y),
    (fun y α hα K hK => hQf α K hα hK y)⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Exact triangular metric-jet difference algebra on literal raw fields. -/

variable {I : Type*}

theorem independentWordMetricFlux_quotient_split
    (G H : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (D E : List I → ℝ → RawJet2 1 ℂ) (α : List I) (r : ℝ) :
    r • (independentWordMetricFlux H E α - independentWordMetricFlux G D α) =
      independentWordMetricFlux (fun β => r • (H β - G β)) E α +
        independentWordMetricFlux G (fun β => r • (E β - D β)) α := by
  simp only [independentWordMetricFlux, independent_list_map_sum_eq_fin_sum]
  rw [← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [cellMetricFlux_difference, smul_add,
    cellMetricFlux_smul_metric, cellMetricFlux_smul_state]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The positive-index Taylor sum in the literal flux is the zero-index source-flux convolution. -/

theorem sum_positive_previous_index {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → E) :
    (∑ j ∈ Finset.Icc 1 N, f (j - 1)) = ∑ j ∈ Finset.range N, f j := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftFluxTaylor_convolution_identity (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : ℕ → Vec 2 → Vec 2 → ∀ i, h i)
    (hΦ : ∀ q, GoodField D (Φ q)) (n : ℕ) (hn : 1 ≤ n)
    (k : Fin 2) (Y z : Vec 2) :
    (∑ j ∈ Finset.Icc 1 (min D n),
      (Real.sqrt η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => sourceFlux edge η ε t (Φ (n - j)) k Y z) 0) =
      Real.sqrt η • ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxCoefficientArray edge η t (Φ (n - 1 - j)) k j Y z := by
  have hs : (∑ j ∈ Finset.Icc 1 (min D n),
      (Real.sqrt η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => sourceFlux edge η ε t (Φ (n - j)) k Y z) 0) =
      Real.sqrt η • ∑ j ∈ Finset.Icc 1 (min D n),
        sourceFluxCoefficientArray edge η t (Φ (n - 1 - (j - 1))) k (j - 1) Y z := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj₁ := (Finset.mem_Icc.mp hj).1
    rw [mul_smul, sourceFluxCoefficientArray_normalized edge hD η t _ (hΦ (n - j))]
    have hq : n - j = n - 1 - (j - 1) := by omega
    rw [hq]
  rw [hs, sum_positive_previous_index (min D n)
    (fun j => sourceFluxCoefficientArray edge η t (Φ (n - 1 - j)) k j Y z)]
  have hm : min D n = min (D - 1) (n - 1) + 1 := by omega
  rw [hm]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Entrywise metric closeness gives the molecular ellipticity constants. -/

theorem metric_close_ellipticity (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, |G i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 / 8)
    (ξ : Fin 2 → ℝ) :
    (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2 := by
  have ht (i j : Fin 2) :
      |(G i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) * ξ i * ξ j| ≤
        (1 / 8) * |ξ i| * |ξ j| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hG i j) (abs_nonneg _)) (abs_nonneg _)
  have he : |∑ i, ∑ j,
      (G i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) * ξ i * ξ j| ≤
        ∑ i, ∑ j, (1 / 8) * |ξ i| * |ξ j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ht i j)
  have hb : (∑ i, ∑ j, (1 / 8 : ℝ) * |ξ i| * |ξ j|) ≤
      (1 / 4) * ∑ i, ξ i ^ 2 := by
    simp only [Fin.sum_univ_two]
    nlinarith [sq_nonneg (|ξ 0| - |ξ 1|), sq_abs (ξ 0), sq_abs (ξ 1)]
  have hid : (∑ i, ∑ j,
      (G i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) * ξ i * ξ j) =
      (∑ i, ∑ j, G i j * ξ i * ξ j) - ∑ i, ξ i ^ 2 := by
    simp only [Fin.sum_univ_two, Matrix.one_apply]
    norm_num
    ring
  rw [hid] at he
  have h := abs_le.mp (he.trans hb)
  constructor <;> linarith [h.1, h.2]

end AVRegularity.EntryWeakProofs
end
end
