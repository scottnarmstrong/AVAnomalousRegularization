-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.LiftSequenceGradedApplyMeanZero
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The centered scalar constant records the actual ordered mean correction sum. -/

def orderedCenteredScalarConstant (hh n p q : ℕ)
    (B : ℕ → ℕ → ℝ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  (1 + (2 : ℝ) ^ p) * K A +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      exponentialLiftCompositionNormalizedConstant j p q A * B ab.1 j *
        ((2 : ℝ) ^ (p + j) * KM ab.2 (n - j) A)

theorem orderedCenteredScalarConstant_nonneg (hh n p q : ℕ)
    (B : ℕ → ℕ → ℝ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (hK : 0 ≤ K A)
    (hKM : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      0 ≤ KM ab.2 (n - j) A) :
    0 ≤ orderedCenteredScalarConstant hh n p q B K KM A := by
  apply add_nonneg (mul_nonneg (by positivity) hK)
  exact Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun ab hab =>
    mul_nonneg (mul_nonneg (exponentialLiftCompositionNormalizedConstant_nonneg j p q A)
      (hB ab.1 j)) (mul_nonneg (by positivity) (hKM j hj ab hab))

/-! The tail majorant records the literal truncated ordered mean convolution. -/

def orderedTailScalarConstant (N D hh n p q : ℕ)
    (B : ℕ → ℕ → ℝ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  K A + ∑ j ∈ Finset.range (N + 1),
    if j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D then
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
        exponentialLiftCompositionNormalizedConstant j p q A * B ab.1 j *
          ((2 : ℝ) ^ (p + j) * KM ab.2 (n - j) A)
    else 0

theorem orderedTailScalarConstant_nonneg (N D hh n p q : ℕ)
    (B : ℕ → ℕ → ℝ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (hK : 0 ≤ K A)
    (hKM : ∀ j ∈ Finset.range (N + 1),
      j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D →
      ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, 0 ≤ KM ab.2 (n - j) A) :
    0 ≤ orderedTailScalarConstant N D hh n p q B K KM A := by
  apply add_nonneg hK
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with hg
  · exact Finset.sum_nonneg fun ab hab =>
      mul_nonneg (mul_nonneg (exponentialLiftCompositionNormalizedConstant_nonneg j p q A)
        (hB ab.1 j)) (mul_nonneg (by positivity) (hKM j hj hg ab hab))
  · exact le_rfl

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The classical finite-past Fourier synthesis represents a public raw cell solution with the original transverse source and zero initial state. -/

theorem profileResponse_exists_raw_solution
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hfm : Measurable (Function.uncurry f))
    (C : Fin 3 → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ 2 (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j : Fin 3, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j.val (f t) x‖ ≤ C j) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ (fun t z => f t (z par.rev)) 0 D ∧
      (∀ t ∈ Icc a b, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube]
        fun z => profileCellResponse (fun r => G r par.rev par.rev) f a t (z par.rev)) ∧
      cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  let g := fun r => G r par.rev par.rev
  let c := fun t n => profileModeResponse g f a t n
  let m := fun n => transverseFourierModeH1 par n
  let u := fun t => ∑' n : ℤ, cellScalarCLM (c t n) (torusHkValueCLM (m n))
  let w := fun t => ∑' n : ℤ, cellH1Scalar (c t n) (m n)
  have hsrc := transverseSource_memLp f hfm par a b (C 0) (by
    intro t ht x hx
    simpa using hj 0 t ht x hx)
  have hz (r : ℝ) : cellSourceSlice (fun _ _ => (0 : ℂ)) r = 0 :=
    cellSourceSlice_eq_of_ae _ r 0 (Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube))
  have hc := profileResponse_cell_curve G hG v V hv hb par ht f a b hab hfm C hC hf hp hj
  have hh : CellWeakHilbertCurve a b u w
      (fun r => cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv hb r (w r)
        (cellSourceSlice (fun t z => f t (z par.rev)) r)
        (fun j => cellSourceSlice (fun t x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) r)) := by
    simpa only [PiLp.zero_apply, hz] using! hc
  obtain ⟨D, hD, htrace⟩ := cellWeakHilbert_exists_raw_solution
    ⟨fun t _ => G t, v, 0, 0⟩ hG V hv hb (fun t z => f t (z par.rev)) 0
    hsrc (MemLp.zero) u w hh
  have hvalue (t : ℝ) (hti : t ∈ Icc a b) : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => profileCellResponse g f a t (z par.rev) := by
    have hgm : AEStronglyMeasurable g volume :=
      ((cellMetric_entry_measurable hG par.rev par.rev).comp
        (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
    have hi : IntegrableOn g (Icc a t) := by
      apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
      exact Filter.Eventually.of_forall fun r => by
        simpa only [Real.norm_eq_abs] using cellMetric_entry_bound hG r 0 par.rev par.rev
    have hs : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl hti.2
    have hcoeff : Summable (c t) := by
      have hsum := profileFourier_jet_summable (c t) 0 (C 0 / (1 / 2)) (by
        intro n hn
        apply profileModeResponse_frequency_weight_bound g f a t (1 / 2) hti.1 (by norm_num) hi
        · intro r hr
          simpa [basisVec_apply, g] using (hG.2.2.2 r 0 (basisVec par.rev)).1
        · exact hC 0
        · exact fun r hr => (hf r (hs hr)).of_le (by norm_num)
        · exact fun r hr => hp r (hs hr)
        · intro r hr x hx
          simpa using hj 0 r (hs hr) x hx
        · exact hn)
      simpa only [pow_zero, one_mul] using hsum
    exact (htrace t).symm.trans (transverseFourierMode_synthesis_ae par (c t) hcoeff)
  refine ⟨D, hD, hvalue, ?_⟩
  simpa only [profileCellResponse_same, Pi.zero_apply] using! hvalue a ⟨le_rfl, hab⟩

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fixed-order paired source budgets include both ordered coefficient and mean differences. -/

def pairedAmbientUncenteredBudget (P Q D R n : ℕ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  pairedUncenteredScalarBudget n (ambientDegreeSlowReserve P R n)
    (ambientDegreeFastReserve Q D 0 R 0 n) A CG Cw CGI Bi Bd

def pairedAmbientCenteredBudget (P Q D R n : ℕ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) (KM : ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  let p := ambientDegreeSlowReserve P R n
  let q := ambientDegreeFastReserve Q D 0 R 0 n
  (1 + (2 : ℝ) ^ p) * pairedAmbientUncenteredBudget P Q D R n CG Cw CGI Bi Bd A +
    ∑ j ∈ Finset.Icc 1 (n - 2), exponentialLiftCompositionNormalizedConstant j p q A *
      (Bd j * ((2 : ℝ) ^ (p + j) * KM (n - j) A) +
        Bi j * ((2 : ℝ) ^ (p + j) *
          pairedAmbientUncenteredBudget P Q D R (n - j) CG Cw CGI Bi Bd A))

theorem pairedAmbientUncenteredBudget_nonneg (P Q D R n : ℕ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) (hBi : ∀ m, 0 ≤ Bi m) (hBd : ∀ m, 0 ≤ Bd m)
    (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ pairedAmbientUncenteredBudget P Q D R n CG Cw CGI Bi Bd A :=
  pairedUncenteredScalarBudget_nonneg _ _ _ _ _ _ _ _ _ hBi hBd

theorem pairedAmbientCenteredBudget_nonneg (P Q D R n : ℕ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) (hBi : ∀ m, 0 ≤ Bi m) (hBd : ∀ m, 0 ≤ Bd m)
    (KM : ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (hKM : ∀ m A, 0 ≤ KM m A)
    (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ pairedAmbientCenteredBudget P Q D R n CG Cw CGI Bi Bd KM A := by
  unfold pairedAmbientCenteredBudget
  apply add_nonneg
  · exact mul_nonneg (by positivity)
      (pairedAmbientUncenteredBudget_nonneg _ _ _ _ _ _ _ _ _ _ hBi hBd A)
  · apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (exponentialLiftCompositionNormalizedConstant_nonneg _ _ _ A)
    apply add_nonneg
    · exact mul_nonneg (hBd j) (mul_nonneg (by positivity) (hKM _ A))
    · exact mul_nonneg (hBi j) (mul_nonneg (by positivity)
        (pairedAmbientUncenteredBudget_nonneg _ _ _ _ _ _ _ _ _ _ hBi hBd A))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Weak uniqueness identifies any actual zero-initial transverse cell solution with the classical Fourier response. -/

theorem cellSolution_eq_profileResponse_ae
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hfm : Measurable (Function.uncurry f))
    (C : Fin 3 → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ 2 (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j : Fin 3, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j.val (f t) x‖ ≤ C j)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ (fun t z => f t (z par.rev)) 0 D)
    (ha : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t ∈ Icc a b, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => profileCellResponse (fun r => G r par.rev par.rev) f a t (z par.rev) := by
  obtain ⟨R, hR, hvalue, hRa⟩ := profileResponse_exists_raw_solution
    G hG v V hv hb par ht f a b hab hfm C hC hf hp hj
  have hsrc := transverseSource_memLp f hfm par a b (C 0) (by
    intro t ht x hx
    simpa using hj 0 t ht x hx)
  have he := cellActual_unique_raw hab ⟨fun t _ => G t, v, 0, 0⟩ hG V 0 hv hb
    measurable_const (fun _ => by simp) (fun t z => f t (z par.rev)) 0
    hsrc (MemLp.zero) D R hD hR (ha.trans hRa.symm)
  intro t ht
  exact (he t ht).trans (hvalue t ht)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The paired source budget reads only strictly earlier coefficient degrees. -/

theorem pairedUncenteredScalarBudget_congr_earlier (n p q : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (CG Cw CGI Bi Bd Be : ℕ → ℝ)
    (heq : ∀ m < n, Bd m = Be m) :
    pairedUncenteredScalarBudget n p q A CG Cw CGI Bi Bd =
      pairedUncenteredScalarBudget n p q A CG Cw CGI Bi Be := by
  unfold pairedUncenteredScalarBudget pairedFirstCrossScalarBudget pairedSecondCrossScalarBudget
  rw [heq (n - 1) (by omega)]
  split_ifs with hn₂
  · rw [heq (n - 2) (by omega)]
  · rfl

theorem pairedAmbientCenteredBudget_congr_earlier (P Q D R n : ℕ) (hn : 1 ≤ n)
    (CG Cw CGI Bi Bd Be : ℕ → ℝ) (heq : ∀ m < n, Bd m = Be m)
    (KM : ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (A : Vec 2 →L[ℝ] ℝ) :
    pairedAmbientCenteredBudget P Q D R n CG Cw CGI Bi Bd KM A =
      pairedAmbientCenteredBudget P Q D R n CG Cw CGI Bi Be KM A := by
  have hUn (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
      pairedAmbientUncenteredBudget P Q D R m CG Cw CGI Bi Bd A =
      pairedAmbientUncenteredBudget P Q D R m CG Cw CGI Bi Be A :=
    pairedUncenteredScalarBudget_congr_earlier m _ _ hm A CG Cw CGI Bi Bd Be
      (fun j hj => heq j (hj.trans_le hmn))
  unfold pairedAmbientCenteredBudget
  dsimp only
  rw [hUn n hn le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hmem := Finset.mem_Icc.mp hj
  rw [heq j (by omega), hUn (n - j) (by omega) (Nat.sub_le _ _)]

/-! Fixed-data scalar formulas mirror the uncentered, mean, and centered lift sources. -/

def ambientUncenteredBudget (P Q D H R hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  let p := ambientDegreeSlowReserve P R n
  let q := ambientDegreeFastReserve Q D H R hh n
  ambientUncenteredScalarBudget D hh n B
    (ambientFirstCrossScalarConstant (n - 1) p q A CG Cw)
    (ambientSecondCrossScalarConstant (n - 2) p q A CG)
    (fun j => ambientSourceScalarConstant D (n - j) p q j A Cj)

def ambientMeanBudget (P Q D H R hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  (2 : ℝ) ^ ambientDegreeSlowReserve P R n *
    ambientUncenteredBudget P Q D H R hh n CG Cw Cj B A

def ambientCenteredBudget (P Q D H R hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  let p := ambientDegreeSlowReserve P R n
  let q := ambientDegreeFastReserve Q D H R hh n
  ambientCenteredScalarBudget p hh n
    (ambientUncenteredBudget P Q D H R hh n CG Cw Cj B A) B
    (fun h m => ambientMeanBudget P Q D H R h m CG Cw Cj B A)
    (fun j => exponentialLiftCompositionNormalizedConstant j p q A)

theorem ambientUncenteredBudget_nonneg (P Q D H R hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ ambientUncenteredBudget P Q D H R hh n CG Cw Cj B A :=
  ambientUncenteredScalarBudget_nonneg _ _ _ _ _ _ _ hB
    (ambientFirstCrossScalarConstant_nonneg _ _ _ _ _ _)
    (ambientSecondCrossScalarConstant_nonneg _ _ _ _ _)
    (fun j => ambientSourceScalarConstant_nonneg _ _ _ _ j _ _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered composition differences retain diagonal support and one perturbation factor. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_exponential_input_paired_bound (n p q δ r s : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (c ci : LiftCoeff ι h) (g gi : Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v u : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g) (hgi : ContDiff ℝ ((p + n : ℕ) : ℕ∞) gi)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ w,
      IsBoxSmooth p q (fun Y y => c m α t Y y v w))
    (hci : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ w,
      IsBoxSmooth p q (fun Y y => ci m α t Y y v w))
    (lam eps B C Bd Cd : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hBd : 0 ≤ Bd) (hCd : 0 ≤ Cd)
    (A : Vec 2 →L[ℝ] ℝ) (ξ : h u)
    (hbci : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ w, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun z => ci m α t Y z v w) y) X‖ ≤
          (B * (if v = w then 1 else 0)) * lam ^ (n - m + a))
    (hbcd : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ w, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun z => c m α t Y z v w - ci m α t Y z v w) y) X‖ ≤
          ((Bd * eps) * (if v = w then 1 else 0)) * lam ^ (n - m + a))
    (hbg : ∀ w, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y w) X‖ ≤
        (C * (if w = u then 1 else 0) * ‖ξ‖) * lam ^ (δ + a))
    (hbgd : ∀ w, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y w - gi Y w) X‖ ≤
        ((Cd * eps) * (if w = u then 1 else 0) * ‖ξ‖) * lam ^ (δ + a)) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
      (Real.exp ((lam • A) Y))⁻¹ • liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v -
      (Real.exp ((lam • A) Y))⁻¹ • liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • gi Z) t Y y v) z) X‖ ≤
      (exponentialLiftCompositionNormalizedConstant n p q A * (Bd * C + B * Cd)) * eps *
        (if v = u then 1 else 0) * ‖ξ‖ * lam ^ (n + δ + r) := by
  let dc : LiftCoeff ι h := fun m α a Y y i j => c m α a Y y i j - ci m α a Y y i j
  let dg := fun Y => g Y - gi Y
  let F := fun (_ _ : ι) => (0 : ℝ)
  have hF : ∀ i j, 0 ≤ F i j := fun _ _ => le_rfl
  have hdc m (hm : m ≤ n) α w : IsBoxSmooth p q (fun Y y => dc m α t Y y v w) :=
    (hc m hm α w).sub (hci m hm α w)
  have hdg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) dg := hg.sub hgi
  have hgexp : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun Y => Real.exp ((lam • A) Y) • g Y) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul hg
  have hgiexp : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun Y => Real.exp ((lam • A) Y) • gi Y) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul hgi
  have hdgexp : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun Y => Real.exp ((lam • A) Y) • dg Y) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul hdg
  let U := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n dc (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v
  let V := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • dg Z) t Y y v
  have hU : IsBoxSmooth p q U := exponential_normalization_box_reserve p q (lam • A) _
    (liftApply_component_box_reserve n p q dc _ t v hgexp hdc)
  have hV : IsBoxSmooth p q V := exponential_normalization_box_reserve p q (lam • A) _
    (liftApply_component_box_reserve n p q ci _ t v hdgexp hci)
  have he (Y y : Vec 2) :
      (Real.exp ((lam • A) Y))⁻¹ • liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v -
      (Real.exp ((lam • A) Y))⁻¹ • liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • gi Z) t Y y v =
      U Y y + V Y y := by
    have hh := liftApply_paired_difference n c ci
      (fun _ Z => Real.exp ((lam • A) Z) • g Z) (fun _ Z => Real.exp ((lam • A) Z) • gi Z) t
      (hgexp.of_le (by exact_mod_cast (show n ≤ p + n by omega)))
      (hgiexp.of_le (by exact_mod_cast (show n ≤ p + n by omega))) Y y v
    dsimp only [U, V, dc, dg]
    simp_rw [smul_sub]
    rw [← smul_sub, hh, smul_add]
  simp_rw [he]
  apply (norm_mixed_jet_add_le (hU.mono hr hs) (hV.mono hr hs) X z).trans
  have hu := liftApply_exponential_input_power_bound n r s δ 0 0 dc g t X v u
    (hg.of_le (by exact_mod_cast Nat.add_le_add_right hr n))
    (fun m hm α w => (hdc m hm α w).mono hr hs) lam hlam A F hF (Bd * eps) C
    (mul_nonneg hBd heps) hC ξ
    (fun m hm α w a ha b hb y => by simpa only [dc, finiteMatrixPower_zero] using hbcd m hm α w a (ha.trans hr) b (hb.trans hs) y)
    (fun w a ha => by simpa only [finiteMatrixPower_zero] using hbg w a (ha.trans (Nat.add_le_add_right hr n))) z
  have hv := liftApply_exponential_input_power_bound n r s δ 0 0 ci dg t X v u
    (hdg.of_le (by exact_mod_cast Nat.add_le_add_right hr n))
    (fun m hm α w => (hci m hm α w).mono hr hs) lam hlam A F hF B (Cd * eps)
    hB (mul_nonneg hCd heps) ξ
    (fun m hm α w a ha b hb y => by simpa only [finiteMatrixPower_zero] using hbci m hm α w a (ha.trans hr) b (hb.trans hs) y)
    (fun w a ha => by simpa only [dg, Pi.sub_apply, finiteMatrixPower_zero] using hbgd w a (ha.trans (Nat.add_le_add_right hr n))) z
  have hweight : 0 ≤ (Bd * C + B * Cd) * eps * (if v = u then (1 : ℝ) else 0) * ‖ξ‖ * lam ^ (n + δ + r) := by
    positivity
  apply (add_le_add hu hv).trans
  simp only [Nat.zero_add, finiteMatrixPower_zero]
  have hk := mul_le_mul_of_nonneg_right
    (exponentialLiftCompositionNormalizedConstant_mono n r s p q hr hs A) hweight
  convert hk using 1 <;> ring

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The synthesized Fourier response is itself a classical representative of the actual finite-past weak solution. -/

theorem profileResponse_classical_solution
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hfm : Measurable (Function.uncurry f))
    (q : ℕ) (hq : 2 ≤ q) (C : ℕ → ℝ) (hC : ∀ j ≤ q, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ q (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f t) x‖ ≤ C j) :
    IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ (fun t z => f t (z par.rev)) 0
      (fun t => classicalCellJet (fun z => profileCellResponse
        (fun r => G r par.rev par.rev) f a t (z par.rev))) := by
  let g := fun r => G r par.rev par.rev
  let c : ℝ → Vec 2 → ℂ := fun t z => profileCellResponse g f a t (z par.rev)
  have hgm : AEStronglyMeasurable g volume :=
    ((cellMetric_entry_measurable hG par.rev par.rev).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
  have hgb (r : ℝ) : |g r| ≤ 2 := cellMetric_entry_bound hG r 0 par.rev par.rev
  have hgl (r : ℝ) (_ : r ∈ Icc a b) : (1 / 2 : ℝ) ≤ g r := by
    simpa [basisVec_apply, g] using (hG.2.2.2 r 0 (basisVec par.rev)).1
  have hi : IntegrableOn g (Icc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hgb r
  have hcd t (ht' : t ∈ Icc a b) : ContDiff ℝ q (profileCellResponse g f a t) :=
    profileCellResponse_contDiff g f a t (1 / 2) ht'.1 (by norm_num)
      (hi.mono_set (Icc_subset_Icc le_rfl ht'.2)) (fun r hr => hgl r ⟨hr.1, hr.2.trans ht'.2⟩)
      q C hC (fun r hr => hf r ⟨hr.1, hr.2.trans ht'.2⟩)
      (fun r hr => hp r ⟨hr.1, hr.2.trans ht'.2⟩)
      (fun j hj' r hr => hj j hj' r ⟨hr.1, hr.2.trans ht'.2⟩)
  have hcl j (hj' : j ≤ q) := profileCellResponse_iteratedDeriv_joint_continuousOn
    g f a b (1 / 2) 2 hab (by norm_num) hi hgl (by norm_num) hgm hgb hfm q C hC hf hp hj j hj'
  obtain ⟨D, hD, hvalue, _⟩ := profileResponse_exists_raw_solution G hG v V hv hb par ht f a b hab
    hfm (fun j : Fin 3 => C j.val) (fun j => hC j.val (by omega))
    (fun t ht' => (hf t ht').of_le (by exact_mod_cast hq)) hp
    (fun j t ht' x hx => hj j.val (by omega) t ht' x hx)
  apply cellSolution_classical_representative (Icc a b) _ _ _ D (fun t => classicalCellJet (c t))
    hD measurableSet_Icc
  · intro t ht'
    apply classicalCellJet_periodicWeak
    · exact ((hcd t ht').comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) par.rev).contDiff)).of_le
        (by exact_mod_cast (show 1 ≤ q by omega))
    · exact periodic_scalar_profile par.rev _ (profileCellResponse_periodic g f a t)
  · intro α
    apply classicalProfileJet_joint_aestronglyMeasurable (Icc a b) measurableSet_Icc _ par.rev
      (fun t ht' => (hcd t ht').differentiable (by
        exact_mod_cast (show q ≠ 0 by omega)))
    · simpa only [iteratedDeriv_zero, Function.uncurry_def] using hcl 0 (by omega)
    · simpa only [iteratedDeriv_one] using hcl 1 (by omega)
  · intro t ht'
    change cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] (fun z => c t z)
    exact hvalue t ht'

/-! Continuous periodic cell representatives coincide pointwise with the explicit transverse Fourier synthesis. -/

theorem cellSolution_eq_profileResponse
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hfm : Measurable (Function.uncurry f))
    (q : ℕ) (hq : 2 ≤ q) (C : ℕ → ℝ) (hC : ∀ j ≤ q, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ q (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f t) x‖ ≤ C j)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ (fun t z => f t (z par.rev)) 0 D)
    (ha : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (hcont : ∀ t ∈ Icc a b, Continuous (cellValue D t)) :
    ∀ t ∈ Icc a b, cellValue D t =
      fun z => profileCellResponse (fun r => G r par.rev par.rev) f a t (z par.rev) := by
  have hsmall (j : Fin 3) : j.val ≤ q := by omega
  have he := cellSolution_eq_profileResponse_ae G hG v V hv hb par ht f a b hab hfm
    (fun j : Fin 3 => C j.val) (fun j => hC j.val (hsmall j))
    (fun t ht => (hf t ht).of_le (by exact_mod_cast hq)) hp
    (fun j => hj j.val (hsmall j)) D hD ha
  intro t hti
  let g := fun r => G r par.rev par.rev
  have hgm : AEStronglyMeasurable g volume :=
    ((cellMetric_entry_measurable hG par.rev par.rev).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
  have hi : IntegrableOn g (Icc a t) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs] using cellMetric_entry_bound hG r 0 par.rev par.rev
  have hs : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl hti.2
  have hnew : ContDiff ℝ q (fun z : Vec 2 => profileCellResponse g f a t (z par.rev)) := by
    apply profileResponse_transverse_contDiff g f a t (1 / 2) hti.1 (by norm_num) hi
    · intro r hr
      simpa [basisVec_apply, g] using (hG.2.2.2 r 0 (basisVec par.rev)).1
    · exact hC
    · exact fun r hr => hf r (hs hr)
    · exact fun r hr => hp r (hs hr)
    · exact fun j hjq r hr => hj j hjq r (hs hr)
  have heq := periodicContinuous_eq_of_cell_ae (cellValue D t) _ (hcont t hti)
    hnew.continuous (hD.2.2.1 t hti).2 (profileResponse_transverse_periodic g f a t par) (he t hti)
  exact heq

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Each actual edge-source term advances the physical matrix power by one height. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_source_lift_power_bound
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q j p' q' : ℕ) (hhh : hh ≤ H) (hj : j ≤ D)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (hp' : max D (p + j) ≤ p') (hq' : max D (q + D - j) ≤ q') (C : ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n)
      (fun v u => C * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply n (Cc hh n) (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (ambientSourceScalarConstant D n p q j A Cj * C *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) (hh + 1) v u * ‖ξ‖) *
          lam ^ (n + j + r) := by
  have hb := setting_ambient_source_lift_bound P sX sZ Cc hseq hh n p q j p' q'
    hhh hj hp hq hp' hq' _ data A t ht v u ξ r s hr hs X z
  rw [finiteMatrixProduct_edge_scalar_power] at hb
  convert hb using 1
  unfold ambientSourceScalarConstant
  ring
end

/-! Each actual edge-source term advances the physical matrix power by one height. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_source_lift_power_bound_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q j p' q' : ℕ) (hj : j ≤ D)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (hp' : max D (p + j) ≤ p') (hq' : max D (q + D - j) ≤ q') (C : ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n)
      (fun v u => C * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply n (Cc hh n) (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (ambientSourceScalarConstant D n p q j A Cj * C *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) (hh + 1) v u * ‖ξ‖) *
          lam ^ (n + j + r) := by
  have hb := setting_ambient_source_lift_bound_of_coefficients P Cc hper hh n p q j p' q'
    hj hp hq hp' hq' _ data A t ht v u ξ r s hr hs X z
  rw [finiteMatrixProduct_edge_scalar_power] at hb
  convert hb using 1
  unfold ambientSourceScalarConstant
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Every scalar source formula reads only coefficient budgets preceding its own rank. -/

theorem ambientUncenteredBudget_congr_earlier (P Q D H R hh n : ℕ) (hn : n ≤ R)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B C : ℕ → ℕ → ℝ)
    (heq : ∀ h m, ambientRecurrenceRank R h m < ambientRecurrenceRank R hh n →
      B h m = C h m) (A : Vec 2 →L[ℝ] ℝ) :
    ambientUncenteredBudget P Q D H R hh n CG Cw Cj B A =
      ambientUncenteredBudget P Q D H R hh n CG Cw Cj C A :=
  ambientUncenteredScalarBudget_congr_earlier R D hh n hn B C heq _ _ _

theorem ambientMeanBudget_congr_earlier (P Q D H R hh n : ℕ) (hn : n ≤ R)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B C : ℕ → ℕ → ℝ)
    (heq : ∀ h m, ambientRecurrenceRank R h m < ambientRecurrenceRank R hh n →
      B h m = C h m) (A : Vec 2 →L[ℝ] ℝ) :
    ambientMeanBudget P Q D H R hh n CG Cw Cj B A =
      ambientMeanBudget P Q D H R hh n CG Cw Cj C A := by
  unfold ambientMeanBudget
  rw [ambientUncenteredBudget_congr_earlier P Q D H R hh n hn CG Cw Cj B C heq A]

theorem ambientCenteredBudget_congr_earlier (P Q D H R hh n : ℕ) (hn : n ≤ R)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B C : ℕ → ℕ → ℝ)
    (heq : ∀ h m, ambientRecurrenceRank R h m < ambientRecurrenceRank R hh n →
      B h m = C h m) (A : Vec 2 →L[ℝ] ℝ) :
    ambientCenteredBudget P Q D H R hh n CG Cw Cj B A =
      ambientCenteredBudget P Q D H R hh n CG Cw Cj C A := by
  unfold ambientCenteredBudget ambientCenteredScalarBudget
  dsimp only
  rw [ambientUncenteredBudget_congr_earlier P Q D H R hh n hn CG Cw Cj B C heq A]
  congr 1
  unfold ambientCorrectionScalarBudget
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  apply Finset.sum_congr rfl
  intro ab hab
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hc := ambientRecurrenceRank_composition R hh n ab.1 j (by omega) hn (by omega)
  have hm := ambientRecurrenceRank_composition R hh n ab.2 (n - j) (by omega) hn (by omega)
  rw [heq ab.1 j hc]
  dsimp only
  rw [ambientMeanBudget_congr_earlier P Q D H R ab.2 (n - j) (by omega)
    CG Cw Cj B C (fun h m hl => heq h m (hl.trans hm)) A]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The frozen cell metric supplies every scalar diffusion premise for the existing classical response. -/

theorem profileCellResponse_metric_contDiff
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (par : Fin 2) (f : ℝ → ℝ → ℂ) (a b : ℝ) (q : ℕ) (C : ℕ → ℝ)
    (hC : ∀ j ≤ q, 0 ≤ C j) (hf : ∀ t ∈ Icc a b, ContDiff ℝ q (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f t) x‖ ≤ C j) (t : ℝ) (ht : t ∈ Icc a b) :
    ContDiff ℝ q (profileCellResponse (fun r => G r par.rev par.rev) f a t) := by
  let g := fun r => G r par.rev par.rev
  have hgm : AEStronglyMeasurable g volume :=
    ((cellMetric_entry_measurable hG par.rev par.rev).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
  have hi : IntegrableOn g (Icc a t) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs] using cellMetric_entry_bound hG r 0 par.rev par.rev
  have hgl (r : ℝ) (_ : r ∈ Icc a t) : (1 / 2 : ℝ) ≤ g r := by
    simpa [basisVec_apply, g] using (hG.2.2.2 r 0 (basisVec par.rev)).1
  exact profileCellResponse_contDiff g f a t (1 / 2) ht.1 (by norm_num) hi hgl q C hC
    (fun r hr => hf r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun r hr => hp r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun j hj' r hr => hj j hj' r ⟨hr.1, hr.2.trans ht.2⟩)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual inverse uniqueness and symmetric coefficient extraction close one triangular lift step. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_positive_coefficients_unique_of_predecessors
    (sX sZ sX' sZ' : ℕ) (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hd : IsLiftSequence Q sX' sZ' a b N H Dc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m (α : DerivativeWord2 m) t, t ∈ Set.Icc a b → ∀ X z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X z : Vec 2) (v u : ι) : Cc hh n m α t X z v u = Dc hh n m α t X z v u := by
  classical
  by_cases hmn : n < m
  · rw [hc.2.2.2.1 hh hhh n m hmn, hd.2.2.2.1 hh hhh n m hmn]
  · apply symmetric_lift_coefficient_eq_of_operator_eq n m (by omega)
      (Cc hh n) (Dc hh n) (hc.2.2.2.2.1 hh hhh n m) (hd.2.2.2.2.1 hh hhh n m)
      t X z v u
    intro a₀ ha₀
    have hC := hc.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X
    have hD := hd.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X
    have hhEq := setting_cellFieldInverse_unique P X sZ sZ' (fun _ => 0)
      (fun r y => liftCellSource Q Cc (fun _ => a₀) hh n r X y)
      (fun r y => liftCellSource Q Dc (fun _ => a₀) hh n r X y)
      (fun r y => liftApply n (Cc hh n) (fun _ => a₀) r X y)
      (fun r y => liftApply n (Dc hh n) (fun _ => a₀) r X y) hC hD (by
        intro r hr
        have hs := liftCellSource_congr_predecessors Q Cc Dc (fun _ => a₀) hh n hn r
          (fun p q hpq m β Y y w j => he p q hpq m β r hr Y y w j)
        exact congrFun hs X)
    exact congrFun (congrFun (hhEq t ht) z) v

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The literal ordered correction constants equal the scalar recursion's common-reserve formula. -/

theorem orderedCenteredScalarConstant_eq_ambientCenteredBudget (P Q D H R hh n : ℕ)
    (hn : n ≤ R) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ) :
    orderedCenteredScalarConstant hh n (ambientDegreeSlowReserve P R n)
      (ambientDegreeFastReserve Q D H R hh n) B
      (ambientUncenteredBudget P Q D H R hh n CG Cw Cj B)
      (fun h m => ambientUncenteredBudget P Q D H R h m CG Cw Cj B) =
        ambientCenteredBudget P Q D H R hh n CG Cw Cj B := by
  funext A
  unfold orderedCenteredScalarConstant ambientCenteredBudget ambientCenteredScalarBudget
    ambientCorrectionScalarBudget
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  apply Finset.sum_congr rfl
  intro ab _
  unfold ambientMeanBudget
  rw [← ambientDegreeSlowReserve_source P R n j hn (by omega)]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual lift recurrence uniquely determines coefficients, independently of stored jet orders. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_coefficients_unique (sX sZ sX' sZ' : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hd : IsLiftSequence Q sX' sZ' a b N H Dc) :
    ∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) t, t ∈ Set.Icc a b → ∀ X z v u,
      Cc hh n m α t X z v u = Dc hh n m α t X z v u := by
  intro hh
  induction hh using Nat.strong_induction_on with
  | h hh ih =>
    intro hhh n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      by_cases hnN : N < n
      · intro m α t _ X z v u
        rw [hc.2.2.1 hh hhh n hnN, hd.2.2.1 hh hhh n hnN]
      · by_cases hn0 : n = 0
        · subst n
          exact liftSequence_zero_degree_coefficients_unique Q sX sZ sX' sZ' a b N H
            Cc Dc hc hd hh hhh
        · apply liftSequence_positive_coefficients_unique_of_predecessors P sX sZ sX' sZ'
            Cc Dc hc hd hh n hhh (by omega) (by omega)
          intro p q hpq
          rcases hpq with hp | ⟨hp, hq⟩
          · exact ih p hp (by omega) q
          · subst p
            exact ihn q hq

end AVRegularity.CycleComparison.Lift
end
