-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The actual inverse of a transverse profile is transverse by weak uniqueness. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_profile_transverse
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun tx : ℝ × Vec 2 => v tx.1 tx.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → ℝ → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (sZ q : ℕ) (hq : 2 ≤ q) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X,
      Measurable (fun tx : ℝ × ℝ => ((l (f tx.1 X tx.2) : ℝ) : ℂ)))
    (hf : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, ∀ X,
      ContDiff ℝ q (fun x => ((l (f t X x) : ℝ) : ℂ)))
    (hp : ∀ t ∈ Icc a b, ∀ X, Function.Periodic (f t X) 1)
    (C : (E →L[ℝ] ℝ) → Vec 2 → ℕ → ℝ)
    (hC : ∀ l X j, j ≤ q → 0 ≤ C l X j)
    (hj : ∀ l j, j ≤ q → ∀ t ∈ Icc a b, ∀ X, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) x‖ ≤ C l X j) :
    IsTransverseOn par (Icc a b) c := by
  intro t ht X z s
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  apply Complex.ofReal_injective
  have he := cellFieldInverse_dual_eq_profileResponse (fun t => G t X) (hG X) v V hv hb
    par htrans (fun t => f t X) (fun t => c t X) sZ a b hab (hc X) l (hfm l X)
    q hq (C l X) (hC l X) (fun t ht => hf l t ht X)
    (fun t ht x => congrArg (fun y => ((l y : ℝ) : ℂ)) (hp t ht X x))
    (fun j hj' t ht x hx => hj l j hj' t ht X x hx) t ht
  rw [congrFun he (z + s • basisVec par), congrFun he z]
  congr 1
  fin_cases par <;> simp [basisVec_apply]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual paired predecessor coefficients and means supply the full centered source difference estimate. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_centered_paired_grading (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam eps : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps) (n p q : ℕ)
    (Q Qi : LiftOperatorData ι h D) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (B₀ Bi Bd : ℕ → ℝ) (hBi : ∀ j, 0 ≤ Bi j) (hBd : ∀ j, 0 ≤ Bd j)
    (K Ki Kd : (Vec 2 →L[ℝ] ℝ) → ℝ) (hKd : ∀ A, 0 ≤ Kd A)
    (KM KMi KMd : ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ) (hKMd : ∀ j A, 0 ≤ KMd j A)
    (uncentered : AmbientLiftUncenteredData par a b hab lam 0 n p q Q Cc K
      (fun v u => if v = u then 1 else 0))
    (uncenteredi : AmbientLiftUncenteredData par a b hab lam 0 n p q Qi Ci Ki
      (fun v u => if v = u then 1 else 0))
    (huncentered : ∀ A u v ξ, ∀ r ≤ p, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 n (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField Qi Ci 0 n (lam • A) u v ξ t Y y) z) X‖ ≤
        (Kd A * (if v = u then 1 else 0) * ‖ξ‖) * eps * lam ^ (n + r))
    (coef : ∀ j ∈ Finset.Icc 1 (n - 2),
      AmbientLiftCoefficientData par a b hab lam j p q (Cc 0 j)
        (fun v u => B₀ j * (if v = u then 1 else 0)))
    (coefi : ∀ j ∈ Finset.Icc 1 (n - 2),
      AmbientLiftCoefficientData par a b hab lam j p q (Ci 0 j)
        (fun v u => Bi j * (if v = u then 1 else 0)))
    (coefd : ∀ j ∈ Finset.Icc 1 (n - 2),
      AmbientLiftCoefficientData par a b hab lam j p q
        (fun m α t X z v u => Cc 0 j m α t X z v u - Ci 0 j m α t X z v u)
        (fun v u => (Bd j * (if v = u then 1 else 0)) * eps))
    (mean : ∀ j ∈ Finset.Icc 1 (n - 2),
      AmbientLiftUncenteredData par a b hab lam 0 (n - j) (p + j) q Q Cc (KM (n - j))
        (fun v u => if v = u then 1 else 0))
    (meani : ∀ j ∈ Finset.Icc 1 (n - 2),
      AmbientLiftUncenteredData par a b hab lam 0 (n - j) (p + j) q Qi Ci (KMi (n - j))
        (fun v u => if v = u then 1 else 0))
    (hmeand : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ A u v ξ,
      ∀ r ≤ p + j, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 (n - j) (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField Qi Ci 0 (n - j) (lam • A) u v ξ t Y y) z) X‖ ≤
        (KMd (n - j) A * (if v = u then 1 else 0) * ‖ξ‖) * eps * lam ^ ((n - j) + r))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z =>
      normalizedLiftSourceField Q Cc 0 n (lam • A) u v ξ t X z -
      normalizedLiftSourceField Qi Ci 0 n (lam • A) u v ξ t X z) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftSourceField Q Cc 0 n (lam • A) u v ξ t Y y -
        normalizedLiftSourceField Qi Ci 0 n (lam • A) u v ξ t Y y) z) X‖ ≤
        (((1 + (2 : ℝ) ^ p) * Kd A +
          ∑ j ∈ Finset.Icc 1 (n - 2), exponentialLiftCompositionNormalizedConstant j p q A *
            (Bd j * ((2 : ℝ) ^ (p + j) * KM (n - j) A) +
              Bi j * ((2 : ℝ) ^ (p + j) * KMd (n - j) A))) *
          (if v = u then 1 else 0) * ‖ξ‖) * eps * lam ^ (n + r) := by
  have hcorr j (hj : j ∈ Finset.Icc 1 (n - 2)) :=
    ambient_ordered_mean_paired_grading par a b hab lam eps hlam heps j (n - j) p q
      Q Qi Cc Ci (B₀ j) (Bi j) (Bd j) (hBi j) (hBd j)
      (KM (n - j)) (KMi (n - j)) (KMd (n - j)) (hKMd (n - j))
      (coef j hj) (coefi j hj) (coefd j hj) (mean j hj) (meani j hj)
      (hmeand j hj) A u v ξ t ht
  let BC := fun j => exponentialLiftCompositionNormalizedConstant j p q A *
    (Bd j * ((2 : ℝ) ^ (p + j) * KM (n - j) A) +
      Bi j * ((2 : ℝ) ^ (p + j) * KMd (n - j) A)) *
    (if v = u then 1 else 0) * ‖ξ‖
  have hs := liftCellSource_zero_height_paired_grading_of_terms Q Qi Cc Ci
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) n p q t v A lam eps
    (Kd A * (if v = u then 1 else 0) * ‖ξ‖) hlam heps
    (mul_nonneg (mul_nonneg (hKd A) (by split_ifs <;> norm_num)) (norm_nonneg ξ))
    (fun w => uncentered.box A u w ξ t ht) (fun w => uncenteredi.box A u w ξ t ht)
    (fun r hr s hs X z => huncentered A u v ξ r hr s hs t ht X z)
    BC (fun j hj => (hcorr j hj).1)
    (fun j hj r hr s hs X z => (hcorr j hj).2 r hr s hs X z |>.trans_eq (by
      have hmem := Finset.mem_Icc.mp hj
      rw [show j + (n - j) = n by omega]
      dsimp only [BC]
      ring))
  refine ⟨hs.1, ?_⟩
  intro r hr s hsq X z
  exact (hs.2 r hr s hsq X z).trans_eq (by
    dsimp only [BC]
    simp only [add_mul, Finset.sum_mul]
    ring)

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! A single mean coefficient constant is chosen before scales and component families. -/

def ambientMeanGradeConstant (P N k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  finiteFourBudget H (N + D) (N + D) (P + 1) (fun hh n m r =>
    ambientPositiveMeanFluxConstant P N k L D H hh n m r CG Cw Cj +
    ambientDiagonalMeanFluxConstant P N k L D H n m r CG Cw Cj)

theorem ambientMeanGradeConstant_nonneg (P N k L D H : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : 0 ≤ ambientMeanGradeConstant P N k L D H CG Cw Cj :=
  finiteFourBudget_nonneg _ _ _ _ _ fun hh n m r => add_nonneg
    (ambientPositiveMeanFluxConstant_nonneg P N k L D H hh n m r CG Cw Cj)
    (ambientDiagonalMeanFluxConstant_nonneg P N k L D H n m r CG Cw Cj)

theorem ambientMeanGradeConstant_entry_le (P N k L D H : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (hh n m r : ℕ)
    (hhh : hh ≤ H) (hn : n ≤ N + D) (hm : m ≤ N + D) (hr : r ≤ P + 1) :
    ambientPositiveMeanFluxConstant P N k L D H hh n m r CG Cw Cj +
      ambientDiagonalMeanFluxConstant P N k L D H n m r CG Cw Cj ≤
        ambientMeanGradeConstant P N k L D H CG Cw Cj :=
  finiteFourBudget_le _ _ _ _ _ (fun hh n m r => add_nonneg
    (ambientPositiveMeanFluxConstant_nonneg P N k L D H hh n m r CG Cw Cj)
    (ambientDiagonalMeanFluxConstant_nonneg P N k L D H n m r CG Cw Cj))
    hh n m r hhh hn hm hr

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The actual weak inverse has the classical time primitive in every real dual coordinate. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_dual_time_integral
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (c : ℝ → Vec 2 → E) (sZ : ℕ) (hsZ : 2 ≤ sZ)
    (a b : ℝ) (hab : a ≤ b)
    (hc : IsCellFieldInverse G v sZ a b 0 (fun t z => f t (z par.rev)) c)
    (l : E →L[ℝ] ℝ)
    (hfm : Measurable (fun p : ℝ × ℝ => ((l (f p.1 p.2) : ℝ) : ℂ)))
    (C : ℕ → ℝ) (hC : ∀ j ≤ 2, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ 2 (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ j ≤ 2, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C j)
    (t : ℝ) (ht : t ∈ Icc a b) (z : Vec 2) :
    let R := fun s => ((l (-cellOperator (G s) (v s) (c s) z + f s (z par.rev)) : ℝ) : ℂ)
    IntervalIntegrable R volume a t ∧ ((l (c t z) : ℝ) : ℂ) = ∫ s in a..t, R s := by
  let A : E →L[ℝ] ℂ := Complex.ofRealCLM.comp l
  let F := fun s x => ((l (f s x) : ℝ) : ℂ)
  let g := fun s => G s par.rev par.rev
  have heq := cellFieldInverse_dual_eq_profileResponse G hG v V hv hb par htrans f c sZ a b
    hab hc l hfm 2 le_rfl C hC hf hp hj
  obtain ⟨hgm, hgb, hi, hg⟩ := cellMetric_profile_time_data G hG par a b
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨hInt, htime⟩ := profileCellResponse_time_integral g F a b (1 / 2) 2 hab hpos
    (by norm_num) hi (fun s _ => hg s) hgm hgb hfm C hC hf hp hj t ht (z par.rev)
  have hR (s : ℝ) (hs : s ∈ Icc a b) :
      A (-cellOperator (G s) (v s) (c s) z + f s (z par.rev)) =
        g s • iteratedDeriv 2 (profileCellResponse g F a s) (z par.rev) + F s (z par.rev) := by
    have horder : (2 : ℕ∞) ≤ (sZ : ℕ∞) := by exact_mod_cast hsZ
    have hcs : ContDiff ℝ 2 (c s) := (hc.1 s hs).of_le
      (WithTop.coe_le_coe.mpr horder)
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    have hprof : ContDiff ℝ 2 (profileCellResponse g F a s) :=
      profileCellResponse_contDiff g F a s (1 / 2) hs.1 hpos (hi.mono_set hsub)
        (fun r _ => hg r) 2 C hC (fun r hr => hf r (hsub hr))
        (fun r hr => hp r (hsub hr)) (fun j hj2 r hr => hj j hj2 r (hsub hr))
    rw [map_add, map_neg, ← cellOperator_postcomposition A (G s) (v s) (c s) hcs z]
    change -cellOperator (G s) (v s) (fun y => ((l (c s y) : ℝ) : ℂ)) z + F s (z par.rev) = _
    rw [heq s hs, cellOperator_transverse_profile_tangent_drift (G s) (v s) par
      (htrans s) (profileCellResponse g F a s) hprof z, neg_neg]
  have he (s : ℝ) (hs : s ∈ uIcc a t) := by
    rw [uIcc_of_le ht.1] at hs
    exact hR s ⟨hs.1, hs.2.trans ht.2⟩
  dsimp only
  refine ⟨hInt.congr (fun s hs => (he s (uIoc_subset_uIcc hs)).symm), ?_⟩
  rw [congrFun (heq t ht) z, htime]
  exact intervalIntegral.integral_congr (fun s hs => (he s hs).symm)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit finite-order constants for the primitive tail presentation. -/

def tailEntryTestScalarBudget (K k L D H N hh n m p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (α : DerivativeWord2 m) : ℝ :=
  ∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α 1 j| *
    tailTestScalarBudget K k L D H N hh n p q CG Cw Cj
      ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))

theorem tailEntryTestScalarBudget_nonneg (K k L D H N hh n m p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (α : DerivativeWord2 m) :
    0 ≤ tailEntryTestScalarBudget K k L D H N hh n m p q CG Cw Cj α :=
  Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg (liftCalibrationWeight n m α 1 j))
    (tailTestScalarBudget_nonneg K k L D H N hh n p q CG Cw Cj
      ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)))

def tailWordScalarBudget (K k L D H N hh n m j : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  (2 : ℝ) ^ (j + 2) * ∑ α : DerivativeWord2 m,
    tailEntryTestScalarBudget K k L D H N hh n m (K + D + 2)
      (max (k + 1) (L + 2) - 1) CG Cw Cj α

theorem tailWordScalarBudget_nonneg (K k L D H N hh n m j : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ tailWordScalarBudget K k L D H N hh n m j CG Cw Cj :=
  mul_nonneg (pow_nonneg (by norm_num) _) (Finset.sum_nonneg fun α _ =>
    tailEntryTestScalarBudget_nonneg K k L D H N hh n m _ _ CG Cw Cj α)

def tailPresentationScalarBudget (K k L D H N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (2 * N + D + 1),
    ∑ m ∈ Finset.range (2 * N + D + 1), ∑ j ∈ Finset.range (K + 1),
      tailWordScalarBudget K k L D H N hh n m j CG Cw Cj

theorem tailPresentationScalarBudget_nonneg (K k L D H N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ tailPresentationScalarBudget K k L D H N CG Cw Cj :=
  Finset.sum_nonneg fun hh _ => Finset.sum_nonneg fun n _ =>
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ =>
      tailWordScalarBudget_nonneg K k L D H N hh n m j CG Cw Cj

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The order-only presentation constant dominates each requested word bound. -/

theorem tailWordScalarBudget_le_presentation
    (K k L D H N hh n m j : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (hhh : hh ≤ H) (hn : n ≤ 2 * N + D) (hm : m ≤ 2 * N + D) (hj : j ≤ K) :
    tailWordScalarBudget K k L D H N hh n m j CG Cw Cj ≤
      tailPresentationScalarBudget K k L D H N CG Cw Cj := by
  unfold tailPresentationScalarBudget
  apply le_trans _ (Finset.single_le_sum
    (fun h _ => Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ =>
      Finset.sum_nonneg fun j _ => tailWordScalarBudget_nonneg K k L D H N h n m j CG Cw Cj)
    (Finset.mem_range.mpr (by omega : hh < H + 1)))
  apply le_trans _ (Finset.single_le_sum
    (fun n _ => Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ =>
      tailWordScalarBudget_nonneg K k L D H N hh n m j CG Cw Cj)
    (Finset.mem_range.mpr (by omega : n < 2 * N + D + 1)))
  apply le_trans _ (Finset.single_le_sum
    (fun m _ => Finset.sum_nonneg fun j _ =>
      tailWordScalarBudget_nonneg K k L D H N hh n m j CG Cw Cj)
    (Finset.mem_range.mpr (by omega : m < 2 * N + D + 1)))
  exact Finset.single_le_sum
    (fun j _ => tailWordScalarBudget_nonneg K k L D H N hh n m j CG Cw Cj)
    (Finset.mem_range.mpr (by omega : j < K + 1))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Pointwise vector time-integral equation for the actual transverse weak inverse. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_time_integral
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (c : ℝ → Vec 2 → E) (sZ : ℕ) (hsZ : 2 ≤ sZ)
    (a b : ℝ) (hab : a ≤ b)
    (hc : IsCellFieldInverse G v sZ a b 0 (fun t z => f t (z par.rev)) c)
    (hfm : ∀ l : E →L[ℝ] ℝ,
      Measurable (fun p : ℝ × ℝ => ((l (f p.1 p.2) : ℝ) : ℂ)))
    (C : (E →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ 2 → 0 ≤ C l j)
    (hf : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      ContDiff ℝ 2 (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ 2, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (t : ℝ) (ht : t ∈ Icc a b) (z : Vec 2) :
    IntervalIntegrable (fun s => -cellOperator (G s) (v s) (c s) z + f s (z par.rev)) volume a t ∧
      c t z = ∫ s in a..t, -cellOperator (G s) (v s) (c s) z + f s (z par.rev) := by
  apply timeIntegral_of_all_complexified_real_duals
  intro l
  exact cellFieldInverse_dual_time_integral G hG v V hv hb par htrans f c sZ hsZ
    a b hab hc l (hfm l) (C l) (hC l) (hf l) (hp l) (hj l) t ht z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Centered predecessor coefficient data give source admissibility without a completed lift sequence. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_centered_source_data_of_coefficients (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (hh n p q : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ m ≤ j, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X,
        AVenhance.IsZ2Periodic (fun z => Cc ab.1 j m α t X z v u))
    (hmean : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ m ≤ j, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X, ∀ ξ : h u,
        fieldCellMean (fun z => Cc ab.1 j m α t X z v u ξ) = 0)
    (F : ι → ι → ℝ) (hF : ∀ v u, 0 ≤ F v u) (B : ℕ → ℕ → ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ)
    (uncentered : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K (finiteMatrixPower F hh))
    (coef : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      AmbientLiftCoefficientData par a b hab lam j p q (Cc ab.1 j)
        (fun v u => B ab.1 j * finiteMatrixPower F ab.1 v u))
    (mean : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      AmbientLiftUncenteredData par a b hab lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower F ab.2)) :
    AmbientLiftSourceData par a b hab lam hh n p q Q Cc
      (orderedCenteredScalarConstant hh n p q B K KM) (finiteMatrixPower F hh) := by
  have hg := ambient_ordered_centered_power_grading par a b hab lam hlam hh n p q Q Cc F hF
    B hB K KM uncentered coef mean
  refine ⟨?_, finiteMatrixPower_nonneg F hF hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact orderedCenteredScalarConstant_nonneg hh n p q B K KM A hB
      (uncentered.constant_nonneg A) (fun j hj ab hab' => (mean j hj ab hab').constant_nonneg A)
  · intro A u v ξ t ht
    exact (hg A u v ξ t ht).1
  · intro A u v ξ r hr s hs t ht X z
    exact (hg A u v ξ t ht).2 r hr s hs X z
  · intro A u v ξ
    apply liftCellSource_normalized_transverse_of_terms par (Set.Icc a b) Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n v A lam
      (uncentered.transverse A u v ξ)
    intro j hj ab hab'
    have ht := liftApply_transverse par (Set.Icc a b) j (Cc ab.1 j)
      (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) ab.2 (n - j))
      (coef j hj ab hab').transverse
    intro t ht' X z s
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (ht t ht' X z s)
  · intro A u v ξ l X z
    apply liftCellSource_normalized_clamped_dual_measurable_of_terms Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n a b hab v l A lam X z
      (uncentered.measurable A u v ξ l X z)
      (l.continuous.measurable.comp (uncentered.mean_component_measurable A u v ξ X))
    intro j hj ab hab'
    exact ambient_ordered_mean_clamped_dual_measurable par a b hab lam hlam j (n - j)
      p q (p + j) q ab.2 (by omega) Q Cc (Cc ab.1 j) _ _ (KM ab.2 (n - j))
      (coef j hj ab hab') (mean j hj ab hab') A u v ξ l X z
  · intro A u v ξ t ht
    apply liftCellSource_normalized_periodic_of_terms Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t v A lam
      (uncentered.periodic A u v ξ t ht)
    intro j hj ab hab' X k z
    have hp := liftApply_periodic_of_coefficients j (Cc ab.1 j)
      (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) ab.2 (n - j)) t X
      (fun m hm α v u => hper j hj ab hab' m hm α v u t ht X)
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hp k z)
  · intro A u v ξ t ht X
    unfold normalizedLiftSourceField
    rw [AVRegularity.fieldCellMean_smul]
    rw [liftCellSource_component_mean_zero_of_predecessors Q Cc hh n
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t X v
      (fun j hj ab hab' m hm α u' => ⟨
        (((coef j hj ab hab').box m hm α v u' t ht).1 X).continuous,
        hmean j hj ab hab' m hm α v u' t ht X⟩)
      (liftA_fast_continuous_of_normalized_box Q Cc _ hh n p q t A lam
        (fun w => uncentered.box A u w ξ t ht) X)]
    exact smul_zero _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The paired scalar coefficient step combines genuine metric and source perturbations before data are chosen. -/

def pairedCoefficientScalarStep (P Q D R N n : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (CGI Bd : ℕ → ℝ) : ℝ :=
  let B₀ := fun h m => ambientCoefficientScalarBudget P Q D 0 R N h m CG Cw Cj
  let Bi := fun m => ambientCoefficientScalarBudget P Q D 0 R N 0 m
    (identityMetricJetBudget CG) Cw Cj
  let KM := fun m => ambientUncenteredBudget P Q D 0 R 0 m CG Cw Cj B₀
  let p := ambientDegreeSlowReserve P R n
  if n = 0 then 0 else if N < n then 0 else
    finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N
      (fun A => metricInverseUniformConstant p (metricParameterBudget p CG)
          (metricParameterBudget p CGI) (3 / 4) *
            ambientCenteredBudget P Q D 0 R 0 n CG Cw Cj B₀ A +
        ambientInverseUniformConstant p (metricParameterBudget p (identityMetricJetBudget CG))
          (3 / 4) * pairedAmbientCenteredBudget P Q D R n CG Cw CGI Bi Bd KM A)

theorem pairedCoefficientScalarStep_nonneg (P Q D R N n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI Bd : ℕ → ℝ) :
    0 ≤ pairedCoefficientScalarStep P Q D R N n CG Cw Cj CGI Bd := by
  unfold pairedCoefficientScalarStep
  dsimp only
  split_ifs <;> first
  | exact le_rfl
  | exact mul_nonneg (finiteLiftCalibrationBudget_nonneg N)
      (finiteLiftTestDirectionBudget_nonneg N _)

theorem pairedCoefficientScalarStep_congr_earlier (P Q D R N n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI Bd Be : ℕ → ℝ)
    (heq : ∀ m < n, Bd m = Be m) :
    pairedCoefficientScalarStep P Q D R N n CG Cw Cj CGI Bd =
      pairedCoefficientScalarStep P Q D R N n CG Cw Cj CGI Be := by
  unfold pairedCoefficientScalarStep
  dsimp only
  split_ifs <;> try rfl
  congr 1
  congr 1
  funext A
  rw [pairedAmbientCenteredBudget_congr_earlier P Q D R n (by omega)
    CG Cw CGI _ Bd Be heq _ A]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Strong degree recursion fixes the paired coefficient budget independently of scales and components. -/

def pairedCoefficientScalarBudget (P Q D R N : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) : ℕ → ℝ :=
  Nat.strongRec fun n previous => pairedCoefficientScalarStep P Q D R N n CG Cw Cj CGI
    (fun m => if hm : m < n then previous m hm else 0)

theorem pairedCoefficientScalarBudget_nonneg (P Q D R N n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) :
    0 ≤ pairedCoefficientScalarBudget P Q D R N CG Cw Cj CGI n := by
  unfold pairedCoefficientScalarBudget
  rw [Nat.strongRec_eq]
  exact pairedCoefficientScalarStep_nonneg _ _ _ _ _ _ _ _ _ _ _

theorem pairedCoefficientScalarBudget_eq_step (P Q D R N n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) :
    pairedCoefficientScalarBudget P Q D R N CG Cw Cj CGI n =
      pairedCoefficientScalarStep P Q D R N n CG Cw Cj CGI
        (pairedCoefficientScalarBudget P Q D R N CG Cw Cj CGI) := by
  unfold pairedCoefficientScalarBudget
  conv_lhs => rw [Nat.strongRec_eq]
  apply pairedCoefficientScalarStep_congr_earlier
  intro m hm
  simp only [dite_eq_left hm]

/-! The paired scalar recursion has literal zero, cutoff and positive inverse-calibration equations. -/

theorem pairedCoefficientScalarBudget_zero (P Q D R N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) :
    pairedCoefficientScalarBudget P Q D R N CG Cw Cj CGI 0 = 0 := by
  rw [pairedCoefficientScalarBudget_eq_step]
  simp only [pairedCoefficientScalarStep, ite_true]

theorem pairedCoefficientScalarBudget_cutoff (P Q D R N n : ℕ) (hn : N < n)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) :
    pairedCoefficientScalarBudget P Q D R N CG Cw Cj CGI n = 0 := by
  rw [pairedCoefficientScalarBudget_eq_step]
  simp only [pairedCoefficientScalarStep, ite_eq_right (by omega : n ≠ 0), ite_eq_left hn]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite budgets for the actual paired mean coefficients precede all operator data. -/

def pairedMeanFluxWordBudget (n r : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ) : ℝ :=
  2 ^ r * max (Cw 0) 0 * Bd (n - 1) + if n = 2 then max (CGI r) 0 else 0

def pairedMeanFluxScalarBudget (n m r : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ) : ℝ :=
  ∑ _p : DerivativeWord2 m × Fin 2, pairedMeanFluxWordBudget n r Bd Cw CGI

def pairedMeanScalarBudget (R K : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (R + 1), ∑ m ∈ Finset.range (R + 1),
    ∑ r ∈ Finset.range (K + 1), pairedMeanFluxScalarBudget n m r Bd Cw CGI

theorem pairedMeanFluxWordBudget_nonneg (n r : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ)
    (hBd : ∀ n, 0 ≤ Bd n) : 0 ≤ pairedMeanFluxWordBudget n r Bd Cw CGI := by
  unfold pairedMeanFluxWordBudget
  apply add_nonneg
  · exact mul_nonneg (by positivity) (hBd _)
  · split_ifs <;> positivity

theorem pairedMeanFluxScalarBudget_nonneg (n m r : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ)
    (hBd : ∀ n, 0 ≤ Bd n) : 0 ≤ pairedMeanFluxScalarBudget n m r Bd Cw CGI :=
  Finset.sum_nonneg fun _ _ => pairedMeanFluxWordBudget_nonneg n r Bd Cw CGI hBd

theorem pairedMeanScalarBudget_nonneg (R K : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ)
    (hBd : ∀ n, 0 ≤ Bd n) : 0 ≤ pairedMeanScalarBudget R K Bd Cw CGI :=
  Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun r _ =>
    pairedMeanFluxScalarBudget_nonneg n m r Bd Cw CGI hBd

theorem pairedMeanScalarBudget_dominates (R K n m r : ℕ) (Bd : ℕ → ℝ) (Cw CGI : ℕ → ℝ)
    (hBd : ∀ n, 0 ≤ Bd n) (hn : n ≤ R) (hm : m ≤ R) (hr : r ≤ K) :
    pairedMeanFluxScalarBudget n m r Bd Cw CGI ≤ pairedMeanScalarBudget R K Bd Cw CGI := by
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), pairedMeanFluxScalarBudget n m j Bd Cw CGI :=
      Finset.single_le_sum (fun j _ => pairedMeanFluxScalarBudget_nonneg n m j Bd Cw CGI hBd)
        (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ d ∈ Finset.range (R + 1), ∑ j ∈ Finset.range (K + 1),
        pairedMeanFluxScalarBudget n d j Bd Cw CGI :=
      Finset.single_le_sum (fun d _ => Finset.sum_nonneg fun j _ =>
        pairedMeanFluxScalarBudget_nonneg n d j Bd Cw CGI hBd)
        (Finset.mem_range.mpr (by omega))
    _ ≤ pairedMeanScalarBudget R K Bd Cw CGI :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun j _ =>
        pairedMeanFluxScalarBudget_nonneg i d j Bd Cw CGI hBd)
        (Finset.mem_range.mpr (by omega))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual predecessor states supply the complete simultaneous uncentered induction state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_power_data_of_predecessors
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hn : 1 ≤ n) (hhh : hh ≤ H)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf) (Budget : ℕ → ℕ → ℝ)
    (hBudget : ∀ h m, 0 ≤ Budget h m)
    (data₁ : AmbientLiftCoefficientData par a b P.window lam (n - 1) (p + 1) (q + 1)
      (Cc hh (n - 1)) (fun v u => Budget hh (n - 1) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (data₂ : 2 ≤ n → AmbientLiftCoefficientData par a b P.window lam (n - 2) (p + 2) q
      (Cc hh (n - 2)) (fun v u => Budget hh (n - 2) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (dataS : hh ≠ 0 → ∀ j ≤ min D n,
      AmbientLiftCoefficientData par a b P.window lam (n - j) (max D (p + j))
        (max D (q + D - j)) (Cc (hh - 1) (n - j))
        (fun v u => Budget (hh - 1) (n - j) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) (hh - 1) v u))
 :
    AmbientLiftUncenteredData par a b P.window lam hh n p q Q Cc
      (fun A => ambientUncenteredScalarBudget D hh n Budget
        (ambientFirstCrossScalarConstant (n - 1) p q A CG Cw)
        (ambientSecondCrossScalarConstant (n - 2) p q A CG)
        (fun j => ambientSourceScalarConstant D (n - j) p q j A Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hqs : 1 ≤ qs := by omega
  have hqf : 1 ≤ qf := by omega
  have hg := setting_liftA_power_grading_of_predecessors P sX sZ Cc hseq hh n p q
    hn hhh hp hq Budget data₁ data₂ dataS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact ambientUncenteredScalarBudget_nonneg D hh n Budget _ _ _ hBudget
      (ambientFirstCrossScalarConstant_nonneg _ _ _ _ _ _)
      (ambientSecondCrossScalarConstant_nonneg _ _ _ _ _)
      (fun j => ambientSourceScalarConstant_nonneg _ _ _ _ j _ _)
  · exact finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh
  · intro A u v ξ t ht
    exact (hg A t ht v u ξ).1
  · intro A u v ξ r hr s hs t ht X z
    exact (hg A t ht v u ξ).2 r hr s hs X z
  · intro A u v ξ
    apply liftA_normalized_transverse_of_terms par (Set.Icc a b) Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n v A lam
    · exact setting_first_cross_test_transverse P _ _ _ _ _ data₁ A u v ξ
    · intro hn₂
      exact setting_second_cross_test_transverse P _ _ _ _ _ (data₂ hn₂) A u v ξ
    · intro hh0 j hj
      exact setting_ambient_source_test_transverse P sX sZ Cc hseq (hh - 1) (n - j)
        _ _ (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _) hqs hqf
        _ (dataS hh0 j hj) A u v ξ j
  · intro A u v ξ l X z
    apply liftA_normalized_clamped_dual_measurable_of_terms Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n a b P.window v l A lam X z
    · exact setting_ambient_first_cross_test_measurable P _ _ _ (by omega) (by omega)
        hqs _ _ data₁ A u v ξ l X z
    · intro hn₂
      exact setting_ambient_second_cross_test_measurable P _ _ _ (by omega) hqs
        _ _ (data₂ hn₂) A u v ξ l X z
    · intro hh0 j hj
      have hm := ambient_source_lift_test_clamped_measurable Q (by have hd := P.D_ge; omega)
        sX sZ N H a b P.window Cc hseq (hh - 1) (n - j) _ _ (by omega)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) par lam _ (dataS hh0 j hj)
        P.coeff_meas
        (fun t ht v u d γ hγ α => (P.coeff_smooth v u d γ hγ α t ht).mono hqs hqf)
        A u v ξ j X z
      exact l.continuous.measurable.comp hm
  · intro A u v ξ t ht X
    exact setting_liftA_normalized_test_periodic P sX sZ Cc hseq hh n p q hhh hqs hqf
      _ dataS A u v ξ t ht X
end

/-! Actual predecessor states supply the complete simultaneous uncentered induction state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_power_data_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q : ℕ) (hn : 1 ≤ n)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf) (Budget : ℕ → ℕ → ℝ)
    (hBudget : ∀ h m, 0 ≤ Budget h m)
    (data₁ : AmbientLiftCoefficientData par a b P.window lam (n - 1) (p + 1) (q + 1)
      (Cc hh (n - 1)) (fun v u => Budget hh (n - 1) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (data₂ : 2 ≤ n → AmbientLiftCoefficientData par a b P.window lam (n - 2) (p + 2) q
      (Cc hh (n - 2)) (fun v u => Budget hh (n - 2) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (dataS : hh ≠ 0 → ∀ j ≤ min D n,
      AmbientLiftCoefficientData par a b P.window lam (n - j) (max D (p + j))
        (max D (q + D - j)) (Cc (hh - 1) (n - j))
        (fun v u => Budget (hh - 1) (n - j) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) (hh - 1) v u))
 :
    AmbientLiftUncenteredData par a b P.window lam hh n p q Q Cc
      (fun A => ambientUncenteredScalarBudget D hh n Budget
        (ambientFirstCrossScalarConstant (n - 1) p q A CG Cw)
        (ambientSecondCrossScalarConstant (n - 2) p q A CG)
        (fun j => ambientSourceScalarConstant D (n - j) p q j A Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hqs : 1 ≤ qs := by omega
  have hqf : 1 ≤ qf := by omega
  have hg := setting_liftA_power_grading_of_coefficients P Cc hper hh n p q
    hn hp hq Budget data₁ data₂ dataS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact ambientUncenteredScalarBudget_nonneg D hh n Budget _ _ _ hBudget
      (ambientFirstCrossScalarConstant_nonneg _ _ _ _ _ _)
      (ambientSecondCrossScalarConstant_nonneg _ _ _ _ _)
      (fun j => ambientSourceScalarConstant_nonneg _ _ _ _ j _ _)
  · exact finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh
  · intro A u v ξ t ht
    exact (hg A t ht v u ξ).1
  · intro A u v ξ r hr s hs t ht X z
    exact (hg A t ht v u ξ).2 r hr s hs X z
  · intro A u v ξ
    apply liftA_normalized_transverse_of_terms par (Set.Icc a b) Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n v A lam
    · exact setting_first_cross_test_transverse P _ _ _ _ _ data₁ A u v ξ
    · intro hn₂
      exact setting_second_cross_test_transverse P _ _ _ _ _ (data₂ hn₂) A u v ξ
    · intro hh0 j hj
      exact setting_ambient_source_test_transverse_of_coefficients P Cc hper (hh - 1) (n - j)
        _ _ (Nat.le_max_left _ _) (Nat.le_max_left _ _) hqs hqf
        _ (dataS hh0 j hj) A u v ξ j
  · intro A u v ξ l X z
    apply liftA_normalized_clamped_dual_measurable_of_terms Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n a b P.window v l A lam X z
    · exact setting_ambient_first_cross_test_measurable P _ _ _ (by omega) (by omega)
        hqs _ _ data₁ A u v ξ l X z
    · intro hn₂
      exact setting_ambient_second_cross_test_measurable P _ _ _ (by omega) hqs
        _ _ (data₂ hn₂) A u v ξ l X z
    · intro hh0 j hj
      have hm := ambient_source_lift_test_clamped_measurable_of_coefficients Q (by have hd := P.D_ge; omega)
        a b P.window Cc hper (hh - 1) (n - j) _ _
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) par lam _ (dataS hh0 j hj)
        P.coeff_meas
        (fun t ht v u d γ hγ α => (P.coeff_smooth v u d γ hγ α t ht).mono hqs hqf)
        A u v ξ j X z
      exact l.continuous.measurable.comp hm
  · intro A u v ξ t ht X
    exact setting_liftA_normalized_test_periodic_of_coefficients P Cc hper hh n p q hqs hqf
      _ dataS A u v ξ t ht X
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The frozen metric supplies the diffusion bounds in the literal response mean identity. -/

theorem profileCellResponse_metric_mean_zero
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (par : Fin 2) (f : ℝ → ℝ → ℂ) (a t C : ℝ) (hat : a ≤ t) (hC : 0 ≤ C)
    (hf : ∀ s ∈ Icc a t, Continuous (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hb : ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C)
    (hcenter : ∀ s ∈ Icc a t, unitProfileFourierCoeff (f s) 0 = 0) :
    cellMean (fun z => profileCellResponse (fun r => G r par.rev par.rev) f a t (z par.rev)) = 0 := by
  let g := fun r => G r par.rev par.rev
  have hgm : AEStronglyMeasurable g volume :=
    ((cellMetric_entry_measurable hG par.rev par.rev).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
  have hi : IntegrableOn g (Icc a t) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs] using cellMetric_entry_bound hG r 0 par.rev par.rev
  exact profileCellResponse_cellMean_zero g f a t (1 / 2) C hat (by norm_num) hi
    (fun r _ => by simpa [basisVec_apply, g] using (hG.2.2.2 r 0 (basisVec par.rev)).1)
    hC hf hp hb hcenter par.rev

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Window-only transverse source reserves imply the actual inverse time equation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_time_integral (p q sZ : ℕ) (hq : 2 ≤ q) (hsZ : 2 ≤ sZ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → Vec 2 → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hfb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s => -cellOperator (G s X) (v s) (c s X) z + f s X z) volume a t ∧
      c t X z = ∫ s in a..t, -cellOperator (G s X) (v s) (c s X) z + f s X z := by
  let F : ℝ → ℝ → E := fun s x => f (Set.projIcc a b hab s) X (x • basisVec par.rev)
  have hc' := cellFieldInverse_clamped_transverse_source (fun s => G s X) v sZ a b hab
    par f hft X 0 (fun s z => c s X z) (hc X)
  have horder : (2 : ℕ∞) ≤ (q : ℕ∞) := by exact_mod_cast hq
  have hjet (l : E →L[ℝ] ℝ) (j : ℕ) (hj : j ≤ 2) (s x : ℝ) :
      ‖iteratedDeriv j (fun y => ((l (F s y) : ℝ) : ℂ)) x‖ ≤ S j * ‖l‖ := by
    have hh := clamped_linear_profile_mixed_bound p q 0 j 0 (Nat.zero_le p) (hj.trans hq)
      a b hab par.rev f hf (S j) 1
      (fun r hr Y w => by simpa using hfb j (hj.trans hq) r hr Y w) l s x X
    simpa using hh
  obtain ⟨hi, heq⟩ := cellFieldInverse_time_integral (fun s => G s X) (hG X) v W hv hvb
    par htrans F (fun s z => c s X z) sZ hsZ a b hab hc'
    (fun l => clamped_linear_profile_joint_measurable p q a b hab par.rev f hf hfm l X)
    (fun l j => S j * ‖l‖) (fun l j hj => mul_nonneg (hS j (hj.trans hq)) (norm_nonneg l))
    (fun l s _ => (clamped_linear_profile_fast_reserve p q a b hab par.rev f hf l s X).of_le
      (WithTop.coe_le_coe.mpr horder))
    (fun l s _ x => by
      exact congrArg (fun w => ((l w : ℝ) : ℂ))
        (cell_periodic_linear_profile par.rev _ (hper _ (Set.projIcc a b hab s).2 X) x))
    (fun l j hj s _ x _ => hjet l j hj s x) t ht z
  have he (s : ℝ) (hs : s ∈ uIcc a t) : F s (z par.rev) = f s X z := by
    rw [uIcc_of_le ht.1] at hs
    have hsb : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    dsimp only [F]
    rw [Set.projIcc_of_mem hab hsb]
    exact (transverse_profile_representation par (Icc a b) f hft s hsb X z).symm
  refine ⟨hi.congr (fun s hs => by rw [he s (uIoc_subset_uIcc hs)]), ?_⟩
  rw [heq]
  exact intervalIntegral.integral_congr (fun s hs => by rw [he s hs])

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The actual first diagonal lift on a linear test equals its literal transverse response. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftApply_first_linear_dual_profile_eq (sX sZ : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (T : Vec 2 →L[ℝ] (∀ i, h i)) (l : (∀ i, h i) →L[ℝ] ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    ((l (liftApply 1 (Cc 0 1) (fun _ Y => T Y) t X z) : ℝ) : ℂ) =
      profileCellResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (clampedFirstSourceProfile Q.η V a b P.window (l (T (basisVec par)))) a t (z par.rev) := by
  let U := T (basisVec par)
  let F := fun r x => -(Real.sqrt Q.η * V (Set.projIcc a b P.window r) x) • U
  let c := fun r z => liftApply 1 (Cc 0 1) (fun _ Y => T Y) r X z
  let G := fun r => Matrix.of (Q.G r X)
  have hc : IsCellFieldInverse G Q.v sZ a b 0 (fun r z => F r (z par.rev)) c := by
    apply cellFieldInverse_source_congr_on G Q.v sZ a b 0
      (fun r z => liftCellSource Q Cc (fun _ Y => T Y) 0 1 r X z) _ c _
      (hseq.2.2.2.2.2.2 0 (Nat.zero_le H) 1 le_rfl P.N_ge T T.contDiff X)
    intro r hr
    funext y
    rw [liftCellSource_first_diagonal_profile P sX sZ Cc hseq T T.contDiff r hr X y]
    rw [T.fderiv]
    simp only [F, U, Set.projIcc_of_mem P.window hr]
  have hc' := cellFieldInverse_local_coefficients G Q.v sZ a b P.window 0 _ c hc
  obtain ⟨W, hW⟩ := setting_drift_bound P
  obtain ⟨C, hC, hb⟩ := setting_first_clamped_profile_jets P (l U)
  have hjet : ∀ j ≤ qf, ∀ r ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (F r y) : ℝ) : ℂ)) x‖ ≤ C j := by
    intro j hj r _ x _
    simpa only [F, map_smul, smul_eq_mul, clampedFirstSourceProfile] using! hb j hj r x
  have he := cellFieldInverse_dual_eq_profileResponse
    (fun r => G (Set.projIcc a b P.window r)) (setting_cell_metric P X)
    (localCellDrift a b P.window Q.v) W
    (localCellDrift_measurable a b P.window Q.v (setting_drift_continuous P) P.v_meas)
    (fun r y => hW _ (Set.projIcc a b P.window r).2 y) par
    (fun r y => setting_transverse_drift_zero P _ y) F c sZ a b P.window hc' l
    (by simpa only [F, map_smul, smul_eq_mul, clampedFirstSourceProfile] using!
      setting_first_clamped_profile_measurable P (l U))
    qf (by rw [P.qf_eq]; omega) C hC
    (fun r _ => by simpa only [F, map_smul, smul_eq_mul, clampedFirstSourceProfile] using!
      setting_first_clamped_profile_contDiff P (l U) r)
    (fun r _ => by simpa only [F, map_smul, smul_eq_mul, clampedFirstSourceProfile] using!
      setting_first_clamped_profile_periodic P (l U) r)
    hjet t ht
  simpa only [G, c, F, U, Matrix.of_apply, map_smul, smul_eq_mul,
    clampedFirstSourceProfile] using! congrFun he z
end

/-! The first actual lift is a single scalar response times its tested coarse derivative. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem liftApply_first_linear_scalar (sX sZ : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (T : Vec 2 →L[ℝ] (∀ i, h i)) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply 1 (Cc 0 1) (fun _ Y => T Y) t X z =
      (profileCellResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (clampedFirstSourceProfile Q.η V a b P.window 1) a t (z par.rev)).re • T (basisVec par) := by
  apply eq_of_all_real_duals
  intro l
  have he : clampedFirstSourceProfile Q.η V a b P.window (l (T (basisVec par))) =
      fun r y => l (T (basisVec par)) • clampedFirstSourceProfile Q.η V a b P.window 1 r y := by
    funext r y
    simp only [clampedFirstSourceProfile, mul_one, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hh := liftApply_first_linear_dual_profile_eq P sX sZ Cc hseq T l t ht X z
  rw [he, profileCellResponse_real_smul] at hh
  have hr := congrArg Complex.re hh
  simp only [map_smul, smul_eq_mul]
  simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_comm] using! hr
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ComplexConjugate
namespace AVRegularity.CycleComparison.Lift

/-! The real Fourier response satisfies every clause of the actual finite-past field inverse. -/

theorem profileResponse_real_field_inverse
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hfm : Measurable (Function.uncurry f))
    (q : ℕ) (hq : 2 ≤ q) (C : ℕ → ℝ) (hC : ∀ j ≤ q, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ q (f t))
    (hp : ∀ t, Function.Periodic (f t) 1)
    (hj : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f t) x‖ ≤ C j)
    (hreal : ∀ t x, ((f t x).re : ℂ) = f t x)
    (hcenter : ∀ t ∈ Icc a b, unitProfileFourierCoeff (f t) 0 = 0) :
    IsCellFieldInverse G v q a b 0 (fun t z => (f t (z par.rev)).re)
      (fun t z => (profileCellResponse (fun r => G r par.rev par.rev) f a t (z par.rev)).re) := by
  let g := fun r => G r par.rev par.rev
  let c : ℝ → Vec 2 → ℝ := fun t z => (profileCellResponse g f a t (z par.rev)).re
  let D : ℝ → RawJet2 1 ℂ := fun t => classicalCellJet (fun z => profileCellResponse g f a t (z par.rev))
  have hconj t x : conj (f t x) = f t x := by rw [← hreal t x]; simp
  have hr t x := profileCellResponse_ofReal_re g f hp hconj a t x
  have hcd t (hti : t ∈ Icc a b) :=
    profileCellResponse_metric_contDiff G hG par f a b q C hC hf (fun r _ => hp r) hj t hti
  have hcr t (hti : t ∈ Icc a b) : ContDiff ℝ q (c t) :=
    Complex.reCLM.contDiff.comp ((hcd t hti).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) par.rev).contDiff))
  have hD : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
      (fun t z => f t (z par.rev)) 0 D :=
    profileResponse_classical_solution G hG v V hv hb par ht f a b hab hfm q hq C hC hf
      (fun t _ => hp t) hj
  refine ⟨hcr, ?_⟩
  intro l
  have hsol := real_dual_scalar_solution (Icc a b) measurableSet_Icc
    ⟨fun t _ => G t, v, 0, 0⟩ (fun t z => f t (z par.rev))
    (fun t z => profileCellResponse g f a t (z par.rev))
    (fun t z => hreal t (z par.rev)) (fun t z => hr t (z par.rev))
    (fun t hti => (hcr t hti).differentiable (by exact_mod_cast (show q ≠ 0 by omega))) hD l
  refine ⟨hsol, ?_, ?_, cellSolution_compact_energy_finite a b hab _ _ _ _ hsol⟩
  · intro t hti
    change cellMean (fun z => ((l (c t z) : ℝ) : ℂ)) = 0
    apply real_dual_scalar_mean_zero _ (fun z => hr t (z par.rev)) _ l
    exact profileCellResponse_metric_mean_zero G hG par f a t (C 0) hti.1
      (hC 0 (by omega)) (fun r hr => (hf r ⟨hr.1, hr.2.trans hti.2⟩).continuous)
      (fun r _ => hp r)
      (fun r hr x hx => by simpa only [iteratedDeriv_zero] using hj 0 (by omega) r ⟨hr.1, hr.2.trans hti.2⟩ x hx)
      (fun r hr => hcenter r ⟨hr.1, hr.2.trans hti.2⟩)
  · apply Filter.Eventually.of_forall
    intro z
    change ((l (c a z) : ℝ) : ℂ) = ((l (0 : ℝ) : ℝ) : ℂ)
    simp only [c, profileCellResponse_same, Pi.zero_apply, Complex.zero_re, map_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual zero-start cell inverses inherit the ambient rectangular source reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_ambient_box_reserve (p q sZ : ℕ) (hq : 2 ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → ℝ → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M lam κ : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X,
      Measurable (fun x : ℝ × ℝ => ((l (f x.1 X x.2) : ℝ) : ℂ)))
    (hff : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      ContDiff ℝ (q : ℕ∞) (fun z => ((l (f t X z) : ℝ) : ℂ)))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t z,
      ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) z))
    (S : (E →L[ℝ] ℝ) → ℕ → ℕ → ℝ)
    (hS : ∀ l r, r ≤ p → ∀ j ≤ q, 0 ≤ S l r j)
    (hfb : ∀ l r, r ≤ p → ∀ j ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ r
        (fun Y => iteratedDeriv j (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤ S l r j * lam ^ r)
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      unitProfileFourierCoeff (fun z => ((l (f t X z) : ℝ) : ℂ)) 0 = 0)
    (t : ℝ) (ht : t ∈ Icc a b) : IsBoxSmooth p q (c t) := by
  apply isBoxSmooth_of_all_real_duals
  intro l
  let F := fun r X z => ((l (f r X z) : ℝ) : ℂ)
  have hp := profileCellResponse_slow_dependent_isBoxSmooth p q
    (fun r X => G r X par.rev par.rev) hm hs M lam κ a t hM hlam hκ ht.1 hb hgl
    F (hfm l) (hff l) (fun r X z => congrArg (fun y => ((l y : ℝ) : ℂ)) (hper r X z))
    (hfs l) (S l) (hS l) (hfb l) (hcenter l)
    (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ)
  have he : (fun X z => ((l (c t X z) : ℝ) : ℂ)) =
      fun X z => profileCellResponse (fun r => G r X par.rev par.rev) (fun r => F r X) a t (z par.rev) := by
    funext X z
    have hj : ∀ j ≤ q, ∀ r ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv j (F r X) y‖ ≤ S l 0 j := by
      intro j hj r _ y _
      simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using! hfb l 0 (Nat.zero_le p) j hj r y X
    exact congrFun (cellFieldInverse_dual_eq_profileResponse (fun r => G r X) (hG X) v W hv hvb
      par htrans (fun r => f r X) (fun r => c r X) sZ a b hab (hc X) l (hfm l X)
      q hq (S l 0) (hS l 0 (Nat.zero_le p)) (fun r _ => hff l r X)
      (fun r _ z => congrArg (fun y => ((l y : ℝ) : ℂ)) (hper r X z)) hj t ht) z
  have hh : IsBoxSmooth p q (fun X z => ((l (c t X z) : ℝ) : ℂ)) := by
    rw [he]
    exact hp
  simpa only [Complex.ofReal_re] using! hh.clm_comp Complex.reCLM

end AVRegularity.CycleComparison.Lift
end
