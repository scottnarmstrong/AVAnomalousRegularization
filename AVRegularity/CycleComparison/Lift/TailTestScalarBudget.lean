-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.SettingAmbientFirstCrossPairedGrading
public import AVRegularity.CycleComparison.Lift.LiftSequenceUniqueness
import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
import AVRegularity.CycleComparison.Lift.PhysicalPowerSchurWiener
import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The cell mean of a truncated graded composition contains only its degree-zero lift. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem tail_composition_mean (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh n : ℕ) (hhh : hh ≤ H) (hn : 2 ≤ n)
    (g : ℕ → ℕ → ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => ∑ r ∈ Finset.range (N + 1),
      if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, liftApply r (Cc p.1 r) (g p.2 (n - r)) t X z
      else 0) = if n ≤ N + D then g hh n t X else 0 := by
  classical
  let T := fun r z => if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, liftApply r (Cc p.1 r) (g p.2 (n - r)) t X z else 0
  have hc (r : ℕ) : Continuous (T r) :=
    tail_composition_term_fast_continuous Q sX sZ a b N H Cc hseq hh n r hhh g t ht X
  have hm (r : ℕ) (hr : r ≤ N) : fieldCellMean (T r) =
      if r = 0 ∧ n ≤ N + D then g hh n t X else 0 := by
    by_cases hv : r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D
    · by_cases hr0 : r = 0
      · subst r
        have hg : T 0 = fun _ => g hh n t X := by
          funext z
          dsimp only [T]
          rw [ite_eq_left hv]
          exact liftSequence_zero_degree_graded_action Q sX sZ a b N H Cc hseq
            hh hhh (fun q => g q n) t ht X z
        rw [hg, fieldCellMean_const, ite_eq_left (show 0 = 0 ∧ n ≤ N + D by simpa using hv.2.2)]
      · have hz := liftSequence_graded_apply_mean_zero Q sX sZ a b N H Cc hseq
          hh r hhh (by omega) hr (fun q => g q (n - r)) t ht X
        simpa only [T, ite_eq_left hv, ite_eq_right (show ¬(r = 0 ∧ n ≤ N + D) by simp [hr0])] using hz
    · have hnoth : ¬(r = 0 ∧ n ≤ N + D) := by
        rintro ⟨rfl, hnR⟩
        exact hv (by simpa using (show 2 ≤ n ∧ n ≤ N + D from ⟨hn, hnR⟩))
      simp only [T, ite_eq_right hv, fieldCellMean_zero, ite_eq_right hnoth]
  change fieldCellMean (fun z => ∑ r ∈ Finset.range (N + 1), T r z) = _
  rw [fieldCellMean_sum _ (fun r _ => hc r)]
  have he : (∑ r ∈ Finset.range (N + 1), fieldCellMean (T r)) = fieldCellMean (T 0) := by
    apply Finset.sum_eq_single 0
    · intro r hr hr0
      rw [hm r (by have := Finset.mem_range.mp hr; omega)]
      exact ite_eq_right (fun h => hr0 h.1)
    · simp
  rw [he, hm 0 (Nat.zero_le N)]
  simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Earlier paired coefficient states close the actual height-zero uncentered difference step. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_uncentered_paired_grading_of_predecessors
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h) (P₀ n : ℕ)
    (hreserve : P₀ + (N + D) ≤ qs) (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (B₀ Bi Bd : ℕ → ℝ) (hBd : ∀ m, 0 ≤ Bd m)
    (prior : ∀ m < n,
      AmbientLiftCoefficientData par a b P.window lam m
        (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m)
        (Cc 0 m) (fun v u => B₀ m * (if v = u then 1 else 0)))
    (priori : ∀ m < n,
      AmbientLiftCoefficientData par a b P.window lam m
        (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m)
        (Ci 0 m) (fun v u => Bi m * (if v = u then 1 else 0)))
    (priord : ∀ m < n,
      AmbientLiftCoefficientData par a b P.window lam m
        (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m)
        (fun d α t X z v u => Cc 0 m d α t X z v u - Ci 0 m d α t X z v u)
        (fun v u => (Bd m * (if v = u then 1 else 0)) * g))
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    let p := ambientDegreeSlowReserve P₀ (N + D) n
    let q := ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n
    IsBoxSmooth p q (fun X z =>
      normalizedLiftUncenteredField Q Cc 0 n (lam • A) u v ξ t X z -
      normalizedLiftUncenteredField
        (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
        Ci 0 n (lam • A) u v ξ t X z) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 n (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci 0 n (lam • A) u v ξ t Y y) z) X‖ ≤
        (pairedUncenteredScalarBudget n p q A CG Cw CGI Bi Bd *
          (if v = u then 1 else 0) * ‖ξ‖) * g * lam ^ (n + r) := by
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n
  have hp : p + 1 ≤ qs :=
    (ambientDegreeSlowReserve_coefficient P₀ (N + D) n hn hnR).trans hreserve
  have hq : q ≤ qf := by
    have hc := ambientDegreeFastReserve_data (max k (L + 2)) D 0 (N + D) 0 n hn hnR
    rw [P.qf_eq]
    dsimp only [q] at ⊢
    omega
  have hslow j (hj : j ≤ n) : p + j = ambientDegreeSlowReserve P₀ (N + D) (n - j) :=
    ambientDegreeSlowReserve_source P₀ (N + D) n j hnR hj
  have hfast₁ : q + 1 ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 (n - 1) := by
    have he := ambientDegreeFastReserve_cross (max k (L + 2)) D 0 (N + D) 0 n 1 hnR hn
    dsimp only [q] at ⊢
    omega
  have data₁ := (prior (n - 1) (by omega)).mono (le_of_eq (hslow 1 hn)) hfast₁
  have datai₁ := (priori (n - 1) (by omega)).mono (le_of_eq (hslow 1 hn)) hfast₁
  have datad₁ := (priord (n - 1) (by omega)).mono (le_of_eq (hslow 1 hn)) hfast₁
  have data₂ (hn₂ : 2 ≤ n) := (prior (n - 2) (by omega)).mono
    (le_of_eq (hslow 2 hn₂)) (ambientDegreeFastReserve_mono
      (max k (L + 2)) D 0 (N + D) 0 0 n (n - 2) le_rfl (Nat.sub_le _ _))
  have datai₂ (hn₂ : 2 ≤ n) := (priori (n - 2) (by omega)).mono
    (le_of_eq (hslow 2 hn₂)) (ambientDegreeFastReserve_mono
      (max k (L + 2)) D 0 (N + D) 0 0 n (n - 2) le_rfl (Nat.sub_le _ _))
  have datad₂ (hn₂ : 2 ≤ n) := (priord (n - 2) (by omega)).mono
    (le_of_eq (hslow 2 hn₂)) (ambientDegreeFastReserve_mono
      (max k (L + 2)) D 0 (N + D) 0 0 n (n - 2) le_rfl (Nat.sub_le _ _))
  let K₁ := pairedFirstCrossScalarBudget (n - 1) p q A CG Cw CGI Bi Bd *
    (if v = u then 1 else 0) * ‖ξ‖ * g
  let K₂ := pairedSecondCrossScalarBudget (n - 2) p q A CG CGI Bi Bd *
    (if v = u then 1 else 0) * ‖ξ‖ * g
  have h₁ := setting_ambient_first_cross_paired_lift_box P (n - 1) p q (p + 1) (q + 1)
    hp hq le_rfl le_rfl _ _ _ _ data₁ datai₁ A t ht v u ξ
  have hb₁ r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_ambient_first_cross_paired_lift_bound P (n - 1) p q (p + 1) (q + 1)
      hp hq le_rfl le_rfl g hg CGI hGI _ _ _ _
      (fun v u => Bd (n - 1) * (if v = u then 1 else 0))
      (fun v u => mul_nonneg (hBd _) (by split_ifs <;> norm_num))
      data₁ datai₁ datad₁ A t ht v u ξ r s hr hs X z
  have h₂ (hn₂ : 2 ≤ n) := setting_ambient_second_cross_paired_lift_box P (n - 2) p q (p + 2) q
    hp le_rfl le_rfl _ _ _ _ (data₂ hn₂) (datai₂ hn₂) A t ht v u ξ
  have hb₂ (hn₂ : 2 ≤ n) r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_ambient_second_cross_paired_lift_bound P (n - 2) p q (p + 2) q
      hp le_rfl le_rfl g hg CGI hGI _ _ _ _
      (fun v u => Bd (n - 2) * (if v = u then 1 else 0))
      (fun v u => mul_nonneg (hBd _) (by split_ifs <;> norm_num))
      (data₂ hn₂) (datai₂ hn₂) (datad₂ hn₂) A t ht v u ξ r s hr hs X z
  have result := liftA_zero_height_paired_grading_of_cross_terms Q
    (fun _ _ i j => if i = j then 1 else 0) Cc Ci
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) n p q t v A lam K₁ K₂ h₁
    (fun r hr s hs X z => (hb₁ r hr s hs X z).trans_eq (by
      rw [show n - 1 + 1 = n by omega]
      dsimp only [K₁, pairedFirstCrossScalarBudget]
      ring)) h₂
    (fun hn₂ r hr s hs X z => (hb₂ hn₂ r hr s hs X z).trans_eq (by
      rw [show n - 2 + 2 = n by omega]
      dsimp only [K₂, pairedSecondCrossScalarBudget]
      ring))
  refine ⟨result.1, ?_⟩
  intro r hr s hs X z
  exact (result.2 r hr s hs X z).trans_eq (by
    dsimp only [K₁, K₂, pairedUncenteredScalarBudget]
    split_ifs <;> ring)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Real-dual representatives of the cell field inverse agree pointwise with the explicit Fourier response. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_dual_eq_profileResponse
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (c : ℝ → Vec 2 → E) (sZ : ℕ) (a b : ℝ) (hab : a ≤ b)
    (hc : IsCellFieldInverse G v sZ a b 0 (fun t z => f t (z par.rev)) c)
    (l : E →L[ℝ] ℝ)
    (hfm : Measurable (fun p : ℝ × ℝ => ((l (f p.1 p.2) : ℝ) : ℂ)))
    (q : ℕ) (hq : 2 ≤ q) (C : ℕ → ℝ) (hC : ∀ j ≤ q, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C j) :
    ∀ t ∈ Icc a b, (fun z => ((l (c t z) : ℝ) : ℂ)) =
      fun z => profileCellResponse (fun r => G r par.rev par.rev)
        (fun t x => ((l (f t x) : ℝ) : ℂ)) a t (z par.rev) := by
  let F := fun t x => ((l (f t x) : ℝ) : ℂ)
  have hsol : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
      (fun t z => F t (z par.rev)) 0 (cellJetOfField l c) := (hc.2 l).1
  have ha : cellValue (cellJetOfField l c) a =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    simpa only [Pi.zero_apply, map_zero, Complex.ofReal_zero] using! (hc.2 l).2.2.1
  have hcont (t : ℝ) (hti : t ∈ Icc a b) : Continuous (cellValue (cellJetOfField l c) t) := by
    change Continuous (fun z => ((l (c t z) : ℝ) : ℂ))
    exact Complex.ofRealCLM.continuous.comp (l.continuous.comp (hc.1 t hti).continuous)
  exact cellSolution_eq_profileResponse G hG v V hv hb par ht F a b hab hfm
    q hq C hC hf hp hj (cellJetOfField l c) hsol ha hcont

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual ordered mean correction inherits the sum of its two source heights. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_mean_power_grading (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (j δ p q h₁ h₂ : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (F : ι → ι → ℝ) (hF : ∀ v u, 0 ≤ F v u) (B : ℝ) (hB : 0 ≤ B)
    (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (coef : AmbientLiftCoefficientData par a b hab lam j p q (Cc h₁ j)
      (fun v u => B * finiteMatrixPower F h₁ v u))
    (mean : AmbientLiftUncenteredData par a b hab lam h₂ δ (p + j) q Q Cc K
      (finiteMatrixPower F h₂))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftApply j (Cc h₁ j) (liftMean Q Cc
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) h₂ δ) t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftApply j (Cc h₁ j)
          (liftMean Q Cc (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) h₂ δ) t Y y v) z) X‖ ≤
        (exponentialLiftCompositionNormalizedConstant j p q A * B *
          ((2 : ℝ) ^ (p + j) * K A) * finiteMatrixPower F (h₁ + h₂) v u * ‖ξ‖) *
            lam ^ (j + δ + r) := by
  let f := fun (_ : ℝ) Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  let g := fun X => (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f h₂ δ t X
  have hg : ContDiff ℝ ((p + j : ℕ) : ℕ∞) g :=
    mean.mean_normalized_contDiff hlam A u ξ t ht
  have he : liftApply j (Cc h₁ j) (fun _ X => Real.exp ((lam • A) X) • g X) t =
      liftApply j (Cc h₁ j) (liftMean Q Cc f h₂ δ) t := by
    apply liftApply_input_congr_at_time
    funext X
    simp only [g, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hraw := liftApply_component_box_reserve j p q (Cc h₁ j) (liftMean Q Cc f h₂ δ) t v
    (mean.mean_raw_contDiff hlam A u ξ t ht)
    (fun m hm α w => coef.box m hm α v w t ht)
  refine ⟨exponential_normalization_box_reserve p q (lam • A) _ hraw, ?_⟩
  intro r hr s hs X z
  have hC : 0 ≤ (2 : ℝ) ^ (p + j) * K A := mul_nonneg (by positivity) (mean.constant_nonneg A)
  have hb := liftApply_exponential_input_power_bound j r s δ h₁ h₂ (Cc h₁ j) g t X v u
    (hg.of_le (by exact_mod_cast Nat.add_le_add_right hr j))
    (fun m hm α w => (coef.box m hm α v w t ht).mono hr hs)
    lam hlam A F hF B ((2 : ℝ) ^ (p + j) * K A) hB hC ξ
    (fun m hm α w d hd e he y => coef.bound m hm α v w d (hd.trans hr)
      e (he.trans hs) t ht X y)
    (fun w d hd => by
      have hm := (mean.mean_component_grading hlam A u w ξ t ht d (by omega)).2 X
      simpa only [g, Pi.smul_apply, f, mul_assoc] using hm) z
  rw [he] at hb
  apply hb.trans
  have hpw := finiteMatrixPower_nonneg F hF (h₁ + h₂) v u
  gcongr
  exact exponentialLiftCompositionNormalizedConstant_mono j r s p q hr hs A

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Calibration of the inverse source gives the scalar coefficient recurrence. -/

def ambientCoefficientScalarStep (P Q D H R N hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ) : ℝ :=
  if n = 0 then (if hh = 0 then 1 else 0)
  else if N < n then 0
  else finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N
    (fun A => ambientInverseUniformConstant (ambientDegreeSlowReserve P R n)
      (metricParameterBudget (ambientDegreeSlowReserve P R n) CG) (3 / 4) *
        ambientCenteredBudget P Q D H R hh n CG Cw Cj B A)

theorem ambientCoefficientScalarStep_nonneg (P Q D H R N hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ) :
    0 ≤ ambientCoefficientScalarStep P Q D H R N hh n CG Cw Cj B := by
  unfold ambientCoefficientScalarStep
  split_ifs <;> first
  | exact le_refl 0
  | exact zero_le_one
  | exact mul_nonneg (finiteLiftCalibrationBudget_nonneg N)
      (finiteLiftTestDirectionBudget_nonneg N _)

theorem ambientCoefficientScalarStep_congr_earlier (P Q D H R N hh n : ℕ)
    (hn : n ≤ R) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (B C : ℕ → ℕ → ℝ)
    (heq : ∀ h m, ambientRecurrenceRank R h m < ambientRecurrenceRank R hh n →
      B h m = C h m) :
    ambientCoefficientScalarStep P Q D H R N hh n CG Cw Cj B =
      ambientCoefficientScalarStep P Q D H R N hh n CG Cw Cj C := by
  unfold ambientCoefficientScalarStep
  split_ifs <;> try rfl
  congr 1
  congr 1
  funext A
  rw [ambientCenteredBudget_congr_earlier P Q D H R hh n hn CG Cw Cj B C heq A]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Native coefficient and actual mean states give the literal tail's scalar matrix-power bound. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_tail_power_grading (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (N hh n p q : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (F : ι → ι → ℝ) (hF : ∀ v u, 0 ≤ F v u) (B : ℕ → ℕ → ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ)
    (uncentered : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K (finiteMatrixPower F hh))
    (coef : ∀ j ∈ Finset.range (N + 1),
      j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D →
      ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
        AmbientLiftCoefficientData par a b hab lam j p q (Cc ab.1 j)
          (fun v u => B ab.1 j * finiteMatrixPower F ab.1 v u))
    (mean : ∀ j ∈ Finset.range (N + 1),
      j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D →
      ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
        AmbientLiftUncenteredData par a b hab lam ab.2 (n - j) (p + j) q Q Cc
          (KM ab.2 (n - j)) (finiteMatrixPower F ab.2))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftTailCoeff Q Cc N
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftTailCoeff Q Cc N
          (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y y v) z) X‖ ≤
        (orderedTailScalarConstant N D hh n p q B K KM A * finiteMatrixPower F hh v u * ‖ξ‖) *
          lam ^ (n + r) := by
  have hcorr j (hj : j ∈ Finset.range (N + 1))
      (hg : j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D) ab
      (hab' : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :=
    ambient_ordered_mean_power_grading par a b hab lam hlam j (n - j) p q ab.1 ab.2 Q Cc F hF
      (B ab.1 j) (hB ab.1 j) (KM ab.2 (n - j)) (coef j hj hg ab hab') (mean j hj hg ab hab')
      A u v ξ t ht
  let BC := fun j (ab : ℕ × ℕ) =>
    exponentialLiftCompositionNormalizedConstant j p q A * B ab.1 j *
      ((2 : ℝ) ^ (p + j) * KM ab.2 (n - j) A) * finiteMatrixPower F hh v u * ‖ξ‖
  have hs := liftTail_normalized_mixed_grading_of_terms Q Cc
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) N hh n p q t v A lam
    (K A * finiteMatrixPower F hh v u * ‖ξ‖)
    (uncentered.box A u v ξ t ht)
    (fun r hr s hs X z => uncentered.bound A u v ξ r hr s hs t ht X z) BC
    (fun j hj hg ab hab' => (hcorr j hj hg ab hab').1)
    (fun j hj hg ab hab' r hr s hs X z => by
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
      have hn : j + (n - j) = n := by omega
      simpa only [BC, he, hn] using (hcorr j hj hg ab hab').2 r hr s hs X z)
  refine ⟨hs.1, ?_⟩
  intro r hr s hsq X z
  apply (hs.2 r hr s hsq X z).trans_eq
  congr 1
  simp only [orderedTailScalarConstant, BC, add_mul, Finset.sum_mul, ite_mul, zero_mul]
end

/-! Actual earlier coefficient and mean states close the centered source's scalar-power bound. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_centered_power_grading (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (hh n p q : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (F : ι → ι → ℝ) (hF : ∀ v u, 0 ≤ F v u) (B : ℕ → ℕ → ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ)
    (uncentered : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K (finiteMatrixPower F hh))
    (coef : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      AmbientLiftCoefficientData par a b hab lam j p q (Cc ab.1 j)
        (fun v u => B ab.1 j * finiteMatrixPower F ab.1 v u))
    (mean : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      AmbientLiftUncenteredData par a b hab lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower F ab.2))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
        (orderedCenteredScalarConstant hh n p q B K KM A * finiteMatrixPower F hh v u * ‖ξ‖) *
          lam ^ (n + r) := by
  have hcorr j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab' : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :=
    ambient_ordered_mean_power_grading par a b hab lam hlam j (n - j) p q ab.1 ab.2 Q Cc F hF
      (B ab.1 j) (hB ab.1 j) (KM ab.2 (n - j)) (coef j hj ab hab') (mean j hj ab hab')
      A u v ξ t ht
  let BC := fun j (ab : ℕ × ℕ) =>
    exponentialLiftCompositionNormalizedConstant j p q A * B ab.1 j *
      ((2 : ℝ) ^ (p + j) * KM ab.2 (n - j) A) * finiteMatrixPower F hh v u * ‖ξ‖
  have hs := liftCellSource_normalized_mixed_grading_of_terms Q Cc
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n p q t v A lam
    (K A * finiteMatrixPower F hh v u * ‖ξ‖) hlam
    (mul_nonneg (mul_nonneg (uncentered.constant_nonneg A)
      (finiteMatrixPower_nonneg F hF hh v u)) (norm_nonneg ξ))
    (fun w => uncentered.box A u w ξ t ht)
    (fun r hr s hs X z => uncentered.bound A u v ξ r hr s hs t ht X z) BC
    (fun j hj ab hab' => (hcorr j hj ab hab').1)
    (fun j hj ab hab' r hr s hs X z => by
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
      have hj' := Finset.mem_Icc.mp hj
      have hn : j + (n - j) = n := by omega
      simpa only [BC, he, hn] using (hcorr j hj ab hab').2 r hr s hs X z)
  refine ⟨hs.1, ?_⟩
  intro r hr s hsq X z
  apply (hs.2 r hr s hsq X z).trans_eq
  congr 1
  unfold orderedCenteredScalarConstant BC
  simp only [add_mul, Finset.sum_mul]
  congr 1
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The scalar majorant is fixed by strong recursion before the component family is chosen. -/

def ambientCoefficientScalarRankBudget (P Q D H R N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℕ → ℝ :=
  Nat.strongRec fun r previous =>
    ambientCoefficientScalarStep P Q D H R N (r / (R + 1)) (r % (R + 1)) CG Cw Cj
      (fun hh n => if hl : ambientRecurrenceRank R hh n < r then
        previous (ambientRecurrenceRank R hh n) hl else 0)

def ambientCoefficientScalarBudget (P Q D H R N hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ambientCoefficientScalarRankBudget P Q D H R N CG Cw Cj (ambientRecurrenceRank R hh n)

theorem ambientCoefficientScalarRankBudget_nonneg (P Q D H R N r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientCoefficientScalarRankBudget P Q D H R N CG Cw Cj r := by
  unfold ambientCoefficientScalarRankBudget
  rw [Nat.strongRec_eq]
  exact ambientCoefficientScalarStep_nonneg _ _ _ _ _ _ _ _ _ _ _ _

theorem ambientCoefficientScalarBudget_nonneg (P Q D H R N hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientCoefficientScalarBudget P Q D H R N hh n CG Cw Cj :=
  ambientCoefficientScalarRankBudget_nonneg _ _ _ _ _ _ _ _ _ _

theorem ambientCoefficientScalarBudget_eq_step (P Q D H R N hh n : ℕ) (hn : n ≤ R)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ambientCoefficientScalarBudget P Q D H R N hh n CG Cw Cj =
      ambientCoefficientScalarStep P Q D H R N hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P Q D H R N h m CG Cw Cj) := by
  unfold ambientCoefficientScalarBudget
  conv_lhs => unfold ambientCoefficientScalarRankBudget
  rw [Nat.strongRec_eq, ambientRecurrenceRank_div R hh n hn,
    ambientRecurrenceRank_mod R hh n hn]
  apply ambientCoefficientScalarStep_congr_earlier P Q D H R N hh n hn CG Cw Cj
  intro h m hl
  simp only [dite_eq_left hl]
  rfl

/-! The scalar recursion has the exact initial, cutoff, and inverse-calibration equations. -/

theorem ambientCoefficientScalarBudget_zero (P Q D H R N hh : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ambientCoefficientScalarBudget P Q D H R N hh 0 CG Cw Cj =
      if hh = 0 then 1 else 0 := by
  rw [ambientCoefficientScalarBudget_eq_step _ _ _ _ _ _ _ _ (Nat.zero_le R)]
  simp [ambientCoefficientScalarStep]

theorem ambientCoefficientScalarBudget_cutoff (P Q D H R N hh n : ℕ)
    (hn : n ≤ R) (hN : N < n) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ambientCoefficientScalarBudget P Q D H R N hh n CG Cw Cj = 0 := by
  rw [ambientCoefficientScalarBudget_eq_step _ _ _ _ _ _ _ _ hn]
  simp only [ambientCoefficientScalarStep, ite_eq_right (by omega : n ≠ 0), ite_eq_left hN]

theorem ambientCoefficientScalarBudget_positive (P Q D H R N hh n : ℕ)
    (hn : n ≤ R) (hnpos : 1 ≤ n) (hnN : n ≤ N)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ambientCoefficientScalarBudget P Q D H R N hh n CG Cw Cj =
      finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N
        (fun A => ambientInverseUniformConstant (ambientDegreeSlowReserve P R n)
          (metricParameterBudget (ambientDegreeSlowReserve P R n) CG) (3 / 4) *
            ambientCenteredBudget P Q D H R hh n CG Cw Cj
              (fun h m => ambientCoefficientScalarBudget P Q D H R N h m CG Cw Cj) A) := by
  rw [ambientCoefficientScalarBudget_eq_step _ _ _ _ _ _ _ _ hn]
  simp only [ambientCoefficientScalarStep, ite_eq_right (by omega : n ≠ 0),
    ite_eq_right (by omega : ¬N < n)]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The diagonal mean flux has a finite fixed-data drift and molecular budget. -/

def ambientDiagonalMeanFluxWordConstant (P N k L D H n r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  2 ^ r * max (Cw 0) 0 *
      ambientCoefficientScalarBudget P (max k (L + 2)) D H (N + D) N 0 (n - 1) CG Cw Cj +
    if n = 2 then max (CG r) 0 else 0

def ambientDiagonalMeanFluxConstant (P N k L D H n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ _p : DerivativeWord2 m × Fin 2,
    ambientDiagonalMeanFluxWordConstant P N k L D H n r CG Cw Cj

theorem ambientDiagonalMeanFluxWordConstant_nonneg (P N k L D H n r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientDiagonalMeanFluxWordConstant P N k L D H n r CG Cw Cj := by
  unfold ambientDiagonalMeanFluxWordConstant
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (by positivity) (le_max_right _ _))
      (ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)
  · split_ifs <;> positivity

theorem ambientDiagonalMeanFluxConstant_nonneg (P N k L D H n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientDiagonalMeanFluxConstant P N k L D H n m r CG Cw Cj :=
  Finset.sum_nonneg fun _ _ => ambientDiagonalMeanFluxWordConstant_nonneg P N k L D H n r CG Cw Cj

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered mean corrections retain their coefficient/mean difference order and one perturbation factor. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_mean_paired_grading (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam eps : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps) (j δ p q : ℕ)
    (Q Qi : LiftOperatorData ι h D) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (B₀ Bi Bd : ℝ) (hBi : 0 ≤ Bi) (hBd : 0 ≤ Bd)
    (K Ki Kd : (Vec 2 →L[ℝ] ℝ) → ℝ) (hKd : ∀ A, 0 ≤ Kd A)
    (coef : AmbientLiftCoefficientData par a b hab lam j p q (Cc 0 j)
      (fun v u => B₀ * (if v = u then 1 else 0)))
    (coefi : AmbientLiftCoefficientData par a b hab lam j p q (Ci 0 j)
      (fun v u => Bi * (if v = u then 1 else 0)))
    (coefd : AmbientLiftCoefficientData par a b hab lam j p q
      (fun m α t X z v u => Cc 0 j m α t X z v u - Ci 0 j m α t X z v u)
      (fun v u => (Bd * (if v = u then 1 else 0)) * eps))
    (mean : AmbientLiftUncenteredData par a b hab lam 0 δ (p + j) q Q Cc K
      (fun v u => if v = u then 1 else 0))
    (meani : AmbientLiftUncenteredData par a b hab lam 0 δ (p + j) q Qi Ci Ki
      (fun v u => if v = u then 1 else 0))
    (hmean : ∀ A u v ξ, ∀ r ≤ p + j, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 δ (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField Qi Ci 0 δ (lam • A) u v ξ t Y y) z) X‖ ≤
        (Kd A * (if v = u then 1 else 0) * ‖ξ‖) * eps * lam ^ (δ + r))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z =>
      (Real.exp ((lam • A) X))⁻¹ • liftApply j (Cc 0 j)
        (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) 0 δ) t X z v -
      (Real.exp ((lam • A) X))⁻¹ • liftApply j (Ci 0 j)
        (liftMean Qi Ci (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) 0 δ) t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • liftApply j (Cc 0 j)
          (liftMean Q Cc (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) 0 δ) t Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • liftApply j (Ci 0 j)
          (liftMean Qi Ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) 0 δ) t Y y v) z) X‖ ≤
        (exponentialLiftCompositionNormalizedConstant j p q A *
          (Bd * ((2 : ℝ) ^ (p + j) * K A) + Bi * ((2 : ℝ) ^ (p + j) * Kd A))) *
          eps * (if v = u then 1 else 0) * ‖ξ‖ * lam ^ (j + δ + r) := by
  let f := fun (_ : ℝ) Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  let g := fun X => (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f 0 δ t X
  let gi := fun X => (Real.exp ((lam • A) X))⁻¹ • liftMean Qi Ci f 0 δ t X
  have hg := mean.mean_normalized_contDiff hlam A u ξ t ht
  have hgi := meani.mean_normalized_contDiff hlam A u ξ t ht
  have he : liftApply j (Cc 0 j) (fun _ X => Real.exp ((lam • A) X) • g X) t =
      liftApply j (Cc 0 j) (liftMean Q Cc f 0 δ) t := by
    apply liftApply_input_congr_at_time
    funext X
    simp only [g, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hei : liftApply j (Ci 0 j) (fun _ X => Real.exp ((lam • A) X) • gi X) t =
      liftApply j (Ci 0 j) (liftMean Qi Ci f 0 δ) t := by
    apply liftApply_input_congr_at_time
    funext X
    simp only [gi, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hraw := liftApply_component_box_reserve j p q (Cc 0 j) (liftMean Q Cc f 0 δ) t v
    (mean.mean_raw_contDiff hlam A u ξ t ht)
    (fun m hm α w => coef.box m hm α v w t ht)
  have hrawi := liftApply_component_box_reserve j p q (Ci 0 j) (liftMean Qi Ci f 0 δ) t v
    (meani.mean_raw_contDiff hlam A u ξ t ht)
    (fun m hm α w => coefi.box m hm α v w t ht)
  refine ⟨(exponential_normalization_box_reserve p q (lam • A) _ hraw).sub
    (exponential_normalization_box_reserve p q (lam • A) _ hrawi), ?_⟩
  intro r hr s hs X z
  have hb := liftApply_exponential_input_paired_bound j p q δ r s hr hs
    (Cc 0 j) (Ci 0 j) g gi t X z v u hg hgi
    (fun m hm α w => coef.box m hm α v w t ht)
    (fun m hm α w => coefi.box m hm α v w t ht)
    lam eps Bi ((2 : ℝ) ^ (p + j) * K A) Bd ((2 : ℝ) ^ (p + j) * Kd A)
    hlam heps hBi (mul_nonneg (by positivity) (mean.constant_nonneg A)) hBd
    (mul_nonneg (by positivity) (hKd A)) A ξ
    (fun m hm α w a ha b hb y => coefi.bound m hm α v w a ha b hb t ht X y)
    (fun m hm α w a ha b hb y =>
      (coefd.bound m hm α v w a ha b hb t ht X y).trans_eq (by ring))
    (fun w a ha => by
      have hm := (mean.mean_component_grading hlam A u w ξ t ht a ha).2 X
      simpa only [g, Pi.smul_apply, f, mul_assoc] using hm)
    (fun w a ha => by
      have hd := ambient_paired_uncentered_mean_grading mean meani A u w ξ t ht
        (Kd A * (if w = u then 1 else 0) * ‖ξ‖) eps
        (fun d hd Y y => by
          simpa only [norm_mixed_jet_fast_zero, mul_assoc] using
            hmean A u w ξ d hd 0 (Nat.zero_le q) t ht Y y) a ha
      have hm := hd.2 X
      simpa only [g, gi, Pi.smul_apply, f, mul_assoc, mul_left_comm, mul_comm] using hm)
  rw [he, hei] at hb
  exact hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual earlier coefficient states yield the uncentered scalar-power source estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_power_grading_of_predecessors
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hn : 1 ≤ n) (hhh : hh ≤ H)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf) (Budget : ℕ → ℕ → ℝ)
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
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc
          (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y y v) z) X‖ ≤
        (ambientUncenteredScalarBudget D hh n Budget
          (ambientFirstCrossScalarConstant (n - 1) p q A CG Cw)
          (ambientSecondCrossScalarConstant (n - 2) p q A CG)
          (fun j => ambientSourceScalarConstant D (n - j) p q j A Cj) *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) * lam ^ (n + r) := by
  let Z := finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖
  let K₁ := ambientFirstCrossScalarConstant (n - 1) p q A CG Cw
  let K₂ := ambientSecondCrossScalarConstant (n - 2) p q A CG
  let KS := fun j => ambientSourceScalarConstant D (n - j) p q j A Cj
  have h₁ := setting_ambient_first_cross_lift_box P (n - 1) p q (p + 1) (q + 1)
    hp (by omega) le_rfl le_rfl _ _ data₁ A t ht v u ξ
  have hb₁ r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_ambient_first_cross_lift_bound P (n - 1) p q (p + 1) (q + 1)
      hp (by omega) le_rfl le_rfl _ _ data₁ A t ht v u ξ r s hr hs X z
  have h₂ (hn₂ : 2 ≤ n) := setting_ambient_second_cross_lift_box P (n - 2) p q (p + 2) q
    hp le_rfl le_rfl _ _ (data₂ hn₂) A t ht v u ξ
  have hb₂ (hn₂ : 2 ≤ n) r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_ambient_second_cross_lift_bound P (n - 2) p q (p + 2) q hp le_rfl le_rfl
      _ _ (data₂ hn₂) A t ht v u ξ r s hr hs X z
  have hS (hh0 : hh ≠ 0) j (hj : j ≤ min D n) :=
    setting_ambient_source_lift_box P sX sZ Cc hseq (hh - 1) (n - j) p q j
      (max D (p + j)) (max D (q + D - j)) (by omega) hp hq le_rfl le_rfl
      _ (dataS hh0 j hj) A t ht v u ξ
  have hbS (hh0 : hh ≠ 0) j (hj : j ≤ min D n) r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_source_lift_power_bound P sX sZ Cc hseq (hh - 1) (n - j) p q j
      (max D (p + j)) (max D (q + D - j)) (by omega) (hj.trans (Nat.min_le_left _ _))
      hp hq le_rfl le_rfl _ (dataS hh0 j hj) A t ht v u ξ r s hr hs X z
  have hresult := liftA_normalized_mixed_grading_of_terms Q Cc
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n p q t v A lam
    (K₁ * Budget hh (n - 1) * Z) (K₂ * Budget hh (n - 2) * Z)
    (fun j => KS j * Budget (hh - 1) (n - j) * Z) h₁
    (fun r hr s hs X z => by
      have he : n - 1 + 1 = n := by omega
      convert hb₁ r hr s hs X z using 1
      simp only [he]
      dsimp only [K₁, Z, ambientFirstCrossScalarConstant]
      ring) h₂
    (fun hn₂ r hr s hs X z => by
      have he : n - 2 + 2 = n := by omega
      convert hb₂ hn₂ r hr s hs X z using 1
      simp only [he]
      dsimp only [K₂, Z, ambientSecondCrossScalarConstant]
      ring) hS
    (fun hh0 j hj r hr s hs X z => by
      have he : n - j + j = n := by have he := hj.trans (Nat.min_le_right _ _); omega
      have hh' : hh - 1 + 1 = hh := by omega
      convert hbS hh0 j hj r hr s hs X z using 1
      simp only [he, hh']
      dsimp only [KS, Z]
      ring)
  rw [ambientUncenteredScalarBudget_factor D hh n hn Budget K₁ K₂ KS Z] at hresult
  simpa only [K₁, K₂, KS, Z, mul_assoc] using hresult
end

/-! Actual earlier coefficient states yield the uncentered scalar-power source estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_power_grading_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q : ℕ) (hn : 1 ≤ n)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf) (Budget : ℕ → ℕ → ℝ)
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
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc
          (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y y v) z) X‖ ≤
        (ambientUncenteredScalarBudget D hh n Budget
          (ambientFirstCrossScalarConstant (n - 1) p q A CG Cw)
          (ambientSecondCrossScalarConstant (n - 2) p q A CG)
          (fun j => ambientSourceScalarConstant D (n - j) p q j A Cj) *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) * lam ^ (n + r) := by
  let Z := finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖
  let K₁ := ambientFirstCrossScalarConstant (n - 1) p q A CG Cw
  let K₂ := ambientSecondCrossScalarConstant (n - 2) p q A CG
  let KS := fun j => ambientSourceScalarConstant D (n - j) p q j A Cj
  have h₁ := setting_ambient_first_cross_lift_box P (n - 1) p q (p + 1) (q + 1)
    hp (by omega) le_rfl le_rfl _ _ data₁ A t ht v u ξ
  have hb₁ r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_ambient_first_cross_lift_bound P (n - 1) p q (p + 1) (q + 1)
      hp (by omega) le_rfl le_rfl _ _ data₁ A t ht v u ξ r s hr hs X z
  have h₂ (hn₂ : 2 ≤ n) := setting_ambient_second_cross_lift_box P (n - 2) p q (p + 2) q
    hp le_rfl le_rfl _ _ (data₂ hn₂) A t ht v u ξ
  have hb₂ (hn₂ : 2 ≤ n) r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_ambient_second_cross_lift_bound P (n - 2) p q (p + 2) q hp le_rfl le_rfl
      _ _ (data₂ hn₂) A t ht v u ξ r s hr hs X z
  have hS (hh0 : hh ≠ 0) j (hj : j ≤ min D n) :=
    setting_ambient_source_lift_box_of_coefficients P Cc hper (hh - 1) (n - j) p q j
      (max D (p + j)) (max D (q + D - j)) hp hq le_rfl le_rfl
      _ (dataS hh0 j hj) A t ht v u ξ
  have hbS (hh0 : hh ≠ 0) j (hj : j ≤ min D n) r (hr : r ≤ p) s (hs : s ≤ q) X z :=
    setting_source_lift_power_bound_of_coefficients P Cc hper (hh - 1) (n - j) p q j
      (max D (p + j)) (max D (q + D - j)) (hj.trans (Nat.min_le_left _ _))
      hp hq le_rfl le_rfl _ (dataS hh0 j hj) A t ht v u ξ r s hr hs X z
  have hresult := liftA_normalized_mixed_grading_of_terms Q Cc
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n p q t v A lam
    (K₁ * Budget hh (n - 1) * Z) (K₂ * Budget hh (n - 2) * Z)
    (fun j => KS j * Budget (hh - 1) (n - j) * Z) h₁
    (fun r hr s hs X z => by
      have he : n - 1 + 1 = n := by omega
      convert hb₁ r hr s hs X z using 1
      simp only [he]
      dsimp only [K₁, Z, ambientFirstCrossScalarConstant]
      ring) h₂
    (fun hn₂ r hr s hs X z => by
      have he : n - 2 + 2 = n := by omega
      convert hb₂ hn₂ r hr s hs X z using 1
      simp only [he]
      dsimp only [K₂, Z, ambientSecondCrossScalarConstant]
      ring) hS
    (fun hh0 j hj r hr s hs X z => by
      have he : n - j + j = n := by have he := hj.trans (Nat.min_le_right _ _); omega
      have hh' : hh - 1 + 1 = hh := by omega
      convert hbS hh0 j hj r hr s hs X z using 1
      simp only [he, hh']
      dsimp only [KS, Z]
      ring)
  rw [ambientUncenteredScalarBudget_factor D hh n hn Budget K₁ K₂ KS Z] at hresult
  simpa only [K₁, K₂, KS, Z, mul_assoc] using hresult
end

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The tail uses the native scalar coefficient budget below the actual degree cutoff. -/

def tailCoefficientScalarBudget (K k L D H N hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  if n ≤ N then
    ambientCoefficientScalarBudget (K + N + D + 2) (max k (L + 2)) D H (N + D) N hh n CG Cw Cj
  else 0

theorem tailCoefficientScalarBudget_nonneg (K k L D H N hh n : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ tailCoefficientScalarBudget K k L D H N hh n CG Cw Cj := by
  unfold tailCoefficientScalarBudget
  split_ifs
  · exact ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _
  · exact le_rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The normalized flux term uses a scalar constant fixed before component families and scales. -/

def ambientSourceFluxTermConstant (P N k L D H hh n j : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  finiteLiftSymbolBudget (n - 1 - j) A * normalizedSourceUniformConstant D (P + 1) 0 j A Cj *
    ambientCoefficientScalarBudget P (max k (L + 2)) D H (N + D) N
      (hh - 1) (n - 1 - j) CG Cw Cj

theorem ambientSourceFluxTermConstant_nonneg (P N k L D H hh n j : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientSourceFluxTermConstant P N k L D H hh n j A CG Cw Cj :=
  mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg _ _)
    (normalizedSourceUniformConstant_nonneg _ _ _ _ _ _))
    (ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)

/-! An explicit finite-order majorant for the uncentered terms at every tail degree. -/

def tailUncenteredScalarBudget (K k L D H N hh n p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  ambientUncenteredScalarBudget D hh n
    (fun h m => tailCoefficientScalarBudget K k L D H N h m CG Cw Cj)
    (ambientFirstCrossScalarConstant (n - 1) p q A CG Cw)
    (ambientSecondCrossScalarConstant (n - 2) p q A CG)
    (fun j => ambientSourceScalarConstant D (n - j) p q j A Cj)

theorem tailUncenteredScalarBudget_nonneg (K k L D H N hh n p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ tailUncenteredScalarBudget K k L D H N hh n p q CG Cw Cj A :=
  ambientUncenteredScalarBudget_nonneg D hh n _ _ _ _
    (fun h m => tailCoefficientScalarBudget_nonneg K k L D H N h m CG Cw Cj)
    (ambientFirstCrossScalarConstant_nonneg _ _ _ _ _ _)
    (ambientSecondCrossScalarConstant_nonneg _ _ _ _ _)
    (fun j => ambientSourceScalarConstant_nonneg _ _ _ _ j _ _)

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Fixed finite orders determine one grade constant before component families and scales. -/

def ambientLiftEnergyGradeConstant (P N k L D H hh n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  (2 ^ m : ℝ) * (k + 1) * 2 ^ (r + 1) *
    ambientCoefficientScalarBudget P (max k (L + 2)) D H (N + D) N hh n CG Cw Cj

def ambientLiftWienerGradeConstant (P N k L D H hh n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  (2 ^ m : ℝ) * 4 * 2 ^ r * (centeredProfileJetConstant + 1) *
    ambientCoefficientScalarBudget P (max k (L + 2)) D H (N + D) N hh n CG Cw Cj

theorem ambient_lift_grade_constants_uniform (P N k L D H : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ hh ≤ H, ∀ n ≤ N, ∀ m ≤ N, ∀ r ≤ P,
      ambientLiftEnergyGradeConstant P N k L D H hh n m r CG Cw Cj ≤ C ∧
      ambientLiftWienerGradeConstant P N k L D H hh n m r CG Cw Cj ≤ C := by
  let J := Fin (H + 1) × Fin (N + 1) × Fin (N + 1) × Fin (P + 1)
  obtain ⟨C, hC, hb⟩ := finite_uniform_pair_budget
    (fun x : J => ambientLiftEnergyGradeConstant P N k L D H x.1 x.2.1 x.2.2.1 x.2.2.2 CG Cw Cj)
    (fun x : J => ambientLiftWienerGradeConstant P N k L D H x.1 x.2.1 x.2.2.1 x.2.2.2 CG Cw Cj)
  refine ⟨C, hC, ?_⟩
  intro hh hhh n hn m hm r hr
  exact hb (⟨hh, by omega⟩, ⟨n, by omega⟩, ⟨m, by omega⟩, ⟨r, by omega⟩)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The finite flux convolution has a fixed scalar budget independent of the component family. -/

def ambientSourceFluxMeanConstant (P N k L D H hh n : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
    ambientSourceFluxTermConstant P N k L D H hh n j A CG Cw Cj

theorem ambientSourceFluxMeanConstant_nonneg (P N k L D H hh n : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientSourceFluxMeanConstant P N k L D H hh n A CG Cw Cj :=
  Finset.sum_nonneg fun j _ =>
    ambientSourceFluxTermConstant_nonneg P N k L D H hh n j A CG Cw Cj

/-! A finite fixed-data budget dominates every source-flux calibration direction. -/

def ambientSourceFluxCalibrationConstant (P N k L D H hh n m : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j : Fin (m + 1), ∑ s : Fin n,
    ambientSourceFluxMeanConstant P N k L D H hh n
      ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) CG Cw Cj

theorem ambientSourceFluxCalibrationConstant_nonneg (P N k L D H hh n m : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientSourceFluxCalibrationConstant P N k L D H hh n m CG Cw Cj :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ =>
    ambientSourceFluxMeanConstant_nonneg P N k L D H hh n ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) CG Cw Cj

theorem ambientSourceFluxMeanConstant_calibration_le (P N k L D H hh n m : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (j : Fin (m + 1)) (s : Fin n) :
    ambientSourceFluxMeanConstant P N k L D H hh n
      ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) CG Cw Cj ≤
        ambientSourceFluxCalibrationConstant P N k L D H hh n m CG Cw Cj := by
  let F := fun (j : Fin (m + 1)) (s : Fin n) =>
    ambientSourceFluxMeanConstant P N k L D H hh n
      ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) CG Cw Cj
  have hF (j : Fin (m + 1)) (s : Fin n) : 0 ≤ F j s :=
    ambientSourceFluxMeanConstant_nonneg P N k L D H hh n
      ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) CG Cw Cj
  have h1 : F j s ≤ ∑ s : Fin n, F j s :=
    Finset.single_le_sum (fun s _ => hF j s) (Finset.mem_univ s)
  have h2 : (∑ s : Fin n, F j s) ≤ ∑ j : Fin (m + 1), ∑ s : Fin n, F j s :=
    Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun s _ => hF j s) (Finset.mem_univ j)
  exact h1.trans h2

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite budgets for the actual positive-height divergence coefficients. -/

def ambientPositiveMeanFluxWordConstant (P N k L D H hh n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (α : DerivativeWord2 m) : ℝ :=
  2 ^ r * max (Cw 0) 0 *
      ambientCoefficientScalarBudget P (max k (L + 2)) D H (N + D) N hh (n - 1) CG Cw Cj +
    finiteTestCalibrationConstant (n - 1) m α *
      (2 ^ r * ambientSourceFluxCalibrationConstant P N k L D H hh n m CG Cw Cj)

def ambientPositiveMeanFluxConstant (P N k L D H hh n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p : DerivativeWord2 m × Fin 2,
    ambientPositiveMeanFluxWordConstant P N k L D H hh n m r CG Cw Cj p.1

theorem ambientPositiveMeanFluxWordConstant_nonneg (P N k L D H hh n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (α : DerivativeWord2 m) :
    0 ≤ ambientPositiveMeanFluxWordConstant P N k L D H hh n m r CG Cw Cj α := by
  unfold ambientPositiveMeanFluxWordConstant
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (by positivity) (le_max_right _ _))
      (ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)
  · exact mul_nonneg (finiteTestCalibrationConstant_nonneg (n - 1) m α)
      (mul_nonneg (by positivity)
        (ambientSourceFluxCalibrationConstant_nonneg P N k L D H hh n m CG Cw Cj))

theorem ambientPositiveMeanFluxConstant_nonneg (P N k L D H hh n m r : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ ambientPositiveMeanFluxConstant P N k L D H hh n m r CG Cw Cj :=
  Finset.sum_nonneg fun p _ =>
    ambientPositiveMeanFluxWordConstant_nonneg P N k L D H hh n m r CG Cw Cj p.1

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The simultaneous rank induction keeps the actual coefficient and actual mean-source states. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

structure AmbientScalarPowerRecurrenceData (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (P Q₀ R N H hh n : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (F : ι → ι → ℝ) : Prop where
  coefficient : AmbientLiftCoefficientData par a b hab lam n (ambientDegreeSlowReserve P R n)
    (ambientDegreeFastReserve Q₀ D H R hh n) (Cc hh n)
    (fun v u => ambientCoefficientScalarBudget P Q₀ D H R N hh n CG Cw Cj *
      finiteMatrixPower F hh v u)
  uncentered : 1 ≤ n → AmbientLiftUncenteredData par a b hab lam hh n
    (ambientDegreeSlowReserve P R n) (ambientDegreeFastReserve Q₀ D H R hh n) Q Cc
    (ambientUncenteredBudget P Q₀ D H R hh n CG Cw Cj
      (fun h m => ambientCoefficientScalarBudget P Q₀ D H R N h m CG Cw Cj))
    (finiteMatrixPower F hh)
end

/-! A component-independent scalar budget for normalized tail tests. -/

def tailTestScalarBudget (K k L D H N hh n p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : (Vec 2 →L[ℝ] ℝ) → ℝ :=
  orderedTailScalarConstant N D hh n p q
    (fun h m => tailCoefficientScalarBudget K k L D H N h m CG Cw Cj)
    (tailUncenteredScalarBudget K k L D H N hh n p q CG Cw Cj)
    (fun h m => tailUncenteredScalarBudget K k L D H N h m (p + N) q CG Cw Cj)

theorem tailTestScalarBudget_nonneg (K k L D H N hh n p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ tailTestScalarBudget K k L D H N hh n p q CG Cw Cj A :=
  orderedTailScalarConstant_nonneg N D hh n p q _ _ _ A
    (fun h m => tailCoefficientScalarBudget_nonneg K k L D H N h m CG Cw Cj)
    (tailUncenteredScalarBudget_nonneg K k L D H N hh n p q CG Cw Cj A)
    (fun _ _ _ ab _ => tailUncenteredScalarBudget_nonneg K k L D H N ab.2 _ (p + N) q CG Cw Cj A)

end AVRegularity.CycleComparison.Lift
end
