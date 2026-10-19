-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Finite.WeakLift.RepresentationAdapters
import AVRegularity.Readout.RepresentationEstimates
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.CycleWords.CellTransitionLipschitz
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.CycleReference.TorusStreamFluxEquation
public import AVRegularity.Definitions.Iteration.CascadeStatement
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Readout.OperatorMap

@[expose] public noncomputable section

section
open Homogenization AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! Preserve the constant readout prefix and append the covariance and oscillatory
corrections at their two physical wavelengths. -/

variable {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

def appendCorrections (r : Representation H) (R : H →L[ℝ] H')
    (cov lift : Vec 2 → H') (E e : ℝ) : Representation H' where
  base := (r.map R).base
  profiles := (r.map R).profiles ++ [(cov, E)] ++ [(lift, e)]

theorem appendCorrections_value (r : Representation H) (R : H →L[ℝ] H')
    (cov lift : Vec 2 → H') (E e : ℝ) :
    (appendCorrections r R cov lift E e).value = fun x => R (r.value x) + cov x + lift x := by
  funext x
  simp only [Representation.value, appendCorrections, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  have h := congrFun (Readout.representation_map_value r R) x
  simp only [Representation.value] at h
  rw [← add_assoc, ← add_assoc, h]

theorem appendCorrections_size (s : ℝ) (K : ℕ) (r : Representation H) (R : H →L[ℝ] H')
    (cov lift : Vec 2 → H') (E e : ℝ) :
    representedSize s K e (appendCorrections r R cov lift E e) =
      representedSize s K e (r.map R) + profileNorm E K s cov + profileNorm e K s lift := by
  simp only [representedSize, appendCorrections, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  ac_rfl

theorem prefix_representation {e E : ℝ} {k K : ℕ} (he : 0 < e) (heE : e ≤ E)
    (hk : k ≤ K) (r : Representation H) (R : H →L[ℝ] H')
    (hr : IsRepresentationAt E K r) : IsRepresentationAt e k (r.map R) := by
  have hm := WeakLift.representationAt_order_mono hk
    (Readout.representation_map_isRepresentationAt r R hr)
  refine ⟨he, heE.trans hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
  intro p hp
  obtain ⟨hcd, hper, hE, h1⟩ := hm.2.2.2.2 p hp
  exact ⟨hcd, hper, heE.trans hE, h1⟩

theorem appendCorrections_representation {e E : ℝ} {k K : ℕ} (he : 0 < e) (heE : e ≤ E)
    (hk : k ≤ K) (r : Representation H) (R : H →L[ℝ] H')
    (hr : IsRepresentationAt E K r) (cov lift : Vec 2 → H')
    (hcov : ContDiff ℝ (k : ℕ) cov) (hcovp : IsZ2Periodic cov)
    (hlift : ContDiff ℝ (k : ℕ) lift) (hliftp : IsZ2Periodic lift) :
    IsRepresentationAt e k (appendCorrections r R cov lift E e) := by
  have hp := prefix_representation he heE hk r R hr
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_⟩
  intro p hmem
  simp only [appendCorrections, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hmem
  rcases hmem with (hmem | rfl) | rfl
  · exact hp.2.2.2.2 p hmem
  · exact ⟨hcov, hcovp, heE, hr.2.1⟩
  · exact ⟨hlift, hliftp, le_rfl, hp.2.1⟩

theorem prefix_size_le {e E s C : ℝ} {k K : ℕ} (he : 0 < e) (heE : e ≤ E)
    (hs : s < 1) (hk : k ≤ K) (r : Representation H) (R : H →L[ℝ] H')
    (hr : IsRepresentationAt E K r) (hR : ‖R‖ ≤ C) :
    representedSize s k e (r.map R) ≤ ENNReal.ofReal C * representedSize s K E r := by
  have hscale : representedSize s k e (r.map R) ≤ representedSize s k E (r.map R) := by
    unfold representedSize
    exact add_le_add (add_le_add (add_le_add le_rfl
      (Readout.profileSeminorm_le_label he heE hs _)) le_rfl) le_rfl
  calc
    _ ≤ representedSize s k E (r.map R) := hscale
    _ ≤ representedSize s K E (r.map R) := WeakLift.representedSize_order_mono s E hk _
    _ ≤ ENNReal.ofReal ‖R‖ * representedSize s K E r := Readout.representedSize_map_le r R hr
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hR) le_rfl

end AVRegularity.Finite.TerminalLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Finite.TerminalLift

/-! Finite-reserve algebra of the actual covariance polynomial. The coordinate maps needed
for mass normalization commute with the operator without an infinite smoothness assumption. -/

open Construction.Preservation.FullLift

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A constant map commutes with one covariance operator at its exact two-derivative reserve. -/
theorem terminal_covariance_operator_clm (A : Matrix (Fin 2) (Fin 2) ℝ)
    (R : V →L[ℝ] W) (f : Vec 2 → V) (hf : ContDiff ℝ 2 f) (x : Vec 2) :
    R (covOperator A f x) = covOperator A (fun y => R (f y)) x := by
  have h1 (j : Fin 2) : ContDiff ℝ 1 (Readout.along (basisVec j) f) :=
    Readout.along_contDiff (basisVec j) f hf
  have hRj (j : Fin 2) := Readout.along_comp R (basisVec j) f
    (hf.differentiable (by norm_num))
  have hRij (i j : Fin 2) := Readout.along_comp R (basisVec i)
    (Readout.along (basisVec j) f) ((h1 j).differentiable one_ne_zero)
  change R (∑ i : Fin 2, ∑ j : Fin 2,
    A i j • Readout.along (basisVec i) (Readout.along (basisVec j) f) x) =
    ∑ i : Fin 2, ∑ j : Fin 2,
      A i j • Readout.along (basisVec i) (Readout.along (basisVec j) (fun y => R (f y))) x
  simp only [map_sum, map_smul, hRj, hRij]

/-- A covariance power consumes exactly twice its degree when commuting with a constant map. -/
theorem terminal_covariance_iterate_clm (A : Matrix (Fin 2) (Fin 2) ℝ)
    (R : V →L[ℝ] W) (n : ℕ) (f : Vec 2 → V)
    (hf : ContDiff ℝ ((2 * n : ℕ) : ℕ∞) f) (x : Vec 2) :
    R ((covOperator A)^[n] f x) = (covOperator A)^[n] (fun y => R (f y)) x := by
  induction n generalizing f x with
  | zero => rfl
  | succ n ih =>
    have hlow : ContDiff ℝ ((2 * n : ℕ) : ℕ∞) f :=
      hf.of_le (by exact_mod_cast (by omega : 2 * n ≤ 2 * (n + 1)))
    have hmid := covOperator_iterate_contDiff A n 2 f
      (by simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hf)
    have he : (fun y => R ((covOperator A)^[n] f y)) =
        (covOperator A)^[n] (fun y => R (f y)) := funext (fun y => ih f hlow y)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      terminal_covariance_operator_clm A R _ hmid, he]

/-- The complete polynomial commutes with a constant map at finite input reserve 2p. -/
theorem terminal_covariance_polynomial_clm (A : Matrix (Fin 2) (Fin 2) ℝ)
    (R : V →L[ℝ] W) (p : ℕ) (f : Vec 2 → V)
    (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) (x : Vec 2) :
    R (covPolyP A p f x) = covPolyP A p (fun y => R (f y)) x := by
  simp only [covPolyP, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [terminal_covariance_iterate_clm A R n f
    (hf.of_le (by exact_mod_cast Nat.mul_le_mul_left 2 hn'))]

/-- A constant covariance matrix adds two coordinate letters before the tested word. -/
theorem terminal_covariance_operator_word {r : ℕ}
    (A : Matrix (Fin 2) (Fin 2) ℝ) (β : DerivativeWord2 r) (f : Vec 2 → V)
    (hf : ContDiff ℝ ((r + 2 : ℕ) : ℕ∞) f) :
    orderedDerivative β (covOperator A f) = fun x =>
      ∑ i : Fin 2, ∑ j : Fin 2,
        A i j • orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) β) f x := by
  have hw (i j : Fin 2) : orderedDerivative (![j, i] : DerivativeWord2 2) f =
      Readout.along (basisVec i) (Readout.along (basisVec j) f) := rfl
  have hreg (i j : Fin 2) : ContDiff ℝ (r : ℕ∞)
      (orderedDerivative (![j, i] : DerivativeWord2 2) f) := contDiff_orderedDerivative _ hf
  have hc : covOperator A f = fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      A i j • orderedDerivative (![j, i] : DerivativeWord2 2) f x := by
    simp only [hw]
    rfl
  rw [hc, orderedDerivative_finite_sum β _
    (fun i => ContDiff.sum fun j _ => (hreg i j).const_smul (A i j))]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [orderedDerivative_finite_sum β _
    (fun j => (hreg i j).const_smul (A i j))]
  apply Finset.sum_congr rfl
  intro j _
  have he := orderedDerivative_clm_comp (A i j • ContinuousLinearMap.id ℝ V)
    β (hreg i j)
  rw [CycleWords.orderedDerivative_append]
  simpa only [smul_apply, ContinuousLinearMap.id_apply] using congrFun he x

/-- A covariance power has a dimension-free scaled word bound at its exact finite reserve. -/
theorem terminal_covariance_iterate_word_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (E B : ℝ) (hE : 0 < E) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B * E ^ 2)
    (n r : ℕ) (f : Vec 2 → V) (hf : ContDiff ℝ ((r + 2 * n : ℕ) : ℕ∞) f)
    (β : DerivativeWord2 r) (x : Vec 2) :
    E ^ r * ‖orderedDerivative β ((covOperator A)^[n] f) x‖ ≤
      (4 * B) ^ n * (E ^ (r + 2 * n) * ‖iteratedFDeriv ℝ (r + 2 * n) f x‖) := by
  induction n generalizing r f β x with
  | zero =>
    simp only [mul_zero, add_zero, pow_zero, one_mul, Function.iterate_zero_apply] at hf ⊢
    exact mul_le_mul_of_nonneg_left (norm_orderedDerivative_le hf β x) (pow_nonneg hE.le r)
  | succ n ih =>
    have hmid : ContDiff ℝ ((r + 2 : ℕ) : ℕ∞) ((covOperator A)^[n] f) :=
      covOperator_iterate_contDiff A n (r + 2) f
        (by simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
    rw [Function.iterate_succ_apply', terminal_covariance_operator_word A β _ hmid]
    have hterm (i j : Fin 2) : E ^ r *
        ‖A i j • orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) β)
          ((covOperator A)^[n] f) x‖ ≤
        B * (4 * B) ^ n *
          (E ^ (r + 2 * (n + 1)) * ‖iteratedFDeriv ℝ (r + 2 * (n + 1)) f x‖) := by
      have hi := ih (2 + r) f
        (by simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
        (Fin.append (![j, i] : DerivativeWord2 2) β) x
      have he : 2 + r + 2 * n = r + 2 * (n + 1) := by omega
      rw [he] at hi
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ E ^ r * (B * E ^ 2 *
            ‖orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) β)
              ((covOperator A)^[n] f) x‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _))
            (pow_nonneg hE.le r)
        _ = B * (E ^ (2 + r) *
            ‖orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) β)
              ((covOperator A)^[n] f) x‖) := by rw [pow_add]; ring
        _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi hB
    calc
      _ ≤ E ^ r * ∑ i : Fin 2, ∑ j : Fin 2,
          ‖A i j • orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) β)
            ((covOperator A)^[n] f) x‖ := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hE.le r)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ = ∑ i : Fin 2, ∑ j : Fin 2, E ^ r *
          ‖A i j • orderedDerivative (Fin.append (![j, i] : DerivativeWord2 2) β)
            ((covOperator A)^[n] f) x‖ := by rw [Finset.mul_sum]; simp only [Finset.mul_sum]
      _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, B * (4 * B) ^ n *
          (E ^ (r + 2 * (n + 1)) * ‖iteratedFDeriv ℝ (r + 2 * (n + 1)) f x‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = _ := by simp only [Fin.sum_univ_two, pow_succ]; ring

end AVRegularity.Finite.TerminalLift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Finite.TerminalLift

/-! Classical covariance identification from the smooth value of the input. Unlike the
higher-carrier construction, this does not assume that the stored input carrier order covers
all derivatives of its given smooth representative. This is the situation in the terminal
profile estimates, which quantify arbitrary Kz and an independently smooth representation. -/

open Construction.Preservation.FullLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The duality-defined image equals the covariance polynomial of a smooth input value,
even when the input's stored Sobolev order is smaller than the polynomial order. -/
theorem terminal_covariance_rep_eq_from_value {K L n : ℕ}
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, A i j = A j i) (p : ℕ)
    (Z : TorusHk K E) (W : TorusHk L E) (u a : Vec 2 → E)
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) (hup : AVenhance.IsZ2Periodic u)
    (hZ : Z.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] u)
    (hW : IsCovImage (covPolyP A p) Z W) (ha : IsClassicalRep W a n) :
    a = covPolyP A p u := by
  have hc := covariancePolynomial_contDiff A p 0 (fun l => (l.factorial : ℝ)⁻¹) u
    (by simpa only [zero_add] using hu)
  have hp := covariancePolynomial_periodic A p (fun l => (l.factorial : ℝ)⁻¹) u hu hup
  rw [covariancePolynomial_eq_P] at hc hp
  let V := classicalHilbertHk 0 (covPolyP A p u) hc hp
  have hV : IsClassicalRep V (covPolyP A p u) 0 := classicalHilbertHk_rep _ _ hc hp
  have hVI : IsCovImage (covPolyP A p) Z V := by
    intro φ hφ hpφ
    have hv := classicalRep_value_ae V _ hV
    calc
      _ = cellInner (covPolyP A p u) φ := by
        apply integral_congr_ae
        filter_upwards [hv] with x hx
        rw [hx]
      _ = cellInner u (covPolyP A p φ) := by
        have hibp := covariancePolynomial_cellInner_adjoint A hA p
          (fun l => (l.factorial : ℝ)⁻¹) u φ hu
          (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hup hpφ
        simpa only [covariancePolynomial_eq_P] using hibp
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hZ] with x hx
        rw [hx]
  have hWI := covImage_truncate (Nat.zero_le L) (covPolyP A p) Z W hW
  have ha0 := classicalRep_truncate (Nat.zero_le L) le_rfl W a
    (classicalRep_order_mono W a ha (Nat.zero_le n))
  exact classical_covImage_rep_unique (covPolyP A p) Z
    (truncateTorusHk (Nat.zero_le L) W) V hWI hVI a (covPolyP A p u) ha0 hV

/-- The anchored primitive has a uniform parent-wavelength matrix bound at every time.
The constant and Lambda floor precede the terminal level, band chain and endpoints. -/
theorem terminal_covariance_uniform_matrix_bound {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 2 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ (tp t : ℝ) (i j : Fin 2),
          |ocCovariance α q Λ ζ M (κ M) (κ (M - 1)) tp t i j| ≤
            B * ocEpsilon q Λ (M - 1) ^ 2 := by
  obtain ⟨B, hB, Λ₀, hΛ₀, hcov⟩ := CycleReference.bandChain_covariance_estimates
    hα₀ hα₁ hs₀ hs₁ hq hζ
  have he := Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hexp : 0 ≤ ocGamma α q + 3 * ocDelta α q :=
    add_nonneg he.1.le (mul_nonneg (by norm_num) he.2.1.le)
  refine ⟨B, hB, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ tp t i j
  have hε := Scales.epsilon_basic (m := M - 1) hq.1 (hΛ₀.trans hΛ)
  have hp := Real.rpow_le_one hε.1.le hε.2.1 hexp
  have hb := (hcov Λ hΛ M (by omega) κ hκ M hM le_rfl tp t i j).2.1
  have hn : |ocCovariance α q Λ ζ M (κ M) (κ (M - 1)) tp t i j| /
      ocEpsilon q Λ (M - 1) ^ 2 ≤ B :=
    hb.trans (by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hp (zero_le_one.trans hB)))
  exact (div_le_iff₀ (pow_pos hε.1 2)).mp hn

/-- A normalized representation of the input values determines every stored readout value. -/
theorem terminal_readout_value_of_rep {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η : ℝ) (π : CompIn S → ℝ) (π' : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v)
    (Z : ∀ c : CompIn S', TorusHk K (ScalarH c.1.root)) (F : Vec 2 → CompSpace S')
    (hF : IsRepOf π' (fun c => truncateTorusHk (Nat.zero_le K) (Z c)) F)
    (v : CompIn S) :
    (succReadout (hr := ScalarH) m E η K Z v).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube]
      fun x => Real.sqrt (π v) * WithLp.ofLp (readoutCLM m E η π π' (F x)) v := by
  classical
  have hz (c : CompIn S') : (Z c).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => Real.sqrt (π' c) * WithLp.ofLp (F x) c := by
    have htr := KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le K) (Z c)
      (valueIndex2 0)
    exact htr.symm.trans (hF c)
  let q (c : CompIn S') : ℝ := E ^ (η * ((compWord m c.1).length : ℝ))
  let T (c : CompIn S') : TorusHk K ℝ :=
    if compParent m c.1 = v.1 then q c • Z c else 0
  have hread : succReadout (hr := ScalarH) m E η K Z v = ∑ c, T c := by
    unfold succReadout
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [T, q]
    split_ifs <;> rfl
  have ht (c : CompIn S') : (T c).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
        if compParent m c.1 = v.1 then q c * (Real.sqrt (π' c) * WithLp.ofLp (F x) c) else 0 := by
    dsimp only [T]
    split_ifs with hc
    · filter_upwards [KernelEnergy.torusJet_smul_ae (q c) (Z c) (valueIndex2 K), hz c]
        with x hq hx
      simp only [hq, hx, smul_eq_mul]
    · filter_upwards [KernelEnergy.torusHk_toFunction_jet_ae
        (0 : TorusHk K ℝ) (valueIndex2 K),
        (Lp.coeFn_zero ℝ 2 (volume.restrict AVenhance.unitCube))] with x hx h0
      rw [hx]
      exact h0
  rw [hread]
  filter_upwards [KernelEnergy.torusJet_sum_ae_of_eq T (valueIndex2 K) _ ht] with x hx
  rw [hx]
  change (∑ c, if compParent m c.1 = v.1 then
    q c * (Real.sqrt (π' c) * WithLp.ofLp (F x) c) else 0) =
    Real.sqrt (π v) * ∑ c, readoutMatrix m E η π π' v c * WithLp.ofLp (F x) c
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [readoutMatrix]
  split_ifs
  · calc
      _ = E ^ (η * ((compWord m c.1).length : ℝ)) *
          (Real.sqrt (π' c) * WithLp.ofLp (F x) c) := rfl
      _ = (Real.sqrt (π v) * (Real.sqrt (π v))⁻¹) *
          (E ^ (η * ((compWord m c.1).length : ℝ)) *
            (Real.sqrt (π' c) * WithLp.ofLp (F x) c)) := by
        rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (hπ v)).ne', one_mul]
      _ = _ := by ring
  · simp only [zero_mul, mul_zero]

end AVRegularity.Finite.TerminalLift
end
