-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransformBoundLetterSteps
import AVRegularity.Weighted.WordNativeSolutionPack
import Mathlib.Algebra.Ring.IsFormallyReal

/-! Genuine cell energy carriers for the literal moment Bloch jets. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Native component classes promote almost-everywhere periodic weak jets to an L2 time carrier. -/
theorem amplitudeId_periodic_jet_time_carrier {X : Type*} [MeasurableSpace X] {k : ℕ}
    (μ : Measure X) (D : X → RawJet2 k E)
    (hp : ∀ᵐ t ∂μ, HasPeriodicOrderedWeakJet (D t))
    (R : JetIndex2 k → X → Lp E 2 (volume.restrict AVenhance.unitCube))
    (hR : ∀ a, MemLp (R a) 2 μ)
    (he : ∀ᵐ t ∂μ, ∀ a, R a t =ᵐ[volume.restrict AVenhance.unitCube] D t a) :
    ∃ W : X → TorusHk k E, MemLp W 2 μ ∧
      ∀ᵐ t ∂μ, ∀ a, (W t).val a =ᵐ[volume.restrict AVenhance.unitCube] D t a := by
  classical
  let W : X → TorusHk k E := fun t =>
    if h : HasPeriodicOrderedWeakJet (D t) then (TorusHkFunction.mk (D t) h).toHk else 0
  have hw : ∀ᵐ t ∂μ, ∀ a, (W t).val a =ᵐ[volume.restrict AVenhance.unitCube] D t a := by
    filter_upwards [hp] with t ht
    intro a
    dsimp only [W]
    rw [dite_eq_left ht]
    exact torusJetToL2_ae (D t) ht.2.1 a
  refine ⟨W, CycleJointProofs.torusHk_time_memLp_of_jets μ W (fun a => ?_), hw⟩
  apply (hR a).ae_eq
  filter_upwards [he, hw] with t ht hwt
  exact Lp.ext ((ht a).trans (hwt a).symm)

variable [FiniteDimensional ℝ E]

/-- All polynomial energy budgets yield the literal component moment curves in cell L2 time. -/
theorem amplitudeId_native_moment_time_readout {k : ℕ}
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ k E) (hU : MemLp U 2 μ)
    (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (he : ∀ n : ℕ, (∫⁻ t, weightedFactorialNormSq n ϖ 0 r k (U t) ∂μ) ≠ ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (a : JetIndex2 k) :
    let R := fun t => amplitudeId_momentBlochReadout ϖ hϖ θ β e
      (Weighted.planeJetReadoutOperator k a (U t))
    MemLp R 2 μ ∧ ∀ᵐ t ∂μ,
      (R t =ᵐ[volume.restrict AVenhance.unitCube] CycleJointProofs.latticePeriodization
        (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          ((momentWeight β y * inner ℝ e ((U t).toFunction.jet a y) : ℝ) : ℂ))) ∧
      ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun j : Fin 2 → ℤ =>
        ‖Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift j) : ℂ))) *
          ((momentWeight β (z + AVenhance.latticeShift j) *
            inner ℝ e ((U t).toFunction.jet a (z + AVenhance.latticeShift j)) : ℝ) : ℂ)‖) := by
  let n := 2 * (β.1 + β.2 + 4)
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  have hq : Continuous q := (polynomialMomentRoot_continuous ϖ).pow n
  have hq0 (y : Vec 2) : 0 < q y := pow_pos
    (lt_of_lt_of_le zero_lt_one (polynomialMomentRoot_one_le ϖ y)) n
  let f := fun t => Weighted.planeJetReadoutOperator (E := E) k a (U t)
  have hf : MemLp f 2 μ := (Weighted.planeJetReadoutOperator (E := E) k a).comp_memLp' hU
  have hc : (∫⁻ t, Weighted.chartScalarEnergy (fun y => q y ^ 2) (f t) ∂μ) ≠ ⊤ := by
    have h := he n
    simp only [Weighted.weightedFactorialNormSq_stored_readout,
      Weighted.storedChartFactorialEnergy] at h
    have hcomp := Weighted.finite_integrated_weighted_sum_component μ
      (fun a : JetIndex2 k => factorialWeight r a.1.val)
      (fun a => Weighted.factorialWeight_pos_of_radius_pos r hr a.1.val) _ h a
    simpa only [q, polynomialMomentRoot_pow_sq] using hcomp
  have htime := amplitudeId_momentBlochReadout_time ϖ hϖ θ β e μ f hf hc
  refine ⟨htime.1, ?_⟩
  have hm := Weighted.chartScalarEnergy_stationary_time_aemeasurable
    (fun y => q y ^ 2) (hq.pow 2) (fun y => sq_pos_of_pos (hq0 y)) μ f hf
  filter_upwards [ae_lt_top' hm hc] with t ht
  have hread := amplitudeId_momentBlochReadout_readout ϖ hϖ θ β e (f t) ht.ne
  have hlat : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, ∀ j : Fin 2 → ℤ,
      f t (z + AVenhance.latticeShift j) = (U t).toFunction.jet a (z + AVenhance.latticeShift j) :=
    ae_all_iff.mpr (fun j => ((measurePreserving_add_right volume
      (AVenhance.latticeShift j)).quasiMeasurePreserving.ae_eq_comp
        (Weighted.planeJetReadout_ae_raw (U t) a)).restrict (s := AVenhance.unitCube))
  refine ⟨?_, ?_⟩
  · filter_upwards [hread.1, hlat] with z hz hl
    exact hz.trans (tsum_congr (fun j => congrArg
      (fun v : E => Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift j) : ℂ))) *
        ((momentWeight β (z + AVenhance.latticeShift j) * inner ℝ e v : ℝ) : ℂ)) (hl j)))
  · filter_upwards [hread.2, hlat] with z hz hl
    exact hz.congr (fun j => by rw [hl j])

/-- The monomial obtained by one derivative in the indicated coordinate. -/
def amplitudeId_lowerMoment (β : ℕ × ℕ) (i : Fin 2) : ℕ × ℕ :=
  Fin.cases (β.1 - 1, β.2) (fun _ => (β.1, β.2 - 1)) i

/-- The corresponding integer multiplicity, including the zero-degree case. -/
def amplitudeId_momentMultiplicity (β : ℕ × ℕ) (i : Fin 2) : ℕ := ![β.1, β.2] i

/-- The monomial gradient `momentWeightGrad` is exactly the lower monomial with its multiplicity. -/
theorem amplitudeId_momentWeightGrad_lower (β : ℕ × ℕ) (y : Vec 2) (i : Fin 2) :
    momentWeightGrad β y i = (amplitudeId_momentMultiplicity β i : ℝ) *
      momentWeight (amplitudeId_lowerMoment β i) y := by
  fin_cases i
  · change (β.1 : ℝ) * y 0 ^ (β.1 - 1) * y 1 ^ β.2 =
      (β.1 : ℝ) * (y 0 ^ (β.1 - 1) * y 1 ^ β.2)
    ring
  · change (β.2 : ℝ) * y 0 ^ β.1 * y 1 ^ (β.2 - 1) =
      (β.2 : ℝ) * (y 0 ^ β.1 * y 1 ^ (β.2 - 1))
    ring

omit [FiniteDimensional ℝ E] in
/-- Absolute image convergence gives the literal first derivative of each moment Bloch sum. -/
theorem amplitudeId_periodized_first_of_summable (U : PlaneHk Set.univ 1 E)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (i : Fin 2)
    (hv : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun n : Fin 2 → ℤ =>
      Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
        ((momentWeight β (z + AVenhance.latticeShift n) *
          inner ℝ e (U.toFunction.jet (valueIndex2 1) (z + AVenhance.latticeShift n)) : ℝ) : ℂ)))
    (hg : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun n : Fin 2 → ℤ =>
      Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
        ((momentWeight β (z + AVenhance.latticeShift n) *
          inner ℝ e (U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ (z + AVenhance.latticeShift n)) : ℝ) : ℂ)))
    (hl : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun n : Fin 2 → ℤ =>
      Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
        ((momentWeight (amplitudeId_lowerMoment β i) (z + AVenhance.latticeShift n) *
          inner ℝ e (U.toFunction.jet (valueIndex2 1) (z + AVenhance.latticeShift n)) : ℝ) : ℂ))) :
    CycleJointProofs.periodizeRawJet
      (multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet)
        ⟨⟨1, by decide⟩, fun _ => i⟩ =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => CycleJointProofs.latticePeriodization (fun y =>
        Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          ((momentWeight β y * inner ℝ e (U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) : ℝ) : ℂ)) z +
        (amplitudeId_momentMultiplicity β i : ℂ) * CycleJointProofs.latticePeriodization (fun y =>
          Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
            ((momentWeight (amplitudeId_lowerMoment β i) y *
              inner ℝ e (U.toFunction.jet (valueIndex2 1) y) : ℝ) : ℂ)) z -
        (Complex.I * (θ i : ℂ)) * CycleJointProofs.latticePeriodization (fun y =>
          Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
            ((momentWeight β y * inner ℝ e (U.toFunction.jet (valueIndex2 1) y) : ℝ) : ℂ)) z := by
  let V := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    ((momentWeight β y * inner ℝ e (U.toFunction.jet (valueIndex2 1) y) : ℝ) : ℂ)
  let H := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    ((momentWeight β y * inner ℝ e (U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) : ℝ) : ℂ)
  let L := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    ((momentWeight (amplitudeId_lowerMoment β i) y * inner ℝ e
      (U.toFunction.jet (valueIndex2 1) y) : ℝ) : ℂ)
  let c : ℂ := amplitudeId_momentMultiplicity β i
  let d : ℂ := Complex.I * (θ i : ℂ)
  have hvalue : U.toFunction.jet (valueIndex2 1) = planeValue U := by
    rw [planeValue_eq_stored]
    rfl
  have hgrad : U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ =
      planeJetOrder U 1 (fun _ => i) := by
    rw [planeJetOrder_eq_stored le_rfl]
  have hpoint (y : Vec 2) : multiplicationRawJet (amplitudeId_momentCoefficient θ β e)
      U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y = H y + c * L y - d * V y := by
    rw [amplitudeId_moment_jet_first, ← hvalue, ← hgrad, amplitudeId_momentWeightGrad_lower]
    dsimp only [H, L, V, c, d]
    push_cast
    ring
  filter_upwards [hv, hg, hl] with z hzv hzg hzl
  have he := (hzg.add (hzl.mul_left c)).tsum_sub (hzv.mul_left d)
  rw [hzg.tsum_add (hzl.mul_left c)] at he
  simp only [tsum_mul_left] at he
  exact (tsum_congr (fun n => hpoint (z + AVenhance.latticeShift n))).trans he

private def amplitudeId_firstJetClasses (v : CycleEvolution.ComplexCellL2)
    (d : Fin 2 → CycleEvolution.ComplexCellL2) :
    JetIndex2 1 → CycleEvolution.ComplexCellL2
  | ⟨⟨0, _⟩, _⟩ => v
  | ⟨⟨n + 1, _⟩, w⟩ => d (w ⟨0, Nat.succ_pos n⟩)

/-- All moments of the plane H1 curve yield a genuine energy carrier of its literal Bloch jet. -/
theorem amplitudeId_moment_cell_state
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ 1 E) (hU : MemLp U 2 μ)
    (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (he : ∀ n : ℕ, (∫⁻ t, weightedFactorialNormSq n ϖ 0 r 1 (U t) ∂μ) ≠ ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) :
    ∃ W : ℝ → TorusHk 1 ℂ, MemLp W 2 μ ∧
      ∀ᵐ t ∂μ, ∀ a, (W t).val a =ᵐ[volume.restrict AVenhance.unitCube]
        CycleJointProofs.periodizeRawJet
          (multiplicationRawJet (amplitudeId_momentCoefficient θ β e) (U t).toFunction.jet) a := by
  let M := fun (γ : ℕ × ℕ) (a : JetIndex2 1) t => amplitudeId_momentBlochReadout ϖ hϖ θ γ e
    (Weighted.planeJetReadoutOperator 1 a (U t))
  have hM (γ : ℕ × ℕ) (a : JetIndex2 1) :=
    amplitudeId_native_moment_time_readout μ U hU ϖ r hϖ hr he θ γ e a
  let V := M β (valueIndex2 1)
  let G := fun (i : Fin 2) t => M β ⟨⟨1, by decide⟩, fun _ => i⟩ t +
    (amplitudeId_momentMultiplicity β i : ℂ) • M (amplitudeId_lowerMoment β i) (valueIndex2 1) t -
    (Complex.I * (θ i : ℂ)) • V t
  let R := fun (a : JetIndex2 1) t => amplitudeId_firstJetClasses (V t) (fun i => G i t) a
  let D := fun t => CycleJointProofs.periodizeRawJet
    (multiplicationRawJet (amplitudeId_momentCoefficient θ β e) (U t).toFunction.jet)
  have hR (a : JetIndex2 1) : MemLp (R a) 2 μ := by
    rcases a with ⟨a, w⟩
    fin_cases a
    · exact (hM β (valueIndex2 1)).1
    · exact (((hM β ⟨⟨1, by decide⟩, fun _ => w 0⟩).1.add
        ((hM (amplitudeId_lowerMoment β (w 0)) (valueIndex2 1)).1.const_smul
          (amplitudeId_momentMultiplicity β (w 0) : ℂ))).sub
        ((hM β (valueIndex2 1)).1.const_smul (Complex.I * (θ (w 0) : ℂ))))
  have hfin (n : ℕ) : ∀ᵐ t ∂μ, weightedFactorialNormSq n ϖ 0 r 1 (U t) ≠ ⊤ :=
    (ae_lt_top' (Weighted.weightedFactorialNormSq_time_aemeasurable n ϖ 0 r μ U hU)
      (he n)).mono (fun _ ht => ht.ne)
  have hp : ∀ᵐ t ∂μ, HasPeriodicOrderedWeakJet (D t) := by
    filter_upwards [ae_all_iff.mpr hfin] with t ht
    exact amplitudeId_periodized_moment_weakJet (U t) ϖ hϖ
      (fun a n => amplitudeId_stored_moment_finite (U t) n ϖ r hr (ht n) a) θ β e
  apply amplitudeId_periodic_jet_time_carrier μ D hp R hR
  have hv := (hM β (valueIndex2 1)).2
  have hg (i : Fin 2) := (hM β ⟨⟨1, by decide⟩, fun _ => i⟩).2
  have hl (i : Fin 2) := (hM (amplitudeId_lowerMoment β i) (valueIndex2 1)).2
  filter_upwards [hv, ae_all_iff.mpr hg, ae_all_iff.mpr hl] with t hvt hgt hlt
  have hvalue : (U t).toFunction.jet (valueIndex2 1) = planeValue (U t) := by
    rw [planeValue_eq_stored]
    rfl
  have hzero : V t =ᵐ[volume.restrict AVenhance.unitCube] D t (valueIndex2 1) := by
    apply hvt.1.trans
    exact Filter.Eventually.of_forall (fun z => tsum_congr (fun j => by
      have h := (amplitudeId_moment_jet_value (U t) θ β e (z + AVenhance.latticeShift j)).symm
      simpa only [← hvalue] using h))
  have hgrad (i : Fin 2) : G i t =ᵐ[volume.restrict AVenhance.unitCube]
      D t ⟨⟨1, by decide⟩, fun _ => i⟩ := by
    have hfirst := amplitudeId_periodized_first_of_summable (U t) θ β e i
      (hvt.2.mono (fun _ h => Summable.of_norm (f := _) h))
      ((hgt i).2.mono (fun _ h => Summable.of_norm (f := _) h))
      ((hlt i).2.mono (fun _ h => Summable.of_norm (f := _) h))
    have hread : G i t =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
        CycleJointProofs.latticePeriodization (fun y =>
          Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
            ((momentWeight β y * inner ℝ e
              ((U t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) : ℝ) : ℂ)) z +
        (amplitudeId_momentMultiplicity β i : ℂ) *
          CycleJointProofs.latticePeriodization (fun y =>
            Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
              ((momentWeight (amplitudeId_lowerMoment β i) y *
                inner ℝ e ((U t).toFunction.jet (valueIndex2 1) y) : ℝ) : ℂ)) z -
        (Complex.I * (θ i : ℂ)) * CycleJointProofs.latticePeriodization (fun y =>
          Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
            ((momentWeight β y * inner ℝ e ((U t).toFunction.jet (valueIndex2 1) y) : ℝ) : ℂ)) z := by
      let c : ℂ := amplitudeId_momentMultiplicity β i
      let d : ℂ := Complex.I * (θ i : ℂ)
      let A := M β ⟨⟨1, by decide⟩, fun _ => i⟩ t
      let B := M (amplitudeId_lowerMoment β i) (valueIndex2 1) t
      filter_upwards [Lp.coeFn_sub (A + c • B) (d • V t), Lp.coeFn_add A (c • B),
        Lp.coeFn_smul c B, Lp.coeFn_smul d (V t), (hgt i).1, (hlt i).1, hvt.1]
        with z hsub hadd hc hd ha hb hvz
      change (A + c • B - d • V t) z = _
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hc, hd]
      simp only [Pi.smul_apply, smul_eq_mul]
      change A z = _ at ha
      change B z = _ at hb
      change V t z = _ at hvz
      rw [ha, hb, hvz]
    exact hread.trans hfirst.symm
  intro a
  rcases a with ⟨a, w⟩
  fin_cases a
  · have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact hzero
  · have hw : w = fun _ => w 0 := funext (fun k => congrArg w (Subsingleton.elim _ _))
    rw [hw]
    exact hgrad (w 0)

/-- The metric Laplacian is a finite linear combination of lower monomials. -/
theorem amplitudeId_momentWeightLap_lower (β : ℕ × ℕ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (y : Vec 2) :
    momentWeightLap G β y = ∑ i : Fin 2, ∑ k : Fin 2,
      G i k * (amplitudeId_momentMultiplicity β i : ℝ) *
        (amplitudeId_momentMultiplicity (amplitudeId_lowerMoment β i) k : ℝ) *
        momentWeight (amplitudeId_lowerMoment (amplitudeId_lowerMoment β i) k) y := by
  rw [← amplitudeId_moment_laplacian]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hf : (fun z => momentWeightGrad β z i) =
      (fun z => (amplitudeId_momentMultiplicity β i : ℝ) *
        momentWeight (amplitudeId_lowerMoment β i) z) :=
    funext (fun z => amplitudeId_momentWeightGrad_lower β z i)
  rw [hf, fderiv_const_mul
    ((amplitudeId_moment_contDiff _).differentiable (by simp)).differentiableAt]
  simp only [smul_apply, smul_eq_mul, amplitudeId_moment_fderiv,
    amplitudeId_momentWeightGrad_lower]
  ring

/-- Absolutely convergent Bloch sums commute with finite periodic-coefficient combinations. -/
theorem amplitudeId_planeBloch_finite_sum {J : Type*} [Fintype J]
    (θ : Vec 2) (c f : J → Vec 2 → ℝ) (z : Vec 2)
    (hc : ∀ j (n : Fin 2 → ℤ), c j (z + AVenhance.latticeShift n) = c j z)
    (hf : ∀ j, Summable (fun n : Fin 2 → ℤ =>
      Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
        (f j (z + AVenhance.latticeShift n) : ℂ))) :
    planeBlochC θ (fun y => ∑ j, c j y * f j y) z =
      ∑ j, (c j z : ℂ) * planeBlochC θ (f j) z := by
  classical
  have hp (n : Fin 2 → ℤ) :
      Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
        ((∑ j, c j (z + AVenhance.latticeShift n) *
          f j (z + AVenhance.latticeShift n) : ℝ) : ℂ) =
      ∑ j, (c j z : ℂ) *
        (Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
          (f j (z + AVenhance.latticeShift n) : ℂ)) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc j n]
    ring
  change (∑' n : Fin 2 → ℤ,
    Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
      ((∑ j, c j (z + AVenhance.latticeShift n) *
        f j (z + AVenhance.latticeShift n) : ℝ) : ℂ)) = _
  rw [tsum_congr hp, Summable.tsum_finsetSum (fun j _ => (hf j).mul_left (c j z : ℂ))]
  simp only [tsum_mul_left, planeBlochC]
  rfl

/-- Finite bounded periodic multipliers preserve the native moment forcing curves. -/
theorem amplitudeId_cell_forcing_combination {J : Type*} [Fintype J]
    (I : Set ℝ) (θ : Vec 2) (c f : J → ℝ → Vec 2 → ℝ)
    (hc : ∀ j, Measurable (Function.uncurry (c j)))
    (hp : ∀ j t, AVenhance.IsZ2Periodic (c j t))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j t y, |c j t y| ≤ B j)
    (M : J → ℝ → CycleEvolution.ComplexCellL2)
    (hM : ∀ j, MemLp (M j) 2 (volume.restrict I))
    (hm : ∀ j, ∀ᵐ t ∂volume.restrict I,
      M j t =ᵐ[volume.restrict AVenhance.unitCube] planeBlochC θ (f j t))
    (hs : ∀ j, ∀ᵐ t ∂volume.restrict I,
      ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun n : Fin 2 → ℤ =>
        Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
          (f j t (z + AVenhance.latticeShift n) : ℂ))) :
    ∃ R : ℝ → CycleEvolution.ComplexCellL2, MemLp R 2 (volume.restrict I) ∧
      ∀ᵐ t ∂volume.restrict I, R t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => ∑ j, c j t y * f j t y) := by
  classical
  let C := fun j t => CycleEvolution.cellCoefficientComplexCLM
    (fun y => (c j t y : ℂ))
    (((Complex.continuous_ofReal.measurable.comp (hc j)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (B j) (hB j) (fun y => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb j t y)
  let R := fun t => ∑ j, C j t (M j t)
  have hR : MemLp R 2 (volume.restrict I) := by
    apply memLp_finsetSum
    intro j _
    exact CycleEvolution.cellTimeCoefficient_memLp I (fun t y => (c j t y : ℂ))
      (Complex.continuous_ofReal.measurable.comp (hc j)) (B j) (hB j)
      (fun t y => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb j t y)
      (M j) (hM j)
  refine ⟨R, hR, ?_⟩
  filter_upwards [ae_all_iff.mpr hm, ae_all_iff.mpr hs] with t hmt hst
  have hC (j : J) : C j t (M j t) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => (c j t y : ℂ) * planeBlochC θ (f j t) y := by
    have h := CycleEvolution.cellCoefficientCLM_ae (fun y => (c j t y : ℂ))
      (((Complex.continuous_ofReal.measurable.comp (hc j)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (B j) (hB j) (fun y => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb j t y)
      (M j t)
    filter_upwards [h, hmt j] with y hy hmj
    exact hy.trans (congrArg (fun x : ℂ => (c j t y : ℂ) * x) hmj)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => C j t (M j t)),
    ae_all_iff.mpr hC, ae_all_iff.mpr hst] with z hz hcz hsz
  change (∑ j, C j t (M j t)) z = _
  rw [hz]
  simp only [Finset.sum_apply]
  calc
    (∑ j, C j t (M j t) z) = ∑ j, (c j t z : ℂ) * planeBlochC θ (f j t) z :=
      Finset.sum_congr rfl (fun j _ => hcz j)
    _ = planeBlochC θ (fun y => ∑ j, c j t y * f j t y) z :=
      (amplitudeId_planeBloch_finite_sum θ (fun j => c j t) (fun j => f j t) z
        (fun j n => hp j t n z) hsz).symm

/-- Native L2 moment values together with their literal absolutely convergent image readouts. -/
structure AmplitudeIdMomentCellFamily (I : Set ℝ) (θ : Vec 2) (f : ℝ → Vec 2 → ℝ) where
  value : (ℕ × ℕ) → ℝ → CycleEvolution.ComplexCellL2
  mem : ∀ β, MemLp (value β) 2 (volume.restrict I)
  readout : ∀ β, ∀ᵐ t ∂volume.restrict I,
    value β t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight β y * f t y)
  summable : ∀ β, ∀ᵐ t ∂volume.restrict I,
    ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun n : Fin 2 → ℤ =>
      Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) *
        ((momentWeight β (z + AVenhance.latticeShift n) *
          f t (z + AVenhance.latticeShift n) : ℝ) : ℂ))

/-- Every native plane curve with all moment budgets supplies a moment cell family. -/
def amplitudeId_native_moment_family {k : ℕ} (I : Set ℝ)
    (U : ℝ → PlaneHk Set.univ k E) (hU : MemLp U 2 (volume.restrict I))
    (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (he : ∀ n : ℕ, (∫⁻ t in I, weightedFactorialNormSq n ϖ 0 r k (U t)) ≠ ⊤)
    (θ : Vec 2) (e : E) :
    AmplitudeIdMomentCellFamily I θ (fun t y => inner ℝ e (planeValue (U t) y)) where
  value β t := amplitudeId_momentBlochReadout ϖ hϖ θ β e
    (Weighted.planeJetReadoutOperator k (valueIndex2 k) (U t))
  mem β := (amplitudeId_native_moment_time_readout (volume.restrict I) U hU ϖ r hϖ hr
    he θ β e (valueIndex2 k)).1
  readout β := by
    have h := (amplitudeId_native_moment_time_readout (volume.restrict I) U hU ϖ r hϖ hr
      he θ β e (valueIndex2 k)).2.mono (fun _ ht => ht.1)
    have hv (t : ℝ) : (U t).toFunction.jet (valueIndex2 k) = planeValue (U t) := by
      rw [planeValue_eq_stored]
      rfl
    simp_rw [hv] at h
    exact h
  summable β := by
    have h := (amplitudeId_native_moment_time_readout (volume.restrict I) U hU ϖ r hϖ hr
      he θ β e (valueIndex2 k)).2.mono (fun _ ht => ht.2.mono
        (fun _ hz => Summable.of_norm (f := _) hz))
    have hv (t : ℝ) : (U t).toFunction.jet (valueIndex2 k) = planeValue (U t) := by
      rw [planeValue_eq_stored]
      rfl
    simp_rw [hv] at h
    exact h

/-- Moment families are independent of the chosen plane representatives. -/
def AmplitudeIdMomentCellFamily.congr {I : Set ℝ} {θ : Vec 2}
    {f g : ℝ → Vec 2 → ℝ} (M : AmplitudeIdMomentCellFamily I θ f)
    (h : ∀ᵐ t ∂volume.restrict I, f t =ᵐ[volume] g t) :
    AmplitudeIdMomentCellFamily I θ g where
  value := M.value
  mem := M.mem
  readout β := by
    filter_upwards [M.readout β, h] with t ht hfg
    have hl : ∀ᵐ z ∂volume.restrict AVenhance.unitCube,
        ∀ n : Fin 2 → ℤ, f t (z + AVenhance.latticeShift n) = g t (z + AVenhance.latticeShift n) :=
      ae_all_iff.mpr (fun n => ((measurePreserving_add_right volume
        (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp hfg).restrict
          (s := AVenhance.unitCube))
    filter_upwards [ht, hl] with z hz hzl
    exact hz.trans (tsum_congr (fun n => congrArg
      (fun x : ℝ => Complex.exp (-(Complex.I * (vecDot θ
        (z + AVenhance.latticeShift n) : ℂ))) *
          ((momentWeight β (z + AVenhance.latticeShift n) * x : ℝ) : ℂ)) (hzl n)))
  summable β := by
    filter_upwards [M.summable β, h] with t ht hfg
    have hl : ∀ᵐ z ∂volume.restrict AVenhance.unitCube,
        ∀ n : Fin 2 → ℤ, f t (z + AVenhance.latticeShift n) = g t (z + AVenhance.latticeShift n) :=
      ae_all_iff.mpr (fun n => ((measurePreserving_add_right volume
        (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp hfg).restrict
          (s := AVenhance.unitCube))
    filter_upwards [ht, hl] with z hz hzl
    exact hz.congr (fun n => by rw [hzl n])

/-- Bounded periodic finite combinations of selected moments have literal L2 time readouts. -/
theorem amplitudeId_moment_family_combination {J : Type*} [Fintype J]
    (I : Set ℝ) (θ : Vec 2) (f : J → ℝ → Vec 2 → ℝ)
    (M : ∀ j, AmplitudeIdMomentCellFamily I θ (f j)) (γ : J → ℕ × ℕ)
    (c : J → ℝ → Vec 2 → ℝ)
    (hc : ∀ j, Measurable (Function.uncurry (c j)))
    (hp : ∀ j t, AVenhance.IsZ2Periodic (c j t))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j t y, |c j t y| ≤ B j) :
    ∃ R : ℝ → CycleEvolution.ComplexCellL2, MemLp R 2 (volume.restrict I) ∧
      ∀ᵐ t ∂volume.restrict I, R t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => ∑ j, c j t y * momentWeight (γ j) y * f j t y) := by
  have h := amplitudeId_cell_forcing_combination I θ c
    (fun j t y => momentWeight (γ j) y * f j t y) hc hp B hB hb
    (fun j => (M j).value (γ j)) (fun j => (M j).mem (γ j))
    (fun j => (M j).readout (γ j)) (fun j => (M j).summable (γ j))
  simpa only [mul_assoc] using h

/-- Both literal commutator sources have native cell L2 time representatives. -/
theorem amplitudeId_moment_forcing_curves (I : Set ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (θ : Vec 2) (β : ℕ × ℕ) (u : ℝ → Vec 2 → ℝ) (S : Fin 2 → ℝ → Vec 2 → ℝ)
    (Mu : AmplitudeIdMomentCellFamily I θ u)
    (MS : ∀ i, AmplitudeIdMomentCellFamily I θ (S i)) :
    (∃ R : ℝ → CycleEvolution.ComplexCellL2, MemLp R 2 (volume.restrict I) ∧
      ∀ᵐ t ∂volume.restrict I, R t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y =>
          (momentWeightLap (G t) β y + ∑ i, v t y i * momentWeightGrad β y i) * u t y -
            ∑ i, momentWeightGrad β y i * S i t y)) ∧
    (∀ k : Fin 2, ∃ R : ℝ → CycleEvolution.ComplexCellL2, MemLp R 2 (volume.restrict I) ∧
      ∀ᵐ t ∂volume.restrict I, R t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight β y * S k t y -
          (∑ i, (G t k i + G t i k) * momentWeightGrad β y i) * u t y)) := by
  classical
  obtain ⟨V, hV⟩ := hv.2.1
  let a := fun i : Fin 2 => (amplitudeId_momentMultiplicity β i : ℝ)
  let b := fun i k : Fin 2 =>
    (amplitudeId_momentMultiplicity (amplitudeId_lowerMoment β i) k : ℝ)
  have ha (i : Fin 2) : 0 ≤ a i := Nat.cast_nonneg _
  have hb (i k : Fin 2) : 0 ≤ b i k := Nat.cast_nonneg _
  have hgm (i k : Fin 2) : Measurable (fun p : ℝ × Vec 2 => G p.1 i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hG.1)
  have hvm (i : Fin 2) : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2 i) :=
    (measurable_pi_apply i).comp hv.1
  have hvp (i : Fin 2) (t : ℝ) : AVenhance.IsZ2Periodic (fun y => v t y i) :=
    fun n z => congrFun (hv.2.2.1 t n z) i
  constructor
  · let J := (Fin 2 × Fin 2) ⊕ (Fin 2 ⊕ Fin 2)
    let f : J → ℝ → Vec 2 → ℝ := Sum.elim (fun _ => u) (Sum.elim (fun _ => u) S)
    let M : ∀ j, AmplitudeIdMomentCellFamily I θ (f j) :=
      Sum.rec (fun _ => Mu) (Sum.rec (fun _ => Mu) MS)
    let γ : J → ℕ × ℕ := Sum.elim
      (fun p => amplitudeId_lowerMoment (amplitudeId_lowerMoment β p.1) p.2)
      (Sum.elim (amplitudeId_lowerMoment β) (amplitudeId_lowerMoment β))
    let c : J → ℝ → Vec 2 → ℝ := Sum.elim
      (fun p t _ => G t p.1 p.2 * a p.1 * b p.1 p.2)
      (Sum.elim (fun i t y => v t y i * a i) (fun i _ _ => -(a i)))
    let B : J → ℝ := Sum.elim (fun p => 2 * a p.1 * b p.1 p.2)
      (Sum.elim (fun i => |V| * a i) a)
    have hc (j : J) : Measurable (Function.uncurry (c j)) := by
      rcases j with p | (i | i)
      · exact ((hgm p.1 p.2).mul_const _).mul_const _
      · exact (hvm i).mul_const _
      · exact measurable_const
    have hp (j : J) (t : ℝ) : AVenhance.IsZ2Periodic (c j t) := by
      rcases j with p | (i | i)
      · exact fun _ _ => rfl
      · exact fun n z => congrArg (fun x : ℝ => x * a i) (hvp i t n z)
      · exact fun _ _ => rfl
    have hB (j : J) : 0 ≤ B j := by
      rcases j with p | (i | i)
      · exact mul_nonneg (mul_nonneg (by norm_num) (ha _)) (hb _ _)
      · exact mul_nonneg (abs_nonneg _) (ha _)
      · exact ha _
    have hbound (j : J) (t : ℝ) (y : Vec 2) : |c j t y| ≤ B j := by
      rcases j with p | (i | i)
      · change |G t p.1 p.2 * a p.1 * b p.1 p.2| ≤ _
        rw [abs_mul, abs_mul, abs_of_nonneg (ha _), abs_of_nonneg (hb _ _)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (CycleEvolution.cellMetric_entry_bound hG t y p.1 p.2)
            (ha _)) (hb _ _)
      · change |v t y i * a i| ≤ _
        rw [abs_mul, abs_of_nonneg (ha _)]
        exact mul_le_mul_of_nonneg_right (CycleEvolution.cellDrift_entry_bound hV t y i) (ha _)
      · change |-(a i)| ≤ a i
        rw [abs_neg, abs_of_nonneg (ha _)]
    obtain ⟨R, hR, hread⟩ := amplitudeId_moment_family_combination I θ f M γ c hc hp B hB hbound
    refine ⟨R, hR, hread.mono (fun t ht => ?_)⟩
    have he (y : Vec 2) : (∑ j, c j t y * momentWeight (γ j) y * f j t y) =
        (momentWeightLap (G t) β y + ∑ i, v t y i * momentWeightGrad β y i) * u t y -
          ∑ i, momentWeightGrad β y i * S i t y := by
      dsimp only [J]
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, c, γ, f, Sum.elim_inl,
        Sum.elim_inr, amplitudeId_momentWeightLap_lower, amplitudeId_momentWeightGrad_lower]
      simp only [Fin.sum_univ_two, a, b]
      ring
    simpa only [he] using ht
  · intro k
    let J := Unit ⊕ Fin 2
    let f : J → ℝ → Vec 2 → ℝ := Sum.elim (fun _ => S k) (fun _ => u)
    let M : ∀ j, AmplitudeIdMomentCellFamily I θ (f j) := Sum.rec (fun _ => MS k) (fun _ => Mu)
    let γ : J → ℕ × ℕ := Sum.elim (fun _ => β) (amplitudeId_lowerMoment β)
    let c : J → ℝ → Vec 2 → ℝ := Sum.elim (fun _ _ _ => 1)
      (fun i t _ => -((G t k i + G t i k) * a i))
    let B : J → ℝ := Sum.elim (fun _ => 1) (fun i => (2 + 2) * a i)
    have hc (j : J) : Measurable (Function.uncurry (c j)) := by
      rcases j with _ | i
      · exact measurable_const
      · exact (((hgm k i).add (hgm i k)).mul_const _).neg
    have hp (j : J) (t : ℝ) : AVenhance.IsZ2Periodic (c j t) := by
      cases j <;> exact fun _ _ => rfl
    have hB (j : J) : 0 ≤ B j := by
      rcases j with _ | i
      · exact zero_le_one
      · exact mul_nonneg (by norm_num) (ha i)
    have hbound (j : J) (t : ℝ) (y : Vec 2) : |c j t y| ≤ B j := by
      rcases j with _ | i
      · change |(1 : ℝ)| ≤ 1
        rw [abs_one]
      · change |-((G t k i + G t i k) * a i)| ≤ _
        rw [abs_neg, abs_mul, abs_of_nonneg (ha i)]
        exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add
          (CycleEvolution.cellMetric_entry_bound hG t y k i)
          (CycleEvolution.cellMetric_entry_bound hG t y i k))) (ha i)
    obtain ⟨R, hR, hread⟩ := amplitudeId_moment_family_combination I θ f M γ c hc hp B hB hbound
    refine ⟨R, hR, hread.mono (fun t ht => ?_)⟩
    have he (y : Vec 2) : (∑ j, c j t y * momentWeight (γ j) y * f j t y) =
        momentWeight β y * S k t y -
          (∑ i, (G t k i + G t i k) * momentWeightGrad β y i) * u t y := by
      dsimp only [J]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, c, γ, f, Sum.elim_inl,
        Sum.elim_inr, one_mul, amplitudeId_momentWeightGrad_lower]
      simp only [Fin.sum_univ_two, a]
      ring
    simpa only [he] using ht

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A flux coordinate is the Hilbert coordinate of the corresponding single vector. -/
theorem amplitudeId_flux_inner_single (e : E) (k : Fin 2)
    (S : PiLp 2 (fun _ : Fin 2 => E)) :
    inner ℝ (PiLp.single 2 k e) S = inner ℝ e (S k) := by
  classical
  simp only [PiLp.inner_apply, PiLp.single_apply]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
  · intro i _ hi
    rw [ite_eq_right hi, inner_zero_left]
  · exact fun hk => (hk (Finset.mem_univ k)).elim

omit [BorelSpace E] [CompleteSpace E] in
/-- Polynomially growing coordinate fields have native plane carriers with a common radial budget. -/
theorem amplitudeId_polynomial_plane_curve
    (μ : Measure ℝ) (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ y, 0 < q y)
    (C : Vec 2 → E →L[ℝ] ℂ) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A * q y)
    (he : (∫⁻ t, Weighted.chartScalarEnergy (fun y => q y ^ 2) (U t) ∂μ) ≠ ⊤) :
    ∃ P : ℝ → PlaneHk Set.univ 0 ℂ, MemLp P 2 μ ∧
      (∀ᵐ t ∂μ, (P t).toFunction.jet (valueIndex2 0) =ᵐ[volume] fun y => C y (U t y)) ∧
      ∃ V : ℝ → Lp ℂ 2 (volume : Measure (Vec 2)), MemLp V 2 μ ∧ ∀ᵐ t ∂μ,
        V t =ᵐ[volume] fun y => (1 + ‖y‖) ^ 4 • (P t).toFunction.jet (valueIndex2 0) y := by
  let D := fun y => (q y)⁻¹ • C y
  have hD : Continuous D := (hq.inv₀ (fun y => (hq0 y).ne')).smul hC
  have hbD (y : Vec 2) : (1 + ‖y‖) ^ 4 * ‖D y‖ ≤ A :=
    amplitudeId_normalized_decay q hq0 C A hb y
  let L := amplitudeId_boundedLpOperator D hD A hA (amplitudeId_decay_coefficient_le D A hbD)
  let W := fun y => (1 + ‖y‖) ^ 4 • D y
  have hW : Continuous W := (by fun_prop : Continuous (fun y : Vec 2 => (1 + ‖y‖) ^ 4)).smul hD
  have hbW (y : Vec 2) : ‖W y‖ ≤ A := by
    simpa only [W, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y‖) ^ 4)] using hbD y
  let LW := amplitudeId_boundedLpOperator W hW A hA hbW
  let f := fun t => Weighted.weightedPlaneLpReadout q hq (U t)
  have hf : MemLp f 2 μ := Weighted.weightedPlaneLpReadout_time_memLp q hq hq0 μ U hU he
  let P := fun t => planeL2ZeroCarrier (L (f t))
  have hP : MemLp P 2 μ := (planeL2ZeroCarrier (E := ℂ)).comp_memLp' (L.comp_memLp' hf)
  have hraw (t : ℝ) : (P t).toFunction.jet (valueIndex2 0) =ᵐ[volume] L (f t) := by
    have h := (Weighted.planeJetReadout_ae_raw (P t) (valueIndex2 0)).symm
    have hv : Weighted.planeJetReadoutOperator 0 (valueIndex2 0) (P t) = L (f t) := by
      change univToPlane (planeToUniv (L (f t))) = _
      exact univToPlane_planeToUniv _
    rw [hv] at h
    exact h
  have hfin : ∀ᵐ t ∂μ, Weighted.chartScalarEnergy (fun y => q y ^ 2) (U t) ≠ ⊤ :=
    (ae_lt_top' (Weighted.chartScalarEnergy_stationary_time_aemeasurable _ (hq.pow 2)
      (fun y => sq_pos_of_pos (hq0 y)) μ U hU) he).mono (fun _ ht => ht.ne)
  refine ⟨P, hP, ?_, fun t => LW (f t), LW.comp_memLp' hf, ?_⟩
  · filter_upwards [hfin] with t ht
    filter_upwards [hraw t,
      amplitudeId_boundedLpOperator_ae D hD A hA (amplitudeId_decay_coefficient_le D A hbD) (f t),
      Weighted.weightedPlaneLpReadout_ae q hq (U t) ht] with y hy hdy hfy
    rw [hy, hdy, hfy]
    simp only [D, smul_apply, map_smul, smul_smul, mul_inv_cancel₀ (hq0 y).ne', one_smul]
  · exact Filter.Eventually.of_forall (fun t => by
      filter_upwards [amplitudeId_boundedLpOperator_ae W hW A hA hbW (f t),
        amplitudeId_boundedLpOperator_ae D hD A hA
          (amplitudeId_decay_coefficient_le D A hbD) (f t), hraw t] with y hwy hdy hpy
      rw [hwy, hpy, hdy]
      rfl)

/-- A literal complex plane curve together with its native radial fourth-moment curve. -/
structure AmplitudeIdPlaneRadialCurve (μ : Measure ℝ) (f : ℝ → Vec 2 → ℂ) where
  value : ℝ → PlaneHk Set.univ 0 ℂ
  mem : MemLp value 2 μ
  readout : ∀ᵐ t ∂μ, (value t).toFunction.jet (valueIndex2 0) =ᵐ[volume] f t
  weighted : ℝ → Lp ℂ 2 (volume : Measure (Vec 2))
  weighted_mem : MemLp weighted 2 μ
  weighted_readout : ∀ᵐ t ∂μ, weighted t =ᵐ[volume]
    fun y => (1 + ‖y‖) ^ 4 • (value t).toFunction.jet (valueIndex2 0) y

/-- Changing a literal field on a product-null set preserves its concrete radial carrier. -/
def AmplitudeIdPlaneRadialCurve.congr {μ : Measure ℝ} {f g : ℝ → Vec 2 → ℂ}
    (P : AmplitudeIdPlaneRadialCurve μ f) (he : ∀ᵐ t ∂μ, f t =ᵐ[volume] g t) :
    AmplitudeIdPlaneRadialCurve μ g := by
  refine { P with readout := ?_ }
  filter_upwards [P.readout, he] with t ht heq
  exact ht.trans heq

/-- The native weighted curve supplies exactly the radial budget consumed by lattice transfer. -/
theorem AmplitudeIdPlaneRadialCurve.budget {μ : Measure ℝ} {f : ℝ → Vec 2 → ℂ}
    (P : AmplitudeIdPlaneRadialCurve μ f) :
    ∃ M : ℝ → ℝ, MemLp M 2 μ ∧ ∀ᵐ t ∂μ,
      AEStronglyMeasurable
        (fun y => (1 + ‖y‖) ^ 4 • (P.value t).toFunction.jet (valueIndex2 0) y) volume ∧
      eLpNorm (fun y => (1 + ‖y‖) ^ 4 • (P.value t).toFunction.jet (valueIndex2 0) y) 2 volume ≤
        ENNReal.ofReal ‖M t‖ := by
  refine ⟨fun t => ‖P.weighted t‖, P.weighted_mem.norm, ?_⟩
  filter_upwards [P.weighted_readout] with t ht
  refine ⟨(Lp.memLp (P.weighted t)).aestronglyMeasurable.congr ht, ?_⟩
  rw [← eLpNorm_congr_ae ht, ← Lp.enorm_def, ← ofReal_norm, norm_norm]

/-- Every polynomial coordinate of a finite-energy native plane curve has a radial carrier. -/
theorem amplitudeId_native_plane_moment_curve {k : ℕ}
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ k E) (hU : MemLp U 2 μ)
    (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (he : ∀ n : ℕ, (∫⁻ t, weightedFactorialNormSq n ϖ 0 r k (U t) ∂μ) ≠ ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (a : JetIndex2 k) :
    Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (momentWeight β y * inner ℝ e ((U t).toFunction.jet a y) : ℝ))) := by
  let n := 2 * (β.1 + β.2 + 4)
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  have hq : Continuous q := (polynomialMomentRoot_continuous ϖ).pow n
  have hq0 (y : Vec 2) : 0 < q y := pow_pos
    (lt_of_lt_of_le zero_lt_one (polynomialMomentRoot_one_le ϖ y)) n
  let f := fun t => Weighted.planeJetReadoutOperator (E := E) k a (U t)
  have hf : MemLp f 2 μ := (Weighted.planeJetReadoutOperator (E := E) k a).comp_memLp' hU
  have hc : (∫⁻ t, Weighted.chartScalarEnergy (fun y => q y ^ 2) (f t) ∂μ) ≠ ⊤ := by
    have h := he n
    simp only [Weighted.weightedFactorialNormSq_stored_readout,
      Weighted.storedChartFactorialEnergy] at h
    have hcomp := Weighted.finite_integrated_weighted_sum_component μ
      (fun a : JetIndex2 k => factorialWeight r a.1.val)
      (fun a => Weighted.factorialWeight_pos_of_radius_pos r hr a.1.val) _ h a
    simpa only [q, polynomialMomentRoot_pow_sq] using hcomp
  let C := amplitudeId_momentCoefficient θ β e
  let A := (2 + (ϖ ^ 2)⁻¹) ^ (β.1 + β.2 + 4) * ‖e‖
  obtain ⟨P, hP, hp, V, hV, hv⟩ := amplitudeId_polynomial_plane_curve μ f hf q hq hq0
    C (amplitudeId_momentCoefficient_contDiff θ β e).continuous A (by dsimp only [A]; positivity)
    (amplitudeId_momentCoefficient_growth θ β e ϖ hϖ) hc
  refine ⟨⟨P, hP, ?_, V, hV, hv⟩⟩
  filter_upwards [hp] with t ht
  filter_upwards [ht, Weighted.planeJetReadout_ae_raw (U t) a] with y hy huy
  rw [hy, huy]
  simp only [C, amplitudeId_momentCoefficient, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, innerSL_apply_apply,
    Complex.ofReal_mul, mul_assoc]

private theorem amplitudeId_zeroCarrier_readout
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    (planeL2ZeroCarrier f).toFunction.jet (valueIndex2 0) =ᵐ[volume] f := by
  have h := (Weighted.planeJetReadout_ae_raw (planeL2ZeroCarrier f) (valueIndex2 0)).symm
  have he : Weighted.planeJetReadoutOperator 0 (valueIndex2 0) (planeL2ZeroCarrier f) = f := by
    change univToPlane (planeToUniv f) = _
    exact univToPlane_planeToUniv _
  rw [he] at h
  exact h

private theorem amplitudeId_plane_time_coefficient_memLp
    (μ : Measure ℝ) (C : ℝ → Vec 2 → ℂ →L[ℝ] ℂ)
    (hc : ∀ t, Continuous (C t)) (hj : Measurable (Function.uncurry C))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ t y, ‖C t y‖ ≤ B)
    (u : ℝ → Lp ℂ 2 (volume : Measure (Vec 2))) (hu : MemLp u 2 μ) :
    MemLp (fun t => CoupledEnergyPlane.planeCoefficientOperator (C t) (hc t) hB (hb t) (u t)) 2 μ := by
  let amplitudeIdCoefficientFactFinite : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let amplitudeIdCoefficientFactOne : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let amplitudeIdCoefficientSecondCountable :
      SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  borelize ↥(Lp ℂ 2 (volume : Measure (Vec 2)))
  exact CoupledEnergy.Variational.memLp_operator_action
    (fun t => CoupledEnergyPlane.planeCoefficientOperator (C t) (hc t) hB (hb t))
    (fun x => CoupledEnergyPlane.planeCoefficientOperator_stronglyMeasurable C hc hj hB hb x)
    hu hB (fun t => CoupledEnergyPlane.planeCoefficientOperator_norm_le (C t) (hc t) hB (hb t))

/-- A finite bounded coefficient combination preserves the actual radial moment carriers. -/
theorem amplitudeId_plane_radial_combination {J : Type*} [Fintype J]
    (μ : Measure ℝ) (f : J → ℝ → Vec 2 → ℂ)
    (P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j))
    (C : J → ℝ → Vec 2 → ℂ →L[ℝ] ℂ)
    (hc : ∀ j t, Continuous (C j t))
    (hj : ∀ j, Measurable (Function.uncurry (C j)))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j t y, ‖C j t y‖ ≤ B j) :
    Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y => ∑ j, C j t y (f j t y))) := by
  classical
  let L := fun j t => CoupledEnergyPlane.planeCoefficientOperator (C j t) (hc j t) (hB j) (hb j t)
  let U : J → ℝ → Lp ℂ 2 (volume : Measure (Vec 2)) := fun j t =>
    Weighted.planeJetReadoutOperator (E := ℂ) 0 (valueIndex2 0) ((P j).value t)
  have hU (j : J) : MemLp (U j) 2 μ :=
    (Weighted.planeJetReadoutOperator (E := ℂ) 0 (valueIndex2 0)).comp_memLp' (P j).mem
  let V := fun t => ∑ j, L j t (U j t)
  let W := fun t => ∑ j, L j t ((P j).weighted t)
  have hV : MemLp V 2 μ := memLp_finsetSum Finset.univ (fun j _ =>
    amplitudeId_plane_time_coefficient_memLp μ (C j) (hc j) (hj j) (B j) (hB j) (hb j) (U j) (hU j))
  have hW : MemLp W 2 μ := memLp_finsetSum Finset.univ (fun j _ =>
    amplitudeId_plane_time_coefficient_memLp μ (C j) (hc j) (hj j) (B j) (hB j) (hb j)
      (P j).weighted (P j).weighted_mem)
  let Q : ℝ → PlaneHk Set.univ 0 ℂ := fun t => planeL2ZeroCarrier (V t)
  have hQ : MemLp Q 2 μ := (planeL2ZeroCarrier (E := ℂ)).comp_memLp' hV
  have hVraw (t : ℝ) : V t =ᵐ[volume]
      fun y => ∑ j, C j t y ((P j).value t |>.toFunction.jet (valueIndex2 0) y) := by
    have hterm (j : J) : L j t (U j t) =ᵐ[volume]
        fun y => C j t y ((P j).value t |>.toFunction.jet (valueIndex2 0) y) := by
      filter_upwards [CoupledEnergyPlane.planeCoefficientOperator_ae (C j t) (hc j t)
        (hB j) (hb j t) (U j t),
        Weighted.planeJetReadout_ae_raw ((P j).value t) (valueIndex2 0)] with y hy hz
      rw [hy, hz]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => L j t (U j t)), ae_all_iff.mpr hterm] with y hy hz
    rw [hy, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hz j)
  refine ⟨⟨Q, hQ, ?_, W, hW, ?_⟩⟩
  · filter_upwards [ae_all_iff.mpr (fun j => (P j).readout)] with t ht
    filter_upwards [amplitudeId_zeroCarrier_readout (V t), hVraw t, ae_all_iff.mpr ht]
      with y hy hz hfy
    rw [hy, hz]
    exact Finset.sum_congr rfl (fun j _ => congrArg (C j t y) (hfy j))
  · filter_upwards [ae_all_iff.mpr (fun j => (P j).weighted_readout)] with t ht
    have hw (j : J) : L j t ((P j).weighted t) =ᵐ[volume]
        fun y => (1 + ‖y‖) ^ 4 • C j t y ((P j).value t |>.toFunction.jet (valueIndex2 0) y) := by
      filter_upwards [CoupledEnergyPlane.planeCoefficientOperator_ae (C j t) (hc j t)
        (hB j) (hb j t) ((P j).weighted t), ht j] with y hy hz
      rw [hy, hz, map_smul]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => L j t ((P j).weighted t)),
      ae_all_iff.mpr hw, amplitudeId_zeroCarrier_readout (V t), hVraw t] with y hy hz hqy hvy
    rw [hy, hqy, hvy, Finset.smul_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hz j)

/-- Bounded real coefficients combine literal phase-weighted moments on the plane. -/
theorem amplitudeId_plane_moment_combination {J : Type*} [Fintype J]
    (μ : Measure ℝ) (θ : Vec 2) (f : J → ℝ → Vec 2 → ℝ)
    (P : ∀ j β, AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y * f j t y : ℝ)))
    (γ : J → ℕ × ℕ) (c : J → ℝ → Vec 2 → ℝ)
    (hc : ∀ j t, Continuous (c j t)) (hj : ∀ j, Measurable (Function.uncurry (c j)))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j t y, |c j t y| ≤ B j) :
    Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (∑ j, c j t y * momentWeight (γ j) y * f j t y : ℝ))) := by
  let C := fun j t y => c j t y • ContinuousLinearMap.id ℝ ℂ
  have hC (j : J) (t : ℝ) : Continuous (C j t) := (hc j t).smul continuous_const
  have hjC (j : J) : Measurable (Function.uncurry (C j)) :=
    (hj j).smul measurable_const
  have hbC (j : J) (t : ℝ) (y : Vec 2) : ‖C j t y‖ ≤ B j := by
    change ‖c j t y • ContinuousLinearMap.id ℝ ℂ‖ ≤ B j
    rw [norm_smul, Real.norm_eq_abs]
    have hid : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact (mul_le_mul_of_nonneg_left hid (abs_nonneg _)).trans
      (by simpa only [mul_one] using hb j t y)
  obtain ⟨Q⟩ := amplitudeId_plane_radial_combination μ _ (fun j => P j (γ j)) C hC hjC B hB hbC
  refine ⟨{ Q with readout := ?_ }⟩
  filter_upwards [Q.readout] with t ht
  filter_upwards [ht] with y hy
  rw [hy]
  simp only [C, smul_apply, ContinuousLinearMap.id_apply, Complex.real_smul,
    Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- The two polynomial product commutators have native radial plane time carriers. -/
theorem amplitudeId_plane_moment_forcing (μ : Measure ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, Continuous (v t))
    (θ : Vec 2) (β : ℕ × ℕ) (u : ℝ → Vec 2 → ℝ) (S : Fin 2 → ℝ → Vec 2 → ℝ)
    (Mu : ∀ γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * u t y : ℝ)))
    (MS : ∀ i γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * S i t y : ℝ))) :
    Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeightLap (G t) β y + ∑ i, v t y i * momentWeightGrad β y i) * u t y -
          ∑ i, momentWeightGrad β y i * S i t y : ℝ))) ∧
    ∀ k : Fin 2, Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (momentWeight β y * S k t y -
          (∑ i, (G t k i + G t i k) * momentWeightGrad β y i) * u t y : ℝ))) := by
  classical
  obtain ⟨V, hV⟩ := hv.2.1
  let a := fun i : Fin 2 => (amplitudeId_momentMultiplicity β i : ℝ)
  let b := fun i k : Fin 2 =>
    (amplitudeId_momentMultiplicity (amplitudeId_lowerMoment β i) k : ℝ)
  have ha (i : Fin 2) : 0 ≤ a i := Nat.cast_nonneg _
  have hb (i k : Fin 2) : 0 ≤ b i k := Nat.cast_nonneg _
  have hgm (i k : Fin 2) : Measurable (fun p : ℝ × Vec 2 => G p.1 i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hG.1)
  have hvm (i : Fin 2) : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2 i) :=
    (measurable_pi_apply i).comp hv.1
  constructor
  · let J := (Fin 2 × Fin 2) ⊕ (Fin 2 ⊕ Fin 2)
    let f : J → ℝ → Vec 2 → ℝ := Sum.elim (fun _ => u) (Sum.elim (fun _ => u) S)
    let M : ∀ j γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
        Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * f j t y : ℝ)) :=
      Sum.rec (fun _ => Mu) (Sum.rec (fun _ => Mu) MS)
    let γ : J → ℕ × ℕ := Sum.elim
      (fun p => amplitudeId_lowerMoment (amplitudeId_lowerMoment β p.1) p.2)
      (Sum.elim (amplitudeId_lowerMoment β) (amplitudeId_lowerMoment β))
    let c : J → ℝ → Vec 2 → ℝ := Sum.elim
      (fun p t _ => G t p.1 p.2 * a p.1 * b p.1 p.2)
      (Sum.elim (fun i t y => v t y i * a i) (fun i _ _ => -(a i)))
    let B : J → ℝ := Sum.elim (fun p => 2 * a p.1 * b p.1 p.2)
      (Sum.elim (fun i => |V| * a i) a)
    have hc (j : J) : Measurable (Function.uncurry (c j)) := by
      rcases j with p | (i | i)
      · exact ((hgm p.1 p.2).mul_const _).mul_const _
      · exact (hvm i).mul_const _
      · exact measurable_const
    have hcont (j : J) (t : ℝ) : Continuous (c j t) := by
      rcases j with p | (i | i)
      · exact continuous_const
      · exact ((continuous_apply i).comp (hvs t)).mul_const _
      · exact continuous_const
    have hB (j : J) : 0 ≤ B j := by
      rcases j with p | (i | i)
      · exact mul_nonneg (mul_nonneg (by norm_num) (ha _)) (hb _ _)
      · exact mul_nonneg (abs_nonneg _) (ha _)
      · exact ha _
    have hbound (j : J) (t : ℝ) (y : Vec 2) : |c j t y| ≤ B j := by
      rcases j with p | (i | i)
      · change |G t p.1 p.2 * a p.1 * b p.1 p.2| ≤ _
        rw [abs_mul, abs_mul, abs_of_nonneg (ha _), abs_of_nonneg (hb _ _)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (CycleEvolution.cellMetric_entry_bound hG t y p.1 p.2)
            (ha _)) (hb _ _)
      · change |v t y i * a i| ≤ _
        rw [abs_mul, abs_of_nonneg (ha _)]
        exact mul_le_mul_of_nonneg_right (CycleEvolution.cellDrift_entry_bound hV t y i) (ha _)
      · change |-(a i)| ≤ a i
        rw [abs_neg, abs_of_nonneg (ha _)]
    obtain ⟨R⟩ := amplitudeId_plane_moment_combination μ θ f M γ c hcont hc B hB hbound
    refine ⟨{ R with readout := ?_ }⟩
    filter_upwards [R.readout] with t ht
    have he (y : Vec 2) : (∑ j, c j t y * momentWeight (γ j) y * f j t y) =
        (momentWeightLap (G t) β y + ∑ i, v t y i * momentWeightGrad β y i) * u t y -
          ∑ i, momentWeightGrad β y i * S i t y := by
      dsimp only [J]
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, c, γ, f, Sum.elim_inl,
        Sum.elim_inr, amplitudeId_momentWeightLap_lower, amplitudeId_momentWeightGrad_lower]
      simp only [Fin.sum_univ_two, a, b]
      ring
    simpa only [he] using ht
  · intro k
    let J := Unit ⊕ Fin 2
    let f : J → ℝ → Vec 2 → ℝ := Sum.elim (fun _ => S k) (fun _ => u)
    let M : ∀ j γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
        Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * f j t y : ℝ)) := Sum.rec (fun _ => MS k) (fun _ => Mu)
    let γ : J → ℕ × ℕ := Sum.elim (fun _ => β) (amplitudeId_lowerMoment β)
    let c : J → ℝ → Vec 2 → ℝ := Sum.elim (fun _ _ _ => 1)
      (fun i t _ => -((G t k i + G t i k) * a i))
    let B : J → ℝ := Sum.elim (fun _ => 1) (fun i => (2 + 2) * a i)
    have hc (j : J) : Measurable (Function.uncurry (c j)) := by
      rcases j with _ | i
      · exact measurable_const
      · exact (((hgm k i).add (hgm i k)).mul_const _).neg
    have hcont (j : J) (t : ℝ) : Continuous (c j t) := by
      cases j <;> exact continuous_const
    have hB (j : J) : 0 ≤ B j := by
      rcases j with _ | i
      · exact zero_le_one
      · exact mul_nonneg (by norm_num) (ha i)
    have hbound (j : J) (t : ℝ) (y : Vec 2) : |c j t y| ≤ B j := by
      rcases j with _ | i
      · change |(1 : ℝ)| ≤ 1
        rw [abs_one]
      · change |-((G t k i + G t i k) * a i)| ≤ _
        rw [abs_neg, abs_mul, abs_of_nonneg (ha i)]
        exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add
          (CycleEvolution.cellMetric_entry_bound hG t y k i)
          (CycleEvolution.cellMetric_entry_bound hG t y i k))) (ha i)
    obtain ⟨R⟩ := amplitudeId_plane_moment_combination μ θ f M γ c hcont hc B hB hbound
    refine ⟨{ R with readout := ?_ }⟩
    filter_upwards [R.readout] with t ht
    have he (y : Vec 2) : (∑ j, c j t y * momentWeight (γ j) y * f j t y) =
        momentWeight β y * S k t y -
          (∑ i, (G t k i + G t i k) * momentWeightGrad β y i) * u t y := by
      dsimp only [J]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, c, γ, f, Sum.elim_inl,
        Sum.elim_inr, one_mul, amplitudeId_momentWeightGrad_lower]
      simp only [Fin.sum_univ_two, a]
      ring
    simpa only [he] using ht

/-- The covariant moment gradient has its own radial native time carrier. -/
theorem amplitudeId_plane_moment_gradient (μ : Measure ℝ) (θ : Vec 2) (β : ℕ × ℕ)
    (u : ℝ → Vec 2 → ℝ) (du : Fin 2 → ℝ → Vec 2 → ℝ)
    (Mu : ∀ γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * u t y : ℝ)))
    (Mdu : ∀ i γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * du i t y : ℝ))) :
    ∀ i : Fin 2, Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (momentWeight β y * du i t y + momentWeightGrad β y i * u t y : ℝ))) := by
  intro i
  let f : Fin 2 → ℝ → Vec 2 → ℝ := fun j => if j = 0 then du i else u
  let M : ∀ j γ, AmplitudeIdPlaneRadialCurve μ (fun t y =>
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight γ y * f j t y : ℝ)) :=
    fun j => by
      classical
      by_cases hj : j = 0
      · dsimp only [f]
        rw [ite_eq_left hj]
        exact Mdu i
      · dsimp only [f]
        rw [ite_eq_right hj]
        exact Mu
  let γ : Fin 2 → ℕ × ℕ := fun j => if j = 0 then β else amplitudeId_lowerMoment β i
  let c : Fin 2 → ℝ → Vec 2 → ℝ :=
    fun j _ _ => if j = 0 then 1 else (amplitudeId_momentMultiplicity β i : ℝ)
  let B : Fin 2 → ℝ := fun j => |c j 0 0|
  have hc (j : Fin 2) (t : ℝ) : Continuous (c j t) := continuous_const
  have hj (j : Fin 2) : Measurable (Function.uncurry (c j)) := measurable_const
  obtain ⟨P⟩ := amplitudeId_plane_moment_combination μ θ f M γ c hc hj B
    (fun _ => abs_nonneg _) (fun _ _ _ => le_rfl)
  refine ⟨P.congr (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun y => ?_)))⟩
  simp only [Fin.sum_univ_two, c, γ, f, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, one_mul,
    amplitudeId_momentWeightGrad_lower]

/-- Complex bounded scalar coefficients preserve native radial time curves. -/
theorem amplitudeId_plane_complex_combination {J : Type*} [Fintype J]
    (μ : Measure ℝ) (f : J → ℝ → Vec 2 → ℂ)
    (P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j))
    (c : J → ℝ → Vec 2 → ℂ) (hc : ∀ j t, Continuous (c j t))
    (hj : ∀ j, Measurable (Function.uncurry (c j)))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j t y, ‖c j t y‖ ≤ B j) :
    Nonempty (AmplitudeIdPlaneRadialCurve μ (fun t y => ∑ j, c j t y * f j t y)) := by
  let C := fun j t y => c j t y • ContinuousLinearMap.id ℝ ℂ
  have hC (j : J) (t : ℝ) : Continuous (C j t) := (hc j t).smul continuous_const
  have hjC (j : J) : Measurable (Function.uncurry (C j)) := (hj j).smul measurable_const
  have hbC (j : J) (t : ℝ) (y : Vec 2) : ‖C j t y‖ ≤ B j := by
    change ‖c j t y • ContinuousLinearMap.id ℝ ℂ‖ ≤ B j
    rw [norm_smul]
    have hid : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact (mul_le_mul_of_nonneg_left hid (norm_nonneg _)).trans
      (by simpa only [mul_one] using hb j t y)
  obtain ⟨Q⟩ := amplitudeId_plane_radial_combination μ f P C hC hjC B hB hbC
  refine ⟨{ Q with readout := ?_ }⟩
  simpa only [C, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using Q.readout

/-- The flux of the ordinary balance associated with a covariant forced equation. -/
def amplitudeId_covariantFlux (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin 2 → ℝ → Vec 2 → ℂ) (i : Fin 2) (t : ℝ) (y : Vec 2) : ℂ :=
  F i t y + ∑ k : Fin 2, (G t k i : ℂ) * B k t y

/-- The scalar source after moving the fixed frequency shift into the ordinary balance. -/
def amplitudeId_covariantSource (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (θ : Vec 2) (B F : Fin 2 → ℝ → Vec 2 → ℂ)
    (R : ℝ → Vec 2 → ℂ) (t : ℝ) (y : Vec 2) : ℂ :=
  R t y + ∑ i : Fin 2, -(v t y i : ℂ) * B i t y +
    ∑ i : Fin 2, (Complex.I * (θ i : ℂ)) * amplitudeId_covariantFlux G B F i t y

/-- The ordinary balance flux and source retain the common radial moment budget. -/
theorem amplitudeId_covariant_balance_carriers (μ : Measure ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, Continuous (v t))
    (θ : Vec 2) (B F : Fin 2 → ℝ → Vec 2 → ℂ) (R : ℝ → Vec 2 → ℂ)
    (PB : ∀ i, AmplitudeIdPlaneRadialCurve μ (B i))
    (PF : ∀ i, AmplitudeIdPlaneRadialCurve μ (F i))
    (PR : AmplitudeIdPlaneRadialCurve μ R) :
    (∀ i, Nonempty (AmplitudeIdPlaneRadialCurve μ (amplitudeId_covariantFlux G B F i))) ∧
      Nonempty (AmplitudeIdPlaneRadialCurve μ (amplitudeId_covariantSource G v θ B F R)) := by
  classical
  have hgm (k i : Fin 2) : Measurable (fun p : ℝ × Vec 2 => (G p.1 k i : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp hG.1))
  have hQ (i : Fin 2) : Nonempty (AmplitudeIdPlaneRadialCurve μ (amplitudeId_covariantFlux G B F i)) := by
    let f : Unit ⊕ Fin 2 → ℝ → Vec 2 → ℂ := Sum.elim (fun _ => F i) B
    let P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j) := Sum.rec (fun _ => PF i) PB
    let c : Unit ⊕ Fin 2 → ℝ → Vec 2 → ℂ :=
      Sum.elim (fun _ _ _ => 1) (fun k t _ => (G t k i : ℂ))
    let b : Unit ⊕ Fin 2 → ℝ := Sum.elim (fun _ => 1) (fun _ => 2)
    have hc (j : Unit ⊕ Fin 2) (t : ℝ) : Continuous (c j t) := by
      cases j <;> exact continuous_const
    have hj (j : Unit ⊕ Fin 2) : Measurable (Function.uncurry (c j)) := by
      cases j with
      | inl _ => exact measurable_const
      | inr k => exact hgm k i
    have hb (j : Unit ⊕ Fin 2) (t : ℝ) (y : Vec 2) : ‖c j t y‖ ≤ b j := by
      cases j with
      | inl _ => change ‖(1 : ℂ)‖ ≤ 1; rw [norm_one]
      | inr k =>
        simpa only [c, b, Sum.elim_inr, Complex.norm_real, Real.norm_eq_abs] using
          CycleEvolution.cellMetric_entry_bound hG t y k i
    obtain ⟨Q⟩ := amplitudeId_plane_complex_combination μ f P c hc hj b
      (fun j => by cases j <;> norm_num [b]) hb
    refine ⟨Q.congr (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun y => ?_)))⟩
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, c, f, Sum.elim_inl, Sum.elim_inr,
      one_mul, amplitudeId_covariantFlux]
  refine ⟨hQ, ?_⟩
  let Q := fun i => Classical.choice (hQ i)
  obtain ⟨V, hV⟩ := hv.2.1
  let f : Unit ⊕ (Fin 2 ⊕ Fin 2) → ℝ → Vec 2 → ℂ :=
    Sum.elim (fun _ => R) (Sum.elim B (amplitudeId_covariantFlux G B F))
  let P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j) :=
    Sum.rec (fun _ => PR) (Sum.rec PB Q)
  let c : Unit ⊕ (Fin 2 ⊕ Fin 2) → ℝ → Vec 2 → ℂ :=
    Sum.elim (fun _ _ _ => 1) (Sum.elim (fun i t y => -(v t y i : ℂ))
      (fun i _ _ => Complex.I * (θ i : ℂ)))
  let b : Unit ⊕ (Fin 2 ⊕ Fin 2) → ℝ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => |V|) (fun i => ‖Complex.I * (θ i : ℂ)‖))
  have hc (j : Unit ⊕ (Fin 2 ⊕ Fin 2)) (t : ℝ) : Continuous (c j t) := by
    rcases j with _ | (i | i)
    · exact continuous_const
    · exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp (hvs t))).neg
    · exact continuous_const
  have hj (j : Unit ⊕ (Fin 2 ⊕ Fin 2)) : Measurable (Function.uncurry (c j)) := by
    rcases j with _ | (i | i)
    · exact measurable_const
    · exact (Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply i).comp hv.1)).neg
    · exact measurable_const
  have hb (j : Unit ⊕ (Fin 2 ⊕ Fin 2)) (t : ℝ) (y : Vec 2) : ‖c j t y‖ ≤ b j := by
    rcases j with _ | (i | i)
    · change ‖(1 : ℂ)‖ ≤ 1; rw [norm_one]
    · simpa only [c, b, Sum.elim_inl, Sum.elim_inr, norm_neg, Complex.norm_real, Real.norm_eq_abs] using
        CycleEvolution.cellDrift_entry_bound hV t y i
    · exact le_rfl
  obtain ⟨H⟩ := amplitudeId_plane_complex_combination μ f P c hc hj b
    (fun j => by rcases j with _ | (i | i); exact zero_le_one; exact abs_nonneg _; exact norm_nonneg _) hb
  refine ⟨H.congr (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun y => ?_)))⟩
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, c, f, Sum.elim_inl, Sum.elim_inr,
    one_mul, amplitudeId_covariantSource, add_assoc]

/-- Every literal fourth-moment L2 field has an actual native order-zero plane carrier. -/
theorem amplitudeId_radial_plane_carrier (f : Vec 2 → ℂ)
    (hf : MemLp (fun y => (1 + ‖y‖) ^ 4 • f y) 2 volume) :
    ∃ P : PlaneHk Set.univ 0 ℂ, P.toFunction.jet (valueIndex2 0) =ᵐ[volume] f ∧
      MemLp (fun y => (1 + ‖y‖) ^ 4 • P.toFunction.jet (valueIndex2 0) y) 2 volume := by
  have hw : Continuous (fun y : Vec 2 => ((1 + ‖y‖) ^ 4)⁻¹) :=
    ((continuous_const.add continuous_norm).pow 4).inv₀ (fun y => pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg y)))))
  have hmeas : AEStronglyMeasurable f volume := by
    apply (hw.aestronglyMeasurable.smul hf.aestronglyMeasurable).congr
    exact Filter.Eventually.of_forall (fun y => by
      change ((1 + ‖y‖) ^ 4)⁻¹ • ((1 + ‖y‖) ^ 4 • f y) = f y
      rw [smul_smul, inv_mul_cancel₀ (by positivity : (1 + ‖y‖) ^ 4 ≠ 0), one_smul])
  have h0 : MemLp f 2 volume := hf.of_le hmeas (Filter.Eventually.of_forall (fun y => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y‖) ^ 4)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))))
  let P := planeL2ZeroCarrier (h0.toLp f)
  have hp : P.toFunction.jet (valueIndex2 0) =ᵐ[volume] f :=
    (amplitudeId_zeroCarrier_readout (h0.toLp f)).trans h0.coeFn_toLp
  refine ⟨P, hp, hf.ae_eq ?_⟩
  exact hp.mono (fun y hy => congrArg (fun z : ℂ => (1 + ‖y‖) ^ 4 • z) hy.symm)

universe u v
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The actual word value and each actual preceding flux supply native moment families. -/
theorem amplitudeId_word_moment_families
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (θ : Vec 2) (e : h x) :
    Nonempty (AmplitudeIdMomentCellFamily (Icc F.a F.b) θ
      (fun t y => inner ℝ e (planeValue (F.u j x t) y))) ∧
    ∀ k : Fin 2, Nonempty (AmplitudeIdMomentCellFamily (Icc F.a F.b) θ
      (fun t y => inner ℝ e (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
        (fun p => F.w p.1 p.2 t) (j, x) t y k))) := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨r, hr, he⟩ := amplitudeId_full_polynomial_budgets F
  obtain ⟨rS, hrS, hS⟩ := amplitudeId_flux_moments F
  obtain ⟨V, hV, hVe, hVr⟩ := hS j x
  constructor
  · let M := amplitudeId_native_moment_family (Icc F.a F.b) (F.w j x)
      (F.solution.2.1 (j, x)) F.ϖ r hϖ hr (fun n => (he n j x).2) θ e
    apply Nonempty.intro (M.congr ?_)
    filter_upwards [F.solution.2.2.1 (j, x)] with t ht
    have hv : planeValue (F.w j x t) = planeValue (F.u j x t) := by
      calc
        _ = planeValue (truncatePlaneHk (Nat.le_succ (F.κ j x)) (F.w j x t)) :=
          (planeJetOrder_truncate (Nat.le_succ (F.κ j x)) (Nat.zero_le _) (F.w j x t) _).symm
        _ = _ := congrArg planeValue ht
    exact Filter.Eventually.of_forall (fun y => congrArg (fun z => inner ℝ e (z y)) hv)
  · intro k
    let M := amplitudeId_native_moment_family (Icc F.a F.b) V hV
      F.ϖ rS hϖ hrS hVe θ (PiLp.single 2 k e)
    apply Nonempty.intro (M.congr ?_)
    filter_upwards [hVr] with t ht
    filter_upwards [ht] with y hy
    rw [amplitudeId_flux_inner_single, hy]

open AVRegularity.Weighted

/-- The actual real L2 coordinate of the word trace. -/
def amplitudeId_wordCoordinateTrace
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (t : ℝ) : Lp ℝ 2 (volume : Measure (Vec 2)) :=
  planeFiberCoordinateCLM e (CoupledEnergyPlane.Fourier.planeHkValueOperator (F.κ j x) (F.u j x t))

/-- The actual real H1 coordinate of the word energy lift. -/
def amplitudeId_wordCoordinateSlice
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (t : ℝ) : PlaneHk Set.univ 1 ℝ :=
  CoupledEnergyPlane.mapPlaneHk (InnerProductSpace.toDual ℝ (h x) e)
    (truncatePlaneHk (by omega) (F.w j x t))

/-- Native real coordinates preserve the literal value at every time and every stored H1 jet. -/
theorem amplitudeId_wordCoordinate_readouts
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (t : ℝ) :
    (amplitudeId_wordCoordinateTrace F j x e t =ᵐ[volume]
      fun y => inner ℝ e (planeValue (F.u j x t) y)) ∧
    ∀ a : JetIndex2 1, (amplitudeId_wordCoordinateSlice F j x e t).toFunction.jet a =ᵐ[volume]
      fun y => inner ℝ e (planeJetOrder (F.w j x t) a.1.val a.2 y) := by
  constructor
  · have hc := (InnerProductSpace.toDual ℝ (h x) e).coeFn_compLpL
      (CoupledEnergyPlane.Fourier.planeHkValueOperator (F.κ j x) (F.u j x t))
    filter_upwards [hc, univToPlane_ae ((F.u j x t).val (valueIndex2 (F.κ j x)))] with y hcy hvy
    change amplitudeId_wordCoordinateTrace F j x e t y = inner ℝ e
      (CoupledEnergyPlane.Fourier.planeHkValueOperator (F.κ j x) (F.u j x t) y) at hcy
    rw [hcy]
    apply congrArg (inner ℝ e)
    rw [planeValue_eq_stored]
    exact hvy
  · intro a
    have hc := planeHkMapRawReadout (InnerProductSpace.toDual ℝ (h x) e)
      (truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t)) a
    have ha : a.1.val ≤ 1 := Nat.le_of_lt_succ a.1.isLt
    have ht := planeJetOrder_truncate (show 1 ≤ F.κ j x + 1 by omega) ha (F.w j x t) a.2
    rw [planeJetOrder_eq_stored ha] at ht
    filter_upwards [hc] with y hcy
    exact hcy.trans (congrArg (inner ℝ e) (congrFun ht y))

/-- A polynomially controlled native preceding flux gives the actual forced coordinate curve. -/
theorem amplitudeId_word_native_coordinate
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) :
    ∃ rS : ℝ, 0 < rS ∧
    ∃ V : ℝ → PlaneHk Set.univ (F.κ j x) (PiLp 2 (fun _ : Fin 2 => h x)),
      MemLp V 2 (volume.restrict (Icc F.a F.b)) ∧
      (∀ n, (∫⁻ t in Icc F.a F.b, weightedFactorialNormSq n F.ϖ 0 rS (F.κ j x) (V t)) ≠ ⊤) ∧
      (∀ᵐ t ∂volume.restrict (Icc F.a F.b), planeValue (V t) =ᵐ[volume]
        fun y => wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
          (fun p => F.w p.1 p.2 t) (j, x) t y) ∧
      ∃ (C : ℝ) (_ : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol F.v t i z‖ ≤ C),
      PlaneWeakHilbertCurve F.a F.b (amplitudeId_wordCoordinateTrace F j x e)
        (amplitudeId_wordCoordinateSlice F j x e) (fun t =>
          planeRealBlochGeneratorDual (F.G t) F.v F.piece.hv t C (hC t)
            (amplitudeId_wordCoordinateSlice F j x e t) +
          planeSourceDual 0 (planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t)))) := by
  obtain ⟨rS, hrS, hS⟩ := amplitudeId_flux_moments F
  obtain ⟨V, hV, he, hv⟩ := hS j x
  obtain ⟨C, hCpos, hC⟩ := cellDriftTorusSymbol_bound F.v F.piece.hv
  refine ⟨rS, hrS, V, hV, he, hv, C, hCpos, hC, ?_⟩
  apply wordChainCoordinateNative_weakCurve F.piece.hD F.G F.piece.hGm F.letters
    F.X₀ (F.ϖ * F.ηg) F.κ F.a F.b F.ordered F.v F.piece.hv C hCpos hC
    (fun p => wordLevelDatum F.κ F.f p.1 p.2) (fun p => F.u p.1 p.2)
    (fun p => F.w p.1 p.2) F.solution (j, x)
    (fun t => planeFluxValueOperator (F.κ j x) (V t))
    (planeFluxValueOperator_memLp _ V hV) ?_ e
  filter_upwards [hv] with t ht
  intro k
  exact (planeFluxValueOperator_ae (F.κ j x) (V t) k).trans
    (ht.mono (fun y hy => congrArg (fun z : PiLp 2 (fun _ : Fin 2 => h x) => z k) hy))

/-- The native coordinate state and flux retain every phase-moment radial time budget. -/
theorem amplitudeId_wordCoordinate_plane_families
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2)
    (rS : ℝ) (hrS : 0 < rS)
    (V : ℝ → PlaneHk Set.univ (F.κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hV : MemLp V 2 (volume.restrict (Icc F.a F.b)))
    (heV : ∀ n, (∫⁻ t in Icc F.a F.b,
      weightedFactorialNormSq n F.ϖ 0 rS (F.κ j x) (V t)) ≠ ⊤) :
    (∀ (a : JetIndex2 1) (γ : ℕ × ℕ), Nonempty (AmplitudeIdPlaneRadialCurve
      (volume.restrict (Icc F.a F.b)) (fun t y =>
        Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          (momentWeight γ y * (amplitudeId_wordCoordinateSlice F j x e t).toFunction.jet a y : ℝ)))) ∧
    (∀ (i : Fin 2) (γ : ℕ × ℕ), Nonempty (AmplitudeIdPlaneRadialCurve
      (volume.restrict (Icc F.a F.b)) (fun t y =>
        Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          (momentWeight γ y * planeFluxFiberCoordinateCLM e
            (planeFluxValueOperator (F.κ j x) (V t)) i y : ℝ)))) := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨r, hr, he⟩ := amplitudeId_full_polynomial_budgets F
  constructor
  · intro a γ
    let α : JetIndex2 (F.κ j x + 1) := ⟨⟨a.1.val, by omega⟩, a.2⟩
    obtain ⟨P⟩ := amplitudeId_native_plane_moment_curve (volume.restrict (Icc F.a F.b))
      (F.w j x) (F.solution.2.1 (j, x)) F.ϖ r hϖ hr (fun n => (he n j x).2) θ γ e α
    refine ⟨P.congr (Filter.Eventually.of_forall (fun t => ?_))⟩
    filter_upwards [(amplitudeId_wordCoordinate_readouts F j x e t).2 a] with y hy
    have hraw : planeJetOrder (F.w j x t) a.1.val a.2 y = (F.w j x t).toFunction.jet α y := by
      rw [planeJetOrder_eq_stored (show a.1.val ≤ F.κ j x + 1 by omega)]
    rw [hy, hraw]
  · intro i γ
    obtain ⟨P⟩ := amplitudeId_native_plane_moment_curve (volume.restrict (Icc F.a F.b))
      V hV F.ϖ rS hϖ hrS heV θ γ (PiLp.single 2 i e) (valueIndex2 (F.κ j x))
    refine ⟨P.congr (Filter.Eventually.of_forall (fun t => ?_))⟩
    filter_upwards [planeFluxValueOperator_ae (F.κ j x) (V t) i,
      planeFluxFiberCoordinateCLM_ae e (planeFluxValueOperator (F.κ j x) (V t)) i] with y hv hc
    rw [amplitudeId_flux_inner_single, hc, hv]

/-- The literal scalar moment commutator of the given word. -/
def amplitudeId_wordMomentScalar
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (t : ℝ) (y : Vec 2) : ℝ :=
  (momentWeightLap (F.G t) β y + ∑ i, F.v t y i * momentWeightGrad β y i) *
    inner ℝ e (planeValue (F.u j x t) y) -
  ∑ i, momentWeightGrad β y i * inner ℝ e
    (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun p => F.w p.1 p.2 t) (j, x) t y i)

/-- The literal divergence moment commutator of the given word. -/
def amplitudeId_wordMomentFlux
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (i : Fin 2) (t : ℝ) (y : Vec 2) : ℝ :=
  momentWeight β y * inner ℝ e
    (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun p => F.w p.1 p.2 t) (j, x) t y i) -
  (∑ k, (F.G t i k + F.G t k i) * momentWeightGrad β y k) *
    inner ℝ e (planeValue (F.u j x t) y)

/-- Native cell trace, energy state and literal forcing produced by the given word. -/
structure AmplitudeIdWordCellData
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ) where
  value : ℝ → CycleEvolution.ComplexCellL2
  continuous : ContinuousOn value (Icc F.a F.b)
  trace : ∀ t ∈ Icc F.a F.b, value t =ᵐ[volume.restrict AVenhance.unitCube]
    planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y))
  radius : ℝ
  radius_pos : 0 < radius
  plane_mem : MemLp (fun t => truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t))
    2 (volume.restrict (Icc F.a F.b))
  plane_energy : ∀ n, (∫⁻ t in Icc F.a F.b, weightedFactorialNormSq n F.ϖ 0 radius 1
    (truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t))) ≠ ⊤
  state : ℝ → TorusHk 1 ℂ
  state_mem : MemLp state 2 (volume.restrict (Icc F.a F.b))
  state_readout : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), ∀ a, (state t).val a =ᵐ[volume.restrict AVenhance.unitCube]
    CycleJointProofs.periodizeRawJet (multiplicationRawJet (amplitudeId_momentCoefficient θ β e)
      (truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t)).toFunction.jet) a
  scalar : ℝ → CycleEvolution.ComplexCellL2
  scalar_mem : MemLp scalar 2 (volume.restrict (Icc F.a F.b))
  scalar_readout : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), scalar t =ᵐ[volume.restrict AVenhance.unitCube]
    planeBlochC θ (amplitudeId_wordMomentScalar F j x e β t)
  flux : Fin 2 → ℝ → CycleEvolution.ComplexCellL2
  flux_mem : ∀ i, MemLp (flux i) 2 (volume.restrict (Icc F.a F.b))
  flux_readout : ∀ i, ∀ᵐ t ∂volume.restrict (Icc F.a F.b), flux i t =ᵐ[volume.restrict AVenhance.unitCube]
    planeBlochC θ (amplitudeId_wordMomentFlux F j x e β i t)

/-- All spatial and temporal cell carriers are supplied unconditionally by the word budgets. -/
theorem amplitudeId_word_cell_data
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ) :
    Nonempty (AmplitudeIdWordCellData F j x e θ β) := by
  classical
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨r, hr, he⟩ := amplitudeId_full_polynomial_budgets F
  obtain ⟨L, hL, hLr⟩ := amplitudeId_moment_bloch_trace (F.u j x) (Icc F.a F.b)
    (F.solution.1 (j, x)) F.ϖ r hϖ (fun n => ⟨_, (he n j x).1.choose_spec.2⟩) θ β e
  let U := fun t => truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t)
  have hU : MemLp U 2 (volume.restrict (Icc F.a F.b)) :=
    (truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega)).comp_memLp' (F.solution.2.1 (j, x))
  have henergy (n : ℕ) : (∫⁻ t in Icc F.a F.b, weightedFactorialNormSq n F.ϖ 0 r 1 (U t)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (he n j x).2
    apply lintegral_mono
    intro t
    dsimp only [U]
    rw [weightedFactorialNormSq_truncate _ le_rfl]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  obtain ⟨W, hW, hWr⟩ := amplitudeId_moment_cell_state (volume.restrict (Icc F.a F.b))
    U hU F.ϖ r hϖ hr henergy θ β e
  obtain ⟨⟨Mu⟩, hMS⟩ := amplitudeId_word_moment_families F j x θ e
  let MS := fun i => Classical.choice (hMS i)
  obtain ⟨⟨R, hR, hRr⟩, hQ⟩ := amplitudeId_moment_forcing_curves (Icc F.a F.b)
    F.G F.piece.hGm F.v F.piece.hv θ β _ _ Mu MS
  choose Q hQm hQr using hQ
  exact ⟨⟨L, hL, hLr, r, hr, hU, henergy, W, hW, hWr, R, hR, hRr, Q, hQm, hQr⟩⟩

/-- The coordinate lift reads the literal truncated vector jet. -/
theorem amplitudeId_wordCoordinate_truncated_readout
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (t : ℝ) (a : JetIndex2 1) :
    (amplitudeId_wordCoordinateSlice F j x e t).toFunction.jet a =ᵐ[volume]
      fun y => inner ℝ e
        ((truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t)).toFunction.jet a y) := by
  have ha : a.1.val ≤ 1 := Nat.le_of_lt_succ a.1.isLt
  have ht := planeJetOrder_truncate (show 1 ≤ F.κ j x + 1 by omega) ha (F.w j x t) a.2
  rw [planeJetOrder_eq_stored ha] at ht
  filter_upwards [(amplitudeId_wordCoordinate_readouts F j x e t).2 a] with y hy
  exact hy.trans (congrArg (inner ℝ e) (congrFun ht y).symm)

end AVRegularity.CycleWords.Assembly
