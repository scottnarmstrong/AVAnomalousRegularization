-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeRetainedEquation
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovarianceFluxRegLiftFlux
public import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal

section
section
/-! Native budgets, brick 2: the finite coefficient seminorm of the physical coefficients gives
the uniform window data (`NativeUniformCoeff`) needed by the product lemma. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff ENNReal
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- A component of the derivative array is bounded by the array norm. -/
theorem nativeBudget_orderedCoeff_le_array {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (C : Vec 2 → E →L[ℝ] F) (n : ℕ)
    (w : DerivativeWord2 n) (x : Vec 2) :
    ‖orderedCoefficientDerivative C n w x‖ ≤ ‖coefficientDerivativeArray C n x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  have h1 : ‖orderedCoefficientDerivative C n w x z‖ ≤ ‖coefficientDerivativeArray C n x z‖ := by
    rw [← coefficientDerivativeArray_apply]
    exact PiLp.norm_apply_le _ _
  exact h1.trans ((coefficientDerivativeArray C n x).le_opNorm z)

/-- The iterated derivative of a smooth coefficient is bounded by its derivative array. -/
theorem nativeBudget_iteratedFDeriv_le_array {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (C : Vec 2 → E →L[ℝ] F) (n : ℕ)
    (hC : ContDiff ℝ (n : ℕ) C) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n C x‖ ≤
      (Fintype.card (DerivativeWord2 n) : ℝ) * ‖coefficientDerivativeArray C n x‖ := by
  classical
  refine (ChartTransport.norm_le_sum_basisVec _).trans ?_
  calc _ ≤ ∑ _w : DerivativeWord2 n, ‖coefficientDerivativeArray C n x‖ := by
        refine Finset.sum_le_sum fun w _ => ?_
        have he := CycleComparison.Coarse.orderedCoefficientDerivative_eq_iteratedFDeriv C n hC
          (fun i => w (Fin.rev i)) x
        simp only [Fin.rev_rev] at he
        rw [← he]
        exact nativeBudget_orderedCoeff_le_array C n _ x
    _ = _ := by simp

/-- A finite coefficient seminorm bounds every derivative array uniformly on the window. -/
theorem nativeBudget_array_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (C : ℝ → Vec 2 → E →L[ℝ] F) {ρ : ℝ} (hρ : 0 < ρ)
    {K : ℕ} {a b : ℝ} (hsm : coefficientSeminorm ρ K a b C ≠ ⊤) (n : ℕ) (hn : n ≤ K) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖coefficientDerivativeArray (C t) n x‖ ≤ M := by
  unfold coefficientSeminorm at hsm
  have hterm := (ENNReal.sum_ne_top.mp hsm) n (Finset.mem_range.mpr (by omega))
  set S : ℝ≥0∞ := ⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2,
    (‖coefficientDerivativeArray (C t) n x‖₊ : ℝ≥0∞) with hS
  have hSne : S ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top] at hterm
    · exact hterm rfl
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨S.toReal, fun t ht x => ?_⟩
  have h1 : (‖coefficientDerivativeArray (C t) n x‖₊ : ℝ≥0∞) ≤ S :=
    (le_iSup (fun x : Vec 2 => (‖coefficientDerivativeArray (C t) n x‖₊ : ℝ≥0∞)) x).trans
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc a b) => ⨆ x : Vec 2,
        (‖coefficientDerivativeArray (C t) n x‖₊ : ℝ≥0∞)) t ht)
  simpa using ENNReal.toReal_mono hSne h1

/-- Smooth, periodic, jointly measurable coefficients with a finite seminorm have uniform
window data. -/
theorem nativeBudget_uniformCoeff_of_seminorm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] (C : ℝ → Vec 2 → E →L[ℝ] F) {ρ : ℝ} (hρ : 0 < ρ) {K : ℕ} {a b : ℝ}
    (hsm : coefficientSeminorm ρ K a b C ≠ ⊤)
    (hs : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (C t))
    (hp : ∀ t ∈ Icc a b, IsZ2Periodic (C t))
    (hm : Measurable (fun z : Icc a b × Vec 2 => C z.1 z.2)) :
    NativeUniformCoeff a b K C := by
  refine ⟨hs, hp, ?_, fun n hn => ?_⟩
  · have h1 : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => z.1.1) :=
      measurable_fst.comp measurable_subtype_coe
    have h2 : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => z.1.2) :=
      measurable_snd.comp measurable_subtype_coe
    exact hm.comp ((h1.subtype_mk (h := fun z => z.2)).prodMk h2)
  · obtain ⟨M, hM⟩ := nativeBudget_array_bound C hρ hsm n hn
    refine ⟨(Fintype.card (DerivativeWord2 n) : ℝ) * M, fun t ht x => ?_⟩
    exact (nativeBudget_iteratedFDeriv_le_array (C t) n
      ((hs t ht).of_le (Nat.cast_le.mpr hn)) x).trans
      (mul_le_mul_of_nonneg_left (hM t ht x) (Nat.cast_nonneg _))

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The physical coefficients of the incoming family have uniform window data on the window,
at every finite order. -/
theorem nativeBudget_physCoeff_uniform {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (K d : ℕ) (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u) :
    NativeUniformCoeff F.tp F.tf K (F.G.physCoeff v u γ d) := by
  obtain ⟨k, hc, hr0⟩ := hi.incoming_context
  have hlev := hi.stage.level
  have hε : 0 < D.eps (F.G.level - 1) := Construction.Stream.ocEpsilon_pos hi.stage.base
  have h := native_context_physical_fields hi.stage.base hi.stage.bandwidth
    (show 1 ≤ F.G.level by omega) (show j₀ ≤ F.G.level by omega) hc hi.stage.natural hi.shift
    hr0 F.tp F.tf K d v u γ
  exact nativeBudget_uniformCoeff_of_seminorm _ hε h.2.2
    (fun t ht => (h.1 t ht).1) (fun t ht => (h.1 t ht).2) h.2.1

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets: time-only coefficients, gradients and the covariance operator on window
bounds. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- A continuous operator-valued function of time alone is a uniform coefficient. -/
theorem NativeUniformCoeff.ofTime {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [MeasurableSpace W]
    [OpensMeasurableSpace (V →L[ℝ] W)] [SecondCountableTopology (V →L[ℝ] W)]
    (M : ℝ → V →L[ℝ] W) (hM : Continuous M) (a b : ℝ) (K : ℕ) :
    NativeUniformCoeff a b K (fun t _ => M t) := by
  refine ⟨fun _ _ => contDiff_const, fun _ _ _ _ => rfl, ?_, fun n _ => ?_⟩
  · exact (hM.measurable.comp (measurable_fst.comp measurable_subtype_coe))
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := M) (s := Icc a b)
      hM.continuousOn
    refine ⟨max C 0, fun t ht x => ?_⟩
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (hC t ht).trans (le_max_left _ _)
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp

/-- Multiplication by a continuous scalar function of time. -/
theorem ClassicalWindowBound.smul_time
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V} {s : ℝ → ℝ} (hs : Continuous s)
    (hf : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K (fun t x => s t • f t x) := by
  have h := ClassicalWindowBound.clm_apply
    (NativeUniformCoeff.ofTime (fun t => s t • ContinuousLinearMap.id ℝ V)
      (hs.smul continuous_const) a b K) hf
  simpa using h

/-- A one-letter word. -/
theorem nativeBudget_gradE_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec 2 → E) (x : Vec 2) (l : Fin 2) :
    gradE g x l = orderedDerivative (fun _ : Fin 1 => l) g x := by
  have h := congrFun (Sampling.orderedDerivative_snoc (Fin.elim0 : DerivativeWord2 0) l g) x
  have e : (Fin.snoc (Fin.elim0 : DerivativeWord2 0) l : DerivativeWord2 1) = fun _ => l := by
    funext i; fin_cases i; rfl
  rw [e] at h
  rw [h]
  simp [gradE, orderedDerivative_zero]

/-- The classical gradient as a flux. -/
theorem ClassicalWindowBound.grad
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} (hf : ClassicalWindowBound a b (K + 1) f) :
    ClassicalWindowBound a b K (fun t x => toFluxL (gradE (f t) x)) := by
  have hw := ClassicalWindowBound.pi (V := fun _ : Fin 2 => E)
    (fun l => hf.word (fun _ : Fin 1 => l) (L := K) (by omega))
  have hP := hw.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).symm.toContinuousLinearMap
  have e : (fun t x => toFluxL (gradE (f t) x)) = fun t x =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).symm.toContinuousLinearMap
        (fun l => orderedDerivative (fun _ : Fin 1 => l) (f t) x) := by
    funext t x
    exact congrArg (WithLp.toLp 2) (funext fun l => nativeBudget_gradE_eq _ _ l)
  rw [e]
  exact hP

/-- The covariance operator in terms of two-letter words. -/
theorem nativeBudget_covOperator_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (φ : Vec 2 → E) (x : Vec 2) :
    covOperator Hc φ x = ∑ i : Fin 2, ∑ j : Fin 2,
      Hc i j • orderedDerivative (Fin.snoc (fun _ : Fin 1 => j) i : DerivativeWord2 2) φ x := by
  unfold covOperator
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Sampling.orderedDerivative_snoc]
  have : orderedDerivative (fun _ : Fin 1 => j) φ = fun y => fderiv ℝ φ y (basisVec j) :=
    funext fun y => (nativeBudget_gradE_eq φ y j).symm
  rw [this]

/-- The covariance operator with a time-dependent continuous matrix lowers the order by two. -/
theorem ClassicalWindowBound.covOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, Continuous fun t => H t i j) (hf : ClassicalWindowBound a b (K + 2) f) :
    ClassicalWindowBound a b K (fun t x => covOperator (H t) (f t) x) := by
  have e : (fun t x => covOperator (H t) (f t) x) = fun t x => ∑ i : Fin 2, ∑ j : Fin 2,
      H t i j • orderedDerivative (Fin.snoc (fun _ : Fin 1 => j) i : DerivativeWord2 2) (f t) x :=
    funext fun t => funext fun x => nativeBudget_covOperator_eq _ _ _
  rw [e]
  refine ClassicalWindowBound.sum_fintype fun i => ClassicalWindowBound.sum_fintype fun j => ?_
  exact ClassicalWindowBound.smul_time (hH i j) (hf.word _ (L := K) (by omega))

/-- Iterates of the covariance operator. -/
theorem ClassicalWindowBound.covOp_iterate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hH : ∀ i j, Continuous fun t => H t i j)
    (p : ℕ) : ∀ {K : ℕ} {f : ℝ → Vec 2 → E}, ClassicalWindowBound a b (K + 2 * p) f →
      ClassicalWindowBound a b K (fun t x => (covOperator (H t))^[p] (f t) x) := by
  induction p with
  | zero => intro K f hf; simpa using hf
  | succ p ih =>
    intro K f hf
    have h1 : ClassicalWindowBound a b (K + 2 * p) (fun t x => covOperator (H t) (f t) x) :=
      ClassicalWindowBound.covOp hH (K := K + 2 * p) (hf.mono (by omega))
    simpa only [Function.iterate_succ_apply] using ih h1

/-- A time-dependent matrix applied to a gradient, as a flux. -/
theorem ClassicalWindowBound.matGrad
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} {R : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hR : ∀ i j, Continuous fun t => R t i j) (hf : ClassicalWindowBound a b (K + 1) f) :
    ClassicalWindowBound a b K (fun t x => toFluxL (fun k => ∑ l : Fin 2,
      R t k l • gradE (f t) x l)) := by
  have hk (k : Fin 2) : ClassicalWindowBound a b K (fun t x => ∑ l : Fin 2,
      R t k l • gradE (f t) x l) := by
    refine ClassicalWindowBound.sum_fintype fun l => ?_
    have := ClassicalWindowBound.smul_time (s := fun t => R t k l) (hR k l)
      (hf.word (fun _ : Fin 1 => l) (L := K) (by omega))
    simpa only [nativeBudget_gradE_eq] using this
  have hw := ClassicalWindowBound.pi (V := fun _ : Fin 2 => E) hk
  have hP := hw.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).symm.toContinuousLinearMap
  exact hP

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
section
/-! Native budgets, brick 3: the moving paired kernel preserves window bounds. If `f` has a
window bound of order `K` and the kernel has measurable, bounded matrices, then the kernel
average `t ↦ S.applyClassical φ₀ t (f t)` has a window bound of order `K`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
  AVRegularity.Analysis.Convolution AVRegularity.Providers AVRegularity.Providers.KernelSup
  AVRegularity.Construction.Preservation.Residual
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The moving paired kernel average of a continuous periodic field is the tensor operator. -/
theorem nativeBudget_applyClassical_eq_op {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (S : KernelSpec) (t : ℝ)
    {g : Vec 2 → H} (hc : Continuous g) (hp : IsZ2Periodic g) :
    S.applyClassical φ₀ t g = Op volume (tensorKer (momentKernel φ₀ S.order))
      (kerMap S.width (S.H₁ t) (S.H₂ t)) g := by
  have hφc := hasCompactSupport_of_unitBall hφsupp
  have hkK : IsKer (tensorKer (momentKernel φ₀ S.order)) :=
    isKer_tensorKer (contDiff_momentKernel hφc hφs S.order)
      (hasCompactSupport_momentKernel hφc S.order)
  obtain ⟨B, hB⟩ := bdd_of_periodic hc hp
  exact applyClassical_eq_op S _ rfl hkK t hc hB

/-- The window bound of the kernel average. -/
theorem nativeBudget_kernel_windowBound {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (S : KernelSpec)
    (h1 : Measurable S.H₁) (h2 : Measurable S.H₂) {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → H}
    (Q : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K (fun t y => S.applyClassical φ₀ t (f t) y) := by
  have hφc := hasCompactSupport_of_unitBall hφsupp
  have hkK : IsKer (tensorKer (momentKernel φ₀ S.order)) :=
    isKer_tensorKer (contDiff_momentKernel hφc hφs S.order)
      (hasCompactSupport_momentKernel hφc S.order)
  have hcont (t : ℝ) (ht : t ∈ Icc a b) : Continuous (f t) := (Q.smooth t ht).continuous
  refine ⟨fun t ht => (IterationPassage.Passage.regularKernel_contDiff_periodic hφs hφsupp S t
      (Q.smooth t ht) (Q.periodic t ht)).1,
    fun t ht => (IterationPassage.Passage.regularKernel_contDiff_periodic hφs hφsupp S t
      (Q.smooth t ht) (Q.periodic t ht)).2, ?_, ?_⟩
  · let X := {z : ℝ × Vec 2 // z.1 ∈ Icc a b}
    let k := tensorKer (momentKernel φ₀ S.order)
    have hev : Measurable (fun p : (Vec 2 →L[ℝ] Vec 2) × Vec 2 => p.1 p.2) :=
      (isBoundedBilinearMap_apply.continuous).measurable
    have hX1 : Measurable (fun p : X × (Vec 2 × Vec 2) => p.1.1.1) :=
      measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)
    have hX2 : Measurable (fun p : X × (Vec 2 × Vec 2) => p.1.1.2) :=
      measurable_snd.comp (measurable_subtype_coe.comp measurable_fst)
    have hM : Measurable (fun p : X × (Vec 2 × Vec 2) =>
        kerMap S.width (S.H₁ p.1.1.1) (S.H₂ p.1.1.1) p.2) := by
      have e : (fun p : X × (Vec 2 × Vec 2) => kerMap S.width (S.H₁ p.1.1.1) (S.H₂ p.1.1.1) p.2) =
          fun p => S.width • (S.H₁ p.1.1.1 p.2.1 + S.H₂ p.1.1.1 p.2.2) := by
        funext p; simp [kerMap]
      rw [e]
      have hadd : Measurable (fun p : X × (Vec 2 × Vec 2) =>
          S.H₁ p.1.1.1 p.2.1 + S.H₂ p.1.1.1 p.2.2) :=
        (hev.comp ((h1.comp hX1).prodMk (measurable_fst.comp measurable_snd))).add
          (hev.comp ((h2.comp hX1).prodMk (measurable_snd.comp measurable_snd)))
      exact hadd.const_smul S.width
    have hG : Measurable (fun p : X × (Vec 2 × Vec 2) =>
        k p.2 • f p.1.1.1 (p.1.1.2 - kerMap S.width (S.H₁ p.1.1.1) (S.H₂ p.1.1.1) p.2)) := by
      have hk : Measurable (fun p : X × (Vec 2 × Vec 2) => k p.2) :=
        ((isKer_tensorKer (contDiff_momentKernel hφc hφs S.order)
          (hasCompactSupport_momentKernel hφc S.order)).smooth.continuous.measurable).comp
          measurable_snd
      refine hk.smul ?_
      have hz : Measurable (fun p : X × (Vec 2 × Vec 2) =>
          (⟨(p.1.1.1, p.1.1.2 - kerMap S.width (S.H₁ p.1.1.1) (S.H₂ p.1.1.1) p.2), p.1.2⟩ : X)) :=
        (hX1.prodMk (hX2.sub hM)).subtype_mk
      exact Q.measurable.comp hz
    have hsm := hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec 2 × Vec 2)))
    have heq : (fun z : X => S.applyClassical φ₀ z.1.1 (f z.1.1) z.1.2) = fun z : X =>
        ∫ ζ : Vec 2 × Vec 2, k ζ • f z.1.1
          (z.1.2 - kerMap S.width (S.H₁ z.1.1) (S.H₂ z.1.1) ζ) := by
      funext z
      rw [nativeBudget_applyClassical_eq_op hφs hφsupp S z.1.1 (hcont _ z.2)
        (Q.periodic _ z.2)]
      rfl
    rw [heq]
    exact hsm.measurable
  · intro n hn w
    obtain ⟨B, hB, hb⟩ := Q.global_bound n hn w
    refine ⟨fun t => (∫ ζ, ‖tensorKer (momentKernel φ₀ S.order) ζ‖) * B t,
      hB.const_mul _, fun t ht x _ => ?_⟩
    have hfn : ContDiff ℝ (n : ℕ∞) (f t) := (Q.smooth t ht).of_le (Nat.cast_le.mpr hn)
    have hw : orderedDerivative w (S.applyClassical φ₀ t (f t)) =
        Op volume (tensorKer (momentKernel φ₀ S.order)) (kerMap S.width (S.H₁ t) (S.H₂ t))
          (orderedDerivative w (f t)) := by
      rw [nativeBudget_applyClassical_eq_op hφs hφsupp S t (hcont t ht) (Q.periodic t ht)]
      exact kernel_readout_op_word hkK _ w hfn (Q.periodic t ht)
    rw [hw]
    exact norm_op_le (μ := volume) hkK _ (fun y => hb t ht y) x

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The kernel-applied lifted field of every incoming edge has the window bound of order
`Dm + 2`, from the lifted time curve. -/
theorem nativeBudget_kernelField {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    {dUh : F.Field} (hl : ClassicalTimeCurve F (Dm + 4) F.uh dUh)
    (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u) :
    ClassicalWindowBound F.tp F.tf (Dm + 2) (fun t y =>
      (F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t
        (fun y' => F.uh t y' u) y) := by
  obtain ⟨Γ, hΓ⟩ := hi.kernels
  exact nativeBudget_kernel_windowBound hi.smooth hi.support _ (hΓ v u γ).1 (hΓ v u γ).2.1
    (show ClassicalWindowBound F.tp F.tf (Dm + 2) (fun t y => F.uh t y u) from hl.field u)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets, brick 4a: the plain, kernel and fine coefficient fluxes of order one. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- One coefficient term: the physical coefficient applied to the word jets of a window-bounded
field. -/
theorem nativeBudget_coeffTerm {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u) (d : ℕ) (hd : d - 1 + 1 ≤ Dm)
    {g : ℝ → Vec 2 → hr u.1.root} (hg : ClassicalWindowBound F.tp F.tf Dm g) :
    ClassicalWindowBound F.tp F.tf 1 (fun t x =>
      F.G.physCoeff v u γ d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d - 1) =>
        orderedDerivative word (g t) x)) := by
  have hw := ClassicalWindowBound.pi (V := fun _ : DerivativeWord2 (d - 1) => hr u.1.root)
    (fun word => hg.word word (L := 1) (by omega))
  have hP := hw.map (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)).symm.toContinuousLinearMap
  exact ClassicalWindowBound.clm_apply (nativeBudget_physCoeff_uniform hi 1 d v u γ) hP

/-- The finite sum over incoming edges and coefficient orders. -/
theorem nativeBudget_sumTerms {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (v : CompIn F.G.comps) (g : ∀ u : CompIn F.G.comps, F.G.fam.Γ v u → ℝ → Vec 2 → hr u.1.root)
    (hg : ∀ u γ, ClassicalWindowBound F.tp F.tf Dm (g u γ)) :
    ClassicalWindowBound F.tp F.tf 1 (fun t x =>
      ∑ u : CompIn F.G.comps, ∑ γ : F.G.fam.Γ v u, ∑ d : Finset.Icc 2 Dm,
        F.G.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word (g u γ t) x)) := by
  refine ClassicalWindowBound.sum_fintype fun u => ?_
  refine ClassicalWindowBound.sum_fintype fun γ => ?_
  refine ClassicalWindowBound.sum_fintype fun d => ?_
  have := (Finset.mem_Icc.1 d.2)
  exact nativeBudget_coeffTerm hi v u γ d.1 (by omega) (hg u γ)

/-- The plain coefficient flux has the window bound of order one. -/
theorem nativeBudget_plain {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {dUh : F.Field}
    (hl : ClassicalTimeCurve F (Dm + 4) F.uh dUh) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.plain v) :=
  nativeBudget_sumTerms hi v (fun u _ t y => F.uh t y u)
    (fun u _ => (show ClassicalWindowBound F.tp F.tf (Dm + 2) (fun t y => F.uh t y u) from
      hl.field u).mono (by omega))

/-- The kernel coefficient flux has the window bound of order one. -/
theorem nativeBudget_kernel {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {dUh : F.Field}
    (hl : ClassicalTimeCurve F (Dm + 4) F.uh dUh) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.kernel v) :=
  nativeBudget_sumTerms hi v (fun u γ t y =>
      (F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t (fun y' => F.uh t y' u) y)
    (fun u γ => (nativeBudget_kernelField hi hl v u γ).mono (by omega))

/-- The fine coefficient flux has the window bound of order one. -/
theorem nativeBudget_fine {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {dUh : F.Field}
    (hl : ClassicalTimeCurve F (Dm + 4) F.uh dUh) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.fine v) :=
  nativeBudget_sumTerms hi v (fun u γ t y => F.uh t y u -
      (F.G.kernelOf F.P F.seedK F.freshK v u γ).applyClassical F.φ₀ t (fun y' => F.uh t y' u) y)
    (fun u γ => (((show ClassicalWindowBound F.tp F.tf (Dm + 2) (fun t y => F.uh t y u) from
      hl.field u).sub (nativeBudget_kernelField hi hl v u γ)).mono (by omega)))

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! The finite native mean action and its physical pullback expansion. Coefficients
are the actual path means; no input-field periodicity or time regularity is imposed.
The degenerate cases are included: empty components, zero datum, grade zero/degree two, N=0, Dm=1,
and inactive cutoffs. Only active cutoffs consume the closed cell window. -/

/-- The actual native path mean action at finite spatial regularity. -/
def NativeFiniteMeanActionStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀},
    ∀ (hi : NativeInput F) (p : OddSlot) (g n : ℕ),
    g ≤ F.depth → 2 ≤ n → n ≤ F.N + Dm →
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    ∀ f : Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root,
      ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) f → ∀ τ,
      τ ∈ Set.Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) →
      ∀ (X : Vec 2) (k : Fin 2) (v : CompIn F.G.comps),
        fieldCellMean (fun z => liftFluxX Q (F.CcT p.1) (fun _ => f) g n τ X z k v) =
          liftApply (n - 1) (nativeStagePathMeanCoefficient hi.stage p g n k)
            (fun _ => f) τ X 0 v

/-- Cutoff-weighted native cell mean as a finite sum of physical pullback jets. -/
def NativeMeanPullbackExpansionStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀},
    ∀ (hi : NativeInput F) (p : OddSlot) (g n : ℕ), g ≤ F.depth → 2 ≤ n → n ≤ F.N + Dm →
    ∀ (a : F.Field) (t : ℝ), t ∈ Set.Icc F.tp F.tf →
    (∀ u, ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => a t y u)) →
    ∀ (x : Vec 2) (k : Fin 2) (v : CompIn F.G.comps),
    let clock := D.cellScaleSq F.m
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m p.1)
    let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m p.1) y s
    ocCutoff D.α D.q D.Λ F.m p.1 t • fieldCellMean (fun z =>
      liftFluxX Q (F.CcT p.1)
        (fun s Y => a (clock * s) (chart (clock * s) (ρ • Y))) g n (clock⁻¹ * t)
        (ρ⁻¹ • label t x) z k v) =
      ∑ m ∈ Finset.range n, ∑ α : DerivativeWord2 m,
        ∑ c : OrderedFinpartition m, ∑ u : CompIn F.G.comps,
          ocCutoff D.α D.q D.Λ F.m p.1 t •
            nativeStagePathMeanCoefficient hi.stage p g n k m α
              (clock⁻¹ * t) (ρ⁻¹ • label t x) 0 v u
              ((c.compAlongOrderedFinpartition
                (iteratedFDeriv ℝ c.length (fun y => a t y u) x)
                (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                  (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i))))

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Conditional assembly of the native mean action from scalar path means and
literal mean decomposition. The two hypotheses are the scalar path means and the mean decomposition. -/

/-- The scalar path identity, including the edgeless path. -/
def ScalarPathMeanStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)]
    (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu)
    (G : GenStage D hr Dm bw j₀) (hi : StageSuccessor.Input P Mn G)
    (g : ℕ) (π : StagePath G g) (p : OddSlot) (n : ℕ), 2 ≤ n → n ≤ Mn.N + Dm →
    let ρ := Mn.lenFactor * liftLength D G.level
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
    let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∀ f : Vec 2 → Fin (g + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ t ∈ Icc a b, ∀ X z : Vec 2, ∀ k : Fin 2,
      fieldCellMean (fun y => liftFluxX Q C (fun _ => f) g n t X y k) (Fin.last g) =
        liftApply (n - 1) (actualMeanFluxCoefficient Q C g n k) (fun _ => f) t X z (Fin.last g)

/-- Decomposition of the literal native flux mean into scalar walk means,
read through an arbitrary continuous linear functional. -/
def WalkMeanExpansionStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)]
    (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu)
    (G : GenStage D hr Dm bw j₀) (hi : StageSuccessor.Input P Mn G)
    (H : ℕ) (p : OddSlot) (g n : ℕ), g ≤ H → 2 ≤ n → n ≤ Mn.N + Dm →
    let ρ := Mn.lenFactor * liftLength D G.level
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∀ f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Icc a b, ∀ X : Vec 2, ∀ k : Fin 2,
      ∀ v : CompIn G.comps, ∀ ℓ : hr v.1.root →L[ℝ] ℝ,
      ℓ (fieldCellMean (fun z => liftFluxX Q (nativeStagePathCandidate hi H p)
        (fun _ => f) g n t X z k v)) =
      ∑ u : CompIn G.comps, ∑ q : F.Walk g u v,
        let π := Classical.choose (stage_walk_path q)
        let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
        let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
        fieldCellMean (fun z => liftFluxX Qp C
          (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u))))
          g n t X z k) (Fin.last g)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- Scalarization of a single walk's coefficient action. -/
theorem single_path_coefficient_action {g : ℕ} (n : ℕ)
    (c : LiftCoeff (Fin (g + 1)) (fun _ => ℝ))
    (u v : CompIn G.comps) (M : hr u.1.root →L[ℝ] hr v.1.root)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (f : Vec 2 → ∀ w : CompIn G.comps, hr w.1.root)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (X z : Vec 2) :
    liftApply n c (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (M (f Y u)))) t X z (Fin.last g) =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        c m α t X z (Fin.last g) 0 1 * ℓ (M (orderedDerivative α f X u)) := by
  classical
  let L := (ℓ.comp M).comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun w : CompIn G.comps => hr w.1.root) u)
  have hscalar : ContDiff ℝ (⊤ : ℕ∞) (fun Y => ℓ (M (f Y u))) := L.contDiff.comp hf
  have hd (m : ℕ) (α : DerivativeWord2 m) :
      orderedDerivative α (fun Y => Pi.single (0 : Fin (g + 1)) (ℓ (M (f Y u)))) X =
        (Pi.single (0 : Fin (g + 1)) (ℓ (M (orderedDerivative α f X u))) : Fin (g + 1) → ℝ) := by
    have he := orderedDerivative_single (ι := Fin (g + 1)) (hs := fun _ => ℝ) (w := 0) (1 : ℝ) hscalar (α := α)
    simp only [smul_eq_mul, mul_one] at he
    rw [he]
    have hc := HLMaps.hl_orderedDerivative_clm_apply L α
      (hf.of_le (by exact_mod_cast le_top)) X
    exact congrArg (Pi.single (0 : Fin (g + 1))) hc
  simp only [liftApply, hd]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro α hα
  rw [Finset.sum_eq_single (0 : Fin (g + 1))]
  · simp only [Pi.single_eq_same]
    have he := (c m α t X z (Fin.last g) 0).map_smul
      (ℓ (M (orderedDerivative α f X u))) (1 : ℝ)
    simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using he
  · intro i hi hne
    simp only [Pi.single_eq_of_ne hne, map_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The coefficient side of the identity is the sum of scalarized path actions. -/
theorem mean_coefficient_action (hi : StageSuccessor.Input P Mn G)
    (p : OddSlot) (g n : ℕ) (k : Fin 2)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    ℓ (liftApply (n - 1) (nativeStagePathMeanCoefficient hi p g n k) (fun _ => f) t X z v) =
      ∑ u : CompIn G.comps, ∑ q : F.Walk g u v,
        let π := Classical.choose (stage_walk_path q)
        let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
        let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
        liftApply (n - 1) (actualMeanFluxCoefficient Q C g n k)
          (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u)))) t X z (Fin.last g) := by
  classical
  dsimp only
  simp_rw [single_path_coefficient_action (n - 1) _ _ v _ ℓ f hf t X z]
  simp only [liftApply, nativeStagePathMeanCoefficient, sum_apply, smul_apply, map_sum, map_smul,
    smul_eq_mul]
  conv_lhs =>
    arg 2
    ext m
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  conv_lhs =>
    arg 2
    ext m
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Assembly of the native mean action; the hypotheses are separately named statements. -/
theorem native_mean_action_of_ingredients
    (hs : ScalarPathMeanStatement) (hw : WalkMeanExpansionStatement) :
    NativeStagePathMeanActionStatement := by
  classical
  intro hr _ _ _ D Dm bw j₀ P Mn G hi H p g n hg hn hnR
  dsimp only
  intro f hf t ht X k v
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro ℓ
  rw [mean_coefficient_action hi p g n k f hf t X 0 v ℓ]
  rw [hw hr D Dm bw j₀ P Mn G hi H p g n hg hn hnR f hf t ht X k v ℓ]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro q hq
  apply hs hr D Dm bw j₀ P Mn G hi g (Classical.choose (stage_walk_path q)) p n hn hnR
  · exact ((ContinuousLinearMap.single ℝ (fun _ : Fin (g + 1) => ℝ) 0).contDiff.comp
    (ℓ.contDiff.comp (((stageFam G (D.cellScaleSq G.level)
      ((Mn.lenFactor * liftLength D G.level) / D.eps (G.level - 1)) p
      (G.actual p)).compMap q).contDiff.comp ((contDiff_pi.mp hf) u))))
  · exact ht

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
