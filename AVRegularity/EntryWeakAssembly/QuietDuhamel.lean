-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietBackwardEvolution
public import AVRegularity.CycleWords.MetricTaylorTimeCoefficient
public import AVRegularity.EntryWeakAssembly.Assembly.WeakQuietCoefficientOfIngredients
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.EntryWeakAssembly.QuietMarginPlan

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open TopologicalSpace
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Measurability of the genuine backward evolution. A fixed terminal time
gives a native continuous trajectory; adjoint pairing treats a varying terminal
time. Countably many Hilbert readouts recover strong measurability. -/

/-- Countable Hilbert readouts recover strong measurability in a separable
complete real Hilbert space. The continuous readout map is a Borel embedding. -/
theorem weak_quiet_stronglyMeasurable_of_inner {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] (f : T → E)
    (hf : ∀ z : E, Measurable (fun t => inner ℝ (f t) z)) : StronglyMeasurable f := by
  borelize E
  let e : E → ℕ → ℝ := fun u n => inner ℝ u (denseSeq E n)
  have hc : Continuous e := continuous_pi fun _ => continuous_id.inner continuous_const
  have hi : Function.Injective e := by
    intro u v huv
    apply ext_inner_right ℝ
    have hh := (denseRange_denseSeq E).equalizer
      (continuous_const.inner continuous_id : Continuous (fun z => inner ℝ u z))
      (continuous_const.inner continuous_id : Continuous (fun z => inner ℝ v z))
      (funext fun n => congrFun huv n)
    exact congrFun hh
  have hm : Measurable (e ∘ f) := Measurable.of_eval fun n => hf (denseSeq E n)
  exact ((hc.measurableEmbedding hi).measurable_comp_iff.mp hm).stronglyMeasurable

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- Pairing the backward value with a fixed test is continuous in the left
endpoint, after clamping reversed intervals to the identity endpoint. -/
theorem weak_quiet_backward_pair_continuous_left (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (b : Set.Icc x.left x.right)
    (φ ψ : TorusHk 0 ℝ) :
    Continuous (fun a : Set.Icc x.left x.right =>
      inner ℝ (H.apply 0 (min a.val b.val) b φ) ψ) := by
  have hc := weak_quiet_backward_continuous_left x hd H 0 (Nat.zero_le x.cap)
    b b.property φ
  have hm : Continuous (fun a : Set.Icc x.left x.right => min a.val b.val) :=
    continuous_subtype_val.min continuous_const
  have hh := hc.comp_continuous hm (fun a =>
    ⟨le_min a.property.1 b.property.1, min_le_right _ _⟩)
  exact hh.inner continuous_const

/-- The other endpoint is continuous after a Hilbert readout, by the proved
native forward/backward pairing, with the same identity clamping. -/
theorem weak_quiet_backward_pair_continuous_right (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (a : Set.Icc x.left x.right)
    (φ ψ : TorusHk 0 ℝ) :
    Continuous (fun b : Set.Icc x.left x.right =>
      inner ℝ (H.apply 0 (min a.val b.val) b φ) ψ) := by
  obtain ⟨u, w, hu, _⟩ := weak_scalar_torus_forward_native hd (Nat.zero_le x.cap)
    a x.right a.property.1 a.property.2 le_rfl ψ
  have hmax : Continuous (fun b : Set.Icc x.left x.right => max a.val b.val) :=
    continuous_const.max continuous_subtype_val
  have hc := (hu.1 0).comp_continuous hmax (fun b =>
    ⟨le_max_left _ _, max_le a.property.2 b.property.2⟩)
  have he : (fun b : Set.Icc x.left x.right =>
      inner ℝ (H.apply 0 (min a.val b.val) b φ) ψ) =
      (fun b : Set.Icc x.left x.right => inner ℝ φ (u (max a.val b.val))) := by
    funext b
    by_cases hab : a.val ≤ b.val
    · rw [min_eq_left hab, max_eq_right hab,
        weak_quiet_backward_forward_pair x hd H a b a.property.1 hab b.property.2 φ ψ]
      rw [weak_scalar_torus_forward_eq hd (Nat.zero_le x.cap) a.property.1 hab b.property.2
        (CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left b.property.2 hu)]
    · have hba := le_of_not_ge hab
      rw [min_eq_right hba, max_eq_left hba,
        weak_quiet_backward_same_time x H 0 (Nat.zero_le x.cap) b b.property φ]
      have hinit : u a = ψ := hu.2.2.2.1 0
      rw [hinit]
  rw [he]
  exact continuous_const.inner hc

/-- Joint strong measurability of the order-zero backward propagator on the
quiet margin square. On ordered endpoints this is the actual propagator; on reversed
endpoints it is the identity. No time continuity of source coefficients is used. -/
theorem weak_quiet_backward_stronglyMeasurable_zero
    (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (φ : TorusHk 0 ℝ) :
    StronglyMeasurable (fun p : Set.Icc x.left x.right × Set.Icc x.left x.right =>
      H.apply 0 (min p.1.val p.2.val) p.2 φ) := by
  let : SeparableSpace (TorusHk 0 ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace 0
  apply weak_quiet_stronglyMeasurable_of_inner
  intro ψ
  exact measurable_uncurry_of_continuous_of_measurable
    (fun b => weak_quiet_backward_pair_continuous_left x hd H b φ ψ)
    (fun a => (weak_quiet_backward_pair_continuous_right x hd H a φ ψ).measurable)

/-- Joint strong measurability at every finite reserve follows from order zero
through the continuous injective Sobolev embedding and its Borel inverse. -/
theorem weak_quiet_backward_stronglyMeasurable
    (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (P : ℕ) (hP : P ≤ x.cap) (φ : TorusHk P ℝ) :
    StronglyMeasurable (fun p : Set.Icc x.left x.right × Set.Icc x.left x.right =>
      H.apply P (min p.1.val p.2.val) p.2 φ) := by
  let : SeparableSpace (TorusHk P ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace P
  let : SeparableSpace (TorusHk 0 ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace 0
  borelize (TorusHk P ℝ) (TorusHk 0 ℝ)
  let e := truncateTorusHk (E := ℝ) (Nat.zero_le P)
  have hi : Function.Injective e := by
    intro u v he
    apply TorusHk.ext_value
    exact congrArg (fun z : TorusHk 0 ℝ => CoupledEnergy.Galerkin.torusHkValueCLM z) he
  have hm := weak_quiet_backward_stronglyMeasurable_zero x hd H
    (truncateTorusHk (Nat.zero_le P) φ)
  have he : (fun p : Set.Icc x.left x.right × Set.Icc x.left x.right =>
      H.apply 0 (min p.1.val p.2.val) p.2 (truncateTorusHk (Nat.zero_le P) φ)) =
      (fun p : Set.Icc x.left x.right × Set.Icc x.left x.right =>
        e (H.apply P (min p.1.val p.2.val) p.2 φ)) := by
    funext p
    exact (weak_quiet_backward_truncate x hd H (Nat.zero_le P) hP
      (min p.1.val p.2.val) p.2 (le_min p.1.property.1 p.2.property.1)
      (min_le_right _ _) p.2.property.2 φ).symm
  rw [he] at hm
  exact ((e.continuous.measurableEmbedding hi).measurable_comp_iff.mp hm.measurable).stronglyMeasurable

/-- The chosen genuine operators may act on a measurable, varying test field.
This uses strong operator measurability; operator-norm measurability is not
required for the source-path integrals. -/
theorem weak_quiet_backward_stronglyMeasurable_action
    {T : Type*} [MeasurableSpace T] (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (P : ℕ) (hP : P ≤ x.cap) (a b : T → Set.Icc x.left x.right)
    (ha : Measurable a) (hb : Measurable b) (φ : T → TorusHk P ℝ)
    (hφ : StronglyMeasurable φ) :
    StronglyMeasurable (fun t =>
      (weakQuietBackwardEvolution x hd).apply P (min (a t).val (b t).val) (b t) (φ t)) := by
  let : SeparableSpace (TorusHk P ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace P
  borelize (TorusHk P ℝ)
  apply CoupledEnergy.Variational.stronglyMeasurable_operator_action
    (fun t => weakQuietBackwardOperator x hd P (min (a t).val (b t).val) (b t)) _ hφ
  intro ψ
  exact (weak_quiet_backward_stronglyMeasurable x hd (weakQuietBackwardEvolution x hd)
    P hP ψ).comp_measurable (ha.prodMk hb)

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Native order-zero rows of the actual width-zero kernel equation. The flux
below retains the supplied high carrier and every physical order. It is not a
bounded extension of a high differential operator on H¹. -/

section FluxCurve
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.KernelEnergy
open AVRegularity.Construction.Preservation.FullLift
variable {K J r : ℕ} (hKJ : K ≤ J) {ε a b : ℝ} (hε : 0 < ε)
  (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ))
  (hA : coefficientSeminorm ε J a b A ≠ ⊤)
  (hC : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
  (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))

/-- The actual source flux as a native time curve. The coefficient is extended
by zero outside the window; on the window this is precisely A times the
ordered derivative tensor of the supplied carrier. -/
def weakQuietSourceFluxCurve (u : ℝ → TorusHk (K + r) ℝ) (t : ℝ) :
    TorusHk K (PiLp 2 (fun _ : Fin 2 => ℝ)) :=
  CycleWords.torusWindowMultiplier a b A hC hp
    (fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal)
    (fun _ => ENNReal.toReal_nonneg)
    (fun t ht l x => coefficientOrderSup_derivative_bound ε hε K a b A
      (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε hKJ a b A))
      l.val (Nat.le_of_lt_succ l.isLt) t ht x)
    t (torusDerivativeTensor (u t))

/-- No smoothing estimate is used to obtain square integrability of an actual
incoming flux: it follows from the supplied high carrier and multiplier. -/
theorem weak_quiet_source_flux_curve_memLp
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (u : ℝ → TorusHk (K + r) ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Icc a b))) :
    MemLp (weakQuietSourceFluxCurve hKJ hε A hA hC hp u) 2
      (volume.restrict (Set.Icc a b)) := by
  by_cases hab : a ≤ b
  · let C := fun t x => A (Set.projIcc a b hab t) x
    have hCm : Measurable (Function.uncurry C) := hm.comp
      (((continuous_projIcc (a := a) (b := b) (h := hab)).measurable.comp
        measurable_fst).prodMk measurable_snd)
    have he : CycleWords.windowCoefficient a b A = CycleWords.windowCoefficient a b C := by
      funext t x
      by_cases ht : t ∈ Set.Icc a b
      · simp only [CycleWords.windowCoefficient, ht, ite_true, C, Set.projIcc_of_mem]
      · simp only [CycleWords.windowCoefficient, ht, ite_false]
    have hwm : Measurable (Function.uncurry (CycleWords.windowCoefficient a b A)) := by
      rw [he]
      exact CycleWords.windowCoefficient_measurable a b C hCm
    have hten := (torusKernelDerivativeTensorCLM K r (E := ℝ)).comp_memLp' hu
    simp only [Function.comp_def, torusKernelDerivativeTensorCLM_apply] at hten
    exact CycleWords.torusCoefficient_time_memLp (volume.restrict (Set.Icc a b))
      (CycleWords.windowCoefficient a b A) hwm
      (CycleWords.windowCoefficient_contDiff a b K A hC)
      (CycleWords.windowCoefficient_periodic a b A hp)
      (fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal)
      (CycleWords.windowCoefficient_derivative_bound a b K A _
        (fun _ => ENNReal.toReal_nonneg)
        (fun t ht l x => coefficientOrderSup_derivative_bound ε hε K a b A
          (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε hKJ a b A))
          l.val (Nat.le_of_lt_succ l.isLt) t ht x))
      _ hten
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab), Measure.restrict_empty]
    exact memLp_measure_zero

/-- Agreement at every closed-window time, with the original native flux. -/
theorem weak_quiet_source_flux_curve_eq
    (u : ℝ → TorusHk (K + r) ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    weakQuietSourceFluxCurve hKJ hε A hA hC hp u t =
      weakQuietSourceFlux hKJ ε hε a b A hA t ht (hC t ht) (hp t ht) (u t) := by
  exact CycleWords.torusWindowMultiplier_agrees a b A hC hp _
    (fun _ => ENNReal.toReal_nonneg) _ t ht _

/-- The flux curve has the exact raw jet representative used by the
kernel equation. This is an equality of native representatives, not a bound. -/
theorem weak_quiet_source_flux_curve_value_ae
    (u : ℝ → TorusHk (K + r) ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (weakQuietSourceFluxCurve hKJ hε A hA hC hp u t).toFunction.jet
      (valueIndex2 K) =ᵐ[volume.restrict unitCube]
      fun x => A t x (WithLp.toLp 2 fun word : DerivativeWord2 r =>
        (u t).toFunction.jet ⟨⟨r, by omega⟩, word⟩ x) := by
  rw [weak_quiet_source_flux_curve_eq hKJ hε A hA hC hp u t ht]
  have hm := torusMulCoefficient_toFunction_value_ae (torusDerivativeTensor (u t))
    (A t) (hC t ht) (hp t ht)
    (fun l x => coefficientOrderSup_derivative_bound ε hε K a b A
      (ne_top_of_le_ne_top hA (coefficientSeminorm_order_mono ε hKJ a b A))
      l.val (Nat.le_of_lt_succ l.isLt) t ht x)
  have hten := torusDerivativeTensor_base_ae (K := K) (r := r) (u t)
  filter_upwards [hm, hten] with x hmx htx
  change ((torusDerivativeTensor (u t)).mulCoefficient (A t) _ _ _).toFunction.jet
    (valueIndex2 K) x = A t x _
  rw [hmx, htx]
  congr 1
  apply PiLp.ext
  intro word
  change (u t).toFunction.jet (prefixJetIndex word (valueIndex2 K)) x =
    (u t).toFunction.jet ⟨⟨r, by omega⟩, word⟩ x
  congr 1
  simp [prefixJetIndex, valueIndex2, valueIndex]

end FluxCurve

namespace WeakQuietExpansionCase
variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- Every prescribed weak mass is strictly positive, including the root. -/
theorem mass_pos (x : WeakQuietExpansionCase plan prices) (v : x.Vertex) :
    0 < x.mass v := by
  have hΛ : 1 ≤ x.c.D.Λ := by
    rw [x.c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge x.B).trans x.c.base_ge)
  exact weakMass_pos x.c.D _ _ _ x.A.Nw_pos x.A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ) v.1

/-- The aggregate b budget makes every actual constituent coefficient budget
finite. Positivity of the masses is essential when extracting a summand. -/
theorem coefficient_finite (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) (γ : (x.c.stage x.i).fam.Γ v u)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 x.c.Dm) :
    coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
      x.left x.right ((x.c.stage x.i).physCoeff v u γ d) ≠ ⊤ := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, hmatrix⟩ := x.bounds
  let C := coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
    x.left x.right ((x.c.stage x.i).physCoeff v u γ d)
  let σ := ENNReal.ofReal (Real.sqrt (x.mass u / x.mass v))
  let νd := ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2))
  have hterm : C * νd⁻¹ ≤ ∑ γ' : (x.c.stage x.i).fam.Γ v u,
      ∑ d' ∈ Finset.Icc 2 x.c.Dm,
        coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
          x.left x.right ((x.c.stage x.i).physCoeff v u γ' d') *
          (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d' - 2)))⁻¹ :=
    calc
      _ ≤ ∑ d' ∈ Finset.Icc 2 x.c.Dm,
          coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
            x.left x.right ((x.c.stage x.i).physCoeff v u γ d') *
            (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d' - 2)))⁻¹ :=
        Finset.single_le_sum (fun _ _ => zero_le) hd
      _ ≤ _ := Finset.single_le_sum
        (f := fun γ' : (x.c.stage x.i).fam.Γ v u =>
          ∑ d' ∈ Finset.Icc 2 x.c.Dm,
            coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
              x.left x.right ((x.c.stage x.i).physCoeff v u γ' d') *
              (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d' - 2)))⁻¹)
        (fun _ _ => zero_le) (Finset.mem_univ γ)
  have hbound : σ * (C * νd⁻¹) ≤ ENNReal.ofReal (x.b v u) :=
    (mul_le_mul' le_rfl hterm).trans (hmatrix v u)
  have hσ : σ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr
    (Real.sqrt_pos.2 (div_pos (x.mass_pos u) (x.mass_pos v))))
  have hνd : νd⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  change C ≠ ⊤
  intro hC
  rw [hC, ENNReal.top_mul hνd, ENNReal.mul_top hσ] at hfin
  exact hfin rfl

/-- The literal source sum has the fixed weak order cap. The terms removed
from the ambient cap are zero physical operators, not discarded estimates. -/
theorem source_orders (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) (t : ℝ) (ψ : Vec 2 → ℝ) (y : Vec 2) :
    x.source v u t ψ y = Real.sqrt (x.mass u / x.mass v) *
      ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.order,
        weakQuietPrimalSource (d - 1) ((x.c.stage x.i).physCoeff v u γ d t) ψ y := by
  classical
  unfold source
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans x.c.order_ge⟩
  · intro d hd hnot
    have hdc : x.order < d := by
      have hlow := (Finset.mem_Icc.mp hd).1
      simp only [Finset.mem_Icc, not_and, not_le] at hnot
      exact hnot hlow
    rw [weak_quiet_physical_above_cap x.c x.i x.level_lt.le x.level_le v u γ d hdc]
    simp only [weakQuietPrimalSource, weakQuietDivergence, zero_apply,
      PiLp.zero_apply, CycleComparison.Coarse.partialOp, fderiv_const_apply, Finset.sum_const_zero]

/-- The actual physical flux has the same fixed weak-order support as its
formal divergence source. This identity retains the supplied high jets. -/
theorem physical_flux_orders (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) (γ : (x.c.stage x.i).fam.Γ v u)
    (t : ℝ) (Y : TorusHk (x.R.Kw + x.c.Dm - 1) ℝ) (y : Vec 2) :
    (∑ d : ↥(Finset.Icc 2 x.c.Dm), (x.c.stage x.i).physCoeff v u γ d.1 t y
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        Y.toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y)) =
    ∑ d : ↥(Finset.Icc 2 x.order), (x.c.stage x.i).physCoeff v u γ d.1 t y
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        Y.toFunction.jet ⟨⟨d.1 - 1, by
          have hh := (Finset.mem_Icc.mp d.2).2.trans x.c.order_ge; omega⟩, word⟩ y) := by
  classical
  let F (d : ℕ) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
    if hd : d - 1 ≤ x.R.Kw + x.c.Dm - 1 then
      (x.c.stage x.i).physCoeff v u γ d t y
        (WithLp.toLp 2 fun word : DerivativeWord2 (d - 1) =>
          Y.toFunction.jet ⟨⟨d - 1, by omega⟩, word⟩ y)
    else 0
  have hfull : (∑ d : ↥(Finset.Icc 2 x.c.Dm),
      (x.c.stage x.i).physCoeff v u γ d.1 t y
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          Y.toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y)) =
      ∑ d ∈ Finset.Icc 2 x.c.Dm, F d := by
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro d _
    have hd : d.1 - 1 ≤ x.R.Kw + x.c.Dm - 1 := by
      have hh := Finset.mem_Icc.mp d.2
      omega
    simp only [F, dite_eq_left hd]
  have hlow : (∑ d : ↥(Finset.Icc 2 x.order),
      (x.c.stage x.i).physCoeff v u γ d.1 t y
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          Y.toFunction.jet ⟨⟨d.1 - 1, by
            have hh := (Finset.mem_Icc.mp d.2).2.trans x.c.order_ge; omega⟩, word⟩ y)) =
      ∑ d ∈ Finset.Icc 2 x.order, F d := by
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro d _
    have hd : d.1 - 1 ≤ x.R.Kw + x.c.Dm - 1 := by
      have hh := (Finset.mem_Icc.mp d.2).2.trans x.c.order_ge
      omega
    simp only [F, dite_eq_left hd]
  rw [hfull, hlow]
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans x.c.order_ge⟩
  · intro d hd hnot
    have ho : x.order < d := by
      have hlow := (Finset.mem_Icc.mp hd).1
      simp only [Finset.mem_Icc, not_and, not_le] at hnot
      exact hnot hlow
    dsimp only [F]
    split_ifs
    · rw [weak_quiet_physical_above_cap x.c x.i x.level_lt.le x.level_le v u γ d ho]
      exact zero_apply _
    · rfl

/-- The quiet margin has strictly positive duration in the actual solution window. -/
theorem heat_window (x : WeakQuietExpansionCase plan prices) :
    x.left < x.right ∧ Set.Icc x.left x.right ⊆
      Set.Icc (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀) := by
  have he := x.bounds.1
  have hν := x.bounds.2.1
  have hlen : 0 < x.c.D.eps (x.i - 1) ^ 2 / x.c.D.κ x.c.M :=
    div_pos (sq_pos_of_pos he) hν
  exact ⟨sub_lt_self _ hlen, Set.Icc_subset_Icc x.bounds.2.2.1 x.quiet.2.1⟩

/-- The heat quiet margin is inside the trimmed middle half used by the velocity
identity. No statement about the untrimmed quiet region is needed. -/
theorem heat_middle_half (x : WeakQuietExpansionCase plan prices) :
    Set.Icc x.left x.right ⊆ weakMiddleHalf x.c x.run x.i :=
  Set.Icc_subset_Icc x.bounds.2.2.2.1 le_rfl

/-- The literal drift of the stage agrees with the parent drift throughout
its heat quiet margin. -/
theorem heat_velocity_eq (x : WeakQuietExpansionCase plan prices) (t : ℝ)
    (ht : t ∈ Set.Icc x.left x.right) :
    streamVel (x.c.D.Φ x.i) t = streamVel (x.c.D.Φ (x.i - 1)) t :=
  weak_middle_half_velocity_eq x.c x.run x.i x.level_lt x.quiet t (x.heat_middle_half ht)

/-- Every nonroot row is the genuinely solved output of the next passage.
The first source of the reduction is thus included, not treated as an
unjustified homogeneous row. -/
theorem stage_solution (x : WeakQuietExpansionCase plan prices)
    (htop : x.i < x.c.M + x.A.Jw) :
    ∃ f : ∀ _v : x.Vertex, TorusHk x.R.Kw ℝ,
      (x.c.stage x.i).IsRegSolution x.c.P (fun _ => isoPairedKernel 0 x.R.nW)
        (fun _ => isoPairedKernel 0 x.R.nW) x.A.φ₀ x.A.hφ₀
        (x.c.D.κ x.c.M) (streamVel (x.c.D.Φ x.i)) x.R.Kw
        (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀) f
        (fun _ _ => 0) (fun _ _ => 0) (x.run.Ur x.i) (x.run.Urw x.i) (x.run.Urk x.i) := by
  have hp := (x.run.reduction.2.2.2 (x.i + 1) (by have := x.level_lt; omega)
    (by omega)).2.2.2.2.2
  simp only [IsWeakPassageSolution, Nat.add_sub_cancel] at hp
  obtain ⟨f, _, hs⟩ := hp
  have hl := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ x.c.construction
    x.i x.level_lt.le x.level_le
  rw [hl, weak_passage_kap_eq x.c x.i x.level_lt.le] at hs
  exact ⟨f, hs⟩

end WeakQuietExpansionCase

/-- The literal incoming flux of a scalar weak stage and its supplied kernel
carriers. No high-order regularizer estimate is used at width zero. -/
def weakQuietKernelRawFlux {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ K : ℕ}
    (G : GenStage D ScalarH Dm bw j₀)
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (K + Dm - 1) ℝ)
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
  ∑ u, ∑ γ : G.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dm),
    G.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (Y v u γ t).toFunction.jet ⟨⟨d.1 - 1, by
        have := Finset.mem_Icc.1 d.2
        omega⟩, word⟩ x)

/-- Each incoming physical flux has a genuine L² native carrier.
The high inputs are exactly the supplied kernel carriers, and no constituent
or physical order is discarded. -/
theorem weak_quiet_kernel_incoming_flux_exists {D : OCData} {Dm : ℕ} {bw : ℝ}
    {j₀ K J : ℕ} {ε a b : ℝ} (hε : 0 < ε)
    (G : GenStage D ScalarH Dm bw j₀)
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (K + Dm - 1) ℝ)
    (hY : ∀ v u γ, MemLp (Y v u γ) 2 (volume.restrict (Set.Icc a b)))
    (hfin : ∀ v u γ (d : ↥(Finset.Icc 2 Dm)),
      coefficientSeminorm ε J a b (G.physCoeff v u γ d.1) ≠ ⊤)
    (hm : ∀ v u γ (d : ↥(Finset.Icc 2 Dm)),
      Measurable (fun p : Set.Icc a b × Vec 2 => G.physCoeff v u γ d.1 p.1 p.2))
    (hc : ∀ v u γ (d : ↥(Finset.Icc 2 Dm)) t, t ∈ Set.Icc a b →
      ContDiff ℝ (0 : ℕ) (G.physCoeff v u γ d.1 t))
    (hp : ∀ v u γ (d : ↥(Finset.Icc 2 Dm)) t, t ∈ Set.Icc a b →
      AVenhance.IsZ2Periodic (G.physCoeff v u γ d.1 t)) :
    ∃ Q : CompIn G.comps → CompIn G.comps → ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)),
      (∀ v u, MemLp (Q v u) 2 (volume.restrict (Set.Icc a b))) ∧
      ∀ v u t, t ∈ Set.Icc a b →
        (Q v u t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
          fun x => ∑ γ : G.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dm),
            G.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (Y v u γ t).toFunction.jet ⟨⟨d.1 - 1, by
                have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
  classical
  let low (d : ↥(Finset.Icc 2 Dm)) : 0 + (d.1 - 1) ≤ K + Dm - 1 := by
    have := Finset.mem_Icc.1 d.2
    omega
  let term (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) :=
    weakQuietSourceFluxCurve (Nat.zero_le J) hε (G.physCoeff v u γ d.1)
      (hfin v u γ d) (hc v u γ d) (hp v u γ d)
      (fun t => truncateTorusHk (low d) (Y v u γ t))
  refine ⟨fun v u t => ∑ γ : G.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dm),
    term v u γ d t, ?_, ?_⟩
  · intro v u
    have hd (γ : G.fam.Γ v u) :
        MemLp (fun t => ∑ d : ↥(Finset.Icc 2 Dm), term v u γ d t) 2
          (volume.restrict (Set.Icc a b)) :=
      memLp_finsetSum Finset.univ (f := fun d => term v u γ d) (fun d _ =>
        weak_quiet_source_flux_curve_memLp (Nat.zero_le J) hε
          (G.physCoeff v u γ d.1) (hfin v u γ d) (hc v u γ d) (hp v u γ d)
          (hm v u γ d) _ ((truncateTorusHk (low d)).comp_memLp' (hY v u γ)))
    exact memLp_finsetSum Finset.univ
      (f := fun γ t => ∑ d : ↥(Finset.Icc 2 Dm), term v u γ d t)
      (fun γ _ => hd γ)
  · intro v u t ht
    apply KernelEnergy.torusJet_sum_ae_of_eq
    intro γ
    apply KernelEnergy.torusJet_sum_ae_of_eq
    intro d
    have hb := weak_quiet_source_flux_curve_value_ae (Nat.zero_le J) hε
      (G.physCoeff v u γ d.1) (hfin v u γ d) (hc v u γ d) (hp v u γ d)
      (fun t => truncateTorusHk (low d) (Y v u γ t)) t ht
    have hj : ∀ᵐ x ∂volume.restrict unitCube, ∀ word : DerivativeWord2 (d.1 - 1),
        (truncateTorusHk (low d) (Y v u γ t)).toFunction.jet
          ⟨⟨d.1 - 1, by omega⟩, word⟩ x =
        (Y v u γ t).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x :=
      ae_all_iff.mpr fun word => KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (low d) (Y v u γ t) _
    filter_upwards [hb, hj] with x hx hjx
    exact hx.trans (congrArg (G.physCoeff v u γ d.1 t x) (PiLp.ext fun word => hjx word))

private theorem weakQuietKernelIdentity_lower {K : ℕ} {ν a b t : ℝ}
    {v : ℝ → Vec 2 → Vec 2} (ht : t ∈ Set.Icc a b)
    (U f : TorusHk K ℝ) (W : ℝ → TorusHk (K + 1) ℝ)
    (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℝ))
    (Q : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hQ : ∀ s ∈ Set.Icc a b,
      (Q s).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] flux s)
    (ψ : TorusHk 1 ℝ)
    (hold : CoupledWeakIdentity (volume.restrict unitCube) ν a t v
      (U.toFunction.jet (valueIndex2 K)) (f.toFunction.jet (valueIndex2 K))
      (ψ.toFunction.jet (valueIndex2 1))
      (fun q => ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
      (fun s q => (W s).toFunction.jet ⟨⟨1, by omega⟩, fun _ => q⟩)
      flux (fun _ => (0 : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet
        (valueIndex2 K))
      (fun _ => (0 : TorusHk K ℝ).toFunction.jet (valueIndex2 K))) :
    CoupledWeakIdentity (volume.restrict unitCube) ν a t v
      ((truncateTorusHk (Nat.zero_le K) U).toFunction.jet (valueIndex2 0))
      ((truncateTorusHk (Nat.zero_le K) f).toFunction.jet (valueIndex2 0))
      (ψ.toFunction.jet (valueIndex2 1))
      (fun q => ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
      (fun s q => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) (W s)).toFunction.jet
        ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
      (fun _ _ => 0) (fun s => (Q s).toFunction.jet (valueIndex2 0))
      (fun _ => (0 : TorusHk 0 ℝ).toFunction.jet (valueIndex2 0)) := by
  refine CycleJointProofs.coupledWeakIdentity_integrands_congr
    (volume.restrict unitCube) ν a t v v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ hold
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
      (Nat.zero_le K) U (valueIndex2 0)] with x hx
    exact congrArg (fun z => inner ℝ z _) hx.symm
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
      (Nat.zero_le K) f (valueIndex2 0)] with x hx
    exact congrArg (fun z => inner ℝ z _) hx.symm
  · intro s hs'
    have hsb : s ∈ Set.Icc a b := ⟨hs'.1.le, hs'.2.trans ht.2⟩
    filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (Nat.succ_le_succ (Nat.zero_le K)) (W s)
        ⟨⟨1, by omega⟩, fun _ => 0⟩,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (Nat.succ_le_succ (Nat.zero_le K)) (W s)
        ⟨⟨1, by omega⟩, fun _ => 1⟩,
      hQ s hsb,
      CycleJointProofs.torusZero_rawJet_ae
        (E := PiLp 2 (fun _ : Fin 2 => ℝ)) K (valueIndex2 K),
      CycleJointProofs.torusZero_rawJet_ae (E := ℝ) K (valueIndex2 K),
      CycleJointProofs.torusZero_rawJet_ae (E := ℝ) 0 (valueIndex2 0)]
      with x h0 h1 hflux hF hg hg'
    refine weakIdentityRhs_congr_at _ _ _ _ _ _ _ _ _ _ _ _ s x (fun q => ?_) ?_ ?_
    · fin_cases q
      · exact h0.symm
      · exact h1.symm
    · change flux s x + _ = 0 + _
      rw [hF, Pi.zero_apply, zero_add, add_zero, hflux]
    · exact hg.trans hg'.symm

/-- Extract the actual scalar forced row from a kernel solution once its full
incoming flux has been represented by a native H⁰ carrier. The right-hand
side is the original physical flux, not a majorant or a different system. -/
theorem weak_quiet_kernel_native_row {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ K : ℕ}
    (G : GenStage D ScalarH Dm bw j₀) (P : ProvParams) (n : ℕ+)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) {ν a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ _w : CompIn G.comps, TorusHk K ℝ}
    {U : ∀ _w : CompIn G.comps, ℝ → TorusHk K ℝ}
    {W : ∀ _w : CompIn G.comps, ℝ → TorusHk (K + 1) ℝ}
    {Y : ∀ w u (_ : G.fam.Γ w u), ℝ → TorusHk (K + Dm - 1) ℝ}
    (hs : G.IsRegSolution P (fun _ => isoPairedKernel 0 n)
      (fun _ => isoPairedKernel 0 n) φ₀ hφ₀ ν v K a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (w : CompIn G.comps) (Q : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hQ : ∀ t ∈ Set.Icc a b,
      (Q t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
        weakQuietKernelRawFlux G Y w t) :
    IsTorusForcedRow ν a b v 2 0 (truncateTorusHk (Nat.zero_le K) (f w)) Q
      (fun _ => 0) (fun t => truncateTorusHk (Nat.zero_le K) (U w t))
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) (W w t)) := by
  refine isTorusForcedRow_of
    (truncate_continuousOn (Nat.zero_le K) (hs.1 w))
    (truncate_memLp (Nat.succ_le_succ (Nat.zero_le K)) (hs.2.1 w))
    (truncate_lift_ae (Nat.zero_le K) (hs.2.2.1 w))
    (congrArg (truncateTorusHk (Nat.zero_le K)) (hs.2.2.2.1 w)) ?_
  intro t ht ψ
  have hold := hs.2.2.2.2.2.2 w t ht ψ
  exact weakQuietKernelIdentity_lower ht (U w t) (f w) (W w)
    (weakQuietKernelRawFlux G Y w) Q hQ ψ hold

/-- At width zero the supplied high carrier has exactly the row's value.
No assertion that convolution of width zero gains derivatives is involved:
the high carrier is part of the given solution class. -/
theorem weak_quiet_kernel_input_value {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ K : ℕ}
    (G : GenStage D ScalarH Dm bw j₀) (P : ProvParams) (n : ℕ+)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (hmass : ∫ z, φ₀ z = 1)
    {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ _w : CompIn G.comps, TorusHk K ℝ}
    {U : ∀ _w : CompIn G.comps, ℝ → TorusHk K ℝ}
    {W : ∀ _w : CompIn G.comps, ℝ → TorusHk (K + 1) ℝ}
    {Y : ∀ w u (_ : G.fam.Γ w u), ℝ → TorusHk (K + Dm - 1) ℝ}
    (hs : G.IsRegSolution P (fun _ => isoPairedKernel 0 n)
      (fun _ => isoPairedKernel 0 n) φ₀ hφ₀ ν v K a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (w u : CompIn G.comps) (γ : G.fam.Γ w u) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (Y w u γ t).val (valueIndex2 (K + Dm - 1)) = (U u t).val (valueIndex2 K) := by
  have hid (z : Lp ℝ 2 (volume.restrict unitCube)) :
      (ContinuousLinearMap.id ℝ ℝ).compLp z = z :=
    Lp.ext ((ContinuousLinearMap.coeFn_compLp' _ z).trans
      (Filter.Eventually.of_forall fun _ => rfl))
  filter_upwards [hs.2.2.1 u, hs.2.2.2.2.2.1 w u γ] with t ht hy
  rw [Providers.WeakGen.sysS_isoPairedKernel_zero P n hφ₀ hmass G w u γ t,
    ContinuousLinearMap.id_apply, hid] at hy
  exact hy.trans (congrArg (fun z : TorusHk K ℝ => z.val (valueIndex2 K)) ht)

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.WeakEntryProofs.Assembly

/-! One genuine Duhamel insertion. The source is the actual coefficient times
an ordered derivative of the supplied high carrier. Integration by parts uses
its formal adjoint and the native moving scalar test. -/

/-- The defining smooth-test identity determines every native formal adjoint.
Its arbitrary unweighted norm constant does not affect the physical operator. -/
theorem weak_quiet_formal_adjoint_unique {m R R' Kc Kc' P : ℕ} {C C' : ℝ}
    {T : (Vec 2 → ℝ) → Vec 2 → ℝ}
    (A : TorusAdj T m R Kc C) (B : TorusAdj T m R' Kc' C')
    (hP : P + m ≤ Kc) (hP' : P + m ≤ Kc') :
    A.adj P hP = B.adj P hP' := by
  apply ContinuousLinearMap.ext
  intro φ
  apply torusHk_eq_of_cellInner
  intro ψ hψ hp
  rw [A.ident P hP φ ψ (hψ.of_le (by simp)) hp,
    B.ident P hP' φ ψ (hψ.of_le (by simp)) hp]

/-- Lowering the test reserve commutes with a genuine formal adjoint. Its
smooth-test identity determines the order-zero value, independently of the
chosen graph-space realization. -/
theorem weak_quiet_formal_adjoint_truncate {m R Kc P Q : ℕ} {C : ℝ}
    {T : (Vec 2 → ℝ) → Vec 2 → ℝ} (A : TorusAdj T m R Kc C)
    (hPQ : P ≤ Q) (hQ : Q + m ≤ Kc) (φ : TorusHk (Q + m) ℝ) :
    truncateTorusHk hPQ (A.adj Q hQ φ) =
      A.adj P ((Nat.add_le_add_right hPQ m).trans hQ)
        (truncateTorusHk (Nat.add_le_add_right hPQ m) φ) := by
  apply torusHk_eq_of_cellInner
  intro ψ hψ hp
  have hl := A.ident Q hQ φ ψ (hψ.of_le (by simp)) hp
  have hr := A.ident P ((Nat.add_le_add_right hPQ m).trans hQ)
    (truncateTorusHk (Nat.add_le_add_right hPQ m) φ) ψ (hψ.of_le (by simp)) hp
  rw [tval_truncateTorusHk, hl, hr, tval_truncateTorusHk]

/-- The actual aggregate insertion commutes with lowering its test reserve.
Its coefficient normalization is retained in the formal adjoint witness. -/
theorem weak_quiet_insertion_truncate {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (v u : x.Vertex) {P Q : ℕ}
    (hPQ : P ≤ Q) (hQ : Q + x.order ≤ x.cap) (t : ℝ)
    (ht : t ∈ Set.Icc x.left x.right) (φ : TorusHk (Q + x.order) ℝ) :
    truncateTorusHk hPQ (S.apply v u Q hQ t φ) =
      S.apply v u P ((Nat.add_le_add_right hPQ x.order).trans hQ) t
        (truncateTorusHk (Nat.add_le_add_right hPQ x.order) φ) := by
  obtain ⟨C, A, he, _⟩ := S.adjoint v u t ht
  rw [he Q hQ, he P ((Nat.add_le_add_right hPQ x.order).trans hQ)]
  exact weak_quiet_formal_adjoint_truncate A hPQ hQ φ

/-- A native forced scalar row gives Duhamel's formula for any actual source
pairing. The flux and the moving gradient are square integrable; hence the
source pairing is integrable before it is used in the identity. -/
theorem weak_quiet_forced_duhamel {P D : ℕ} {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} (hab : a ≤ b)
    (hd : WeakScalarTorusDrift ν ρ a b v P)
    {F : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))}
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    {f : TorusHk 0 ℝ} {u : ℝ → TorusHk 0 ℝ} {w : ℝ → TorusHk 1 ℝ}
    (hs : IsTorusForcedRow ν a b v D 0 f F (fun _ => 0) u w)
    {φ : TorusHk P ℝ} {z : ℝ → TorusHk P ℝ} {zw : ℝ → TorusHk (P + 1) ℝ}
    (hz : WeakScalarTorusSolution ν (-b) (-a) (fun t x => -v (-t) x) P φ z zw)
    {q : ℝ → ℝ}
    (hpair : q =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      -inner ℝ (torusHkValueCLM (F t))
        (torusH1GradientL2CLM (E := ℝ)
          (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t))))) :
    IntervalIntegrable q volume a b ∧
    inner ℝ (u b) (truncateTorusHk (Nat.zero_le P) φ) =
      inner ℝ (u a) (truncateTorusHk (Nat.zero_le P) (z (-a))) +
        ∫ t in a..b, q t := by
  let g := fun t => inner ℝ (torusHkValueCLM (F t))
    (torusH1GradientL2CLM (E := ℝ)
      (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t))))
  have hgi : IntervalIntegrable g volume a b :=
    weak_scalar_forced_test_integrable hab hF (hz.2.1 0)
  have hqi : IntervalIntegrable q volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hgi).neg.congr hpair.symm)
  refine ⟨hqi, ?_⟩
  have he := weak_scalar_forced_adjoint_pair P hab hd hF hs hz
  have hi : (∫ t in a..b, q t) = -(∫ t in a..b, g t) := by
    rw [intervalIntegral.integral_congr_ae_restrict (by
      simpa only [Set.uIoc_of_le hab] using
        hpair.filter_mono (ae_mono (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))),
      intervalIntegral.integral_neg]
  have hinit : z (-b) = φ := hz.2.2.2.1 0
  rw [hinit] at he
  change _ - _ = -(∫ t in a..b, g t) at he
  linarith only [he, hi]

/-- A finite family of genuine incoming L² fluxes may be summed in the moving
scalar pairing. Integrability is established for each normalized summand before
commuting the finite sum with the time integral. -/
theorem weak_quiet_forced_sum_duhamel {ι : Type} [Fintype ι]
    {P D : ℕ} {ν ρ a b σ : ℝ} {v : ℝ → Vec 2 → Vec 2} (hab : a ≤ b)
    (hd : WeakScalarTorusDrift ν ρ a b v P)
    {F : ι → ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    {f : TorusHk 0 ℝ} {u : ℝ → TorusHk 0 ℝ} {w : ℝ → TorusHk 1 ℝ}
    (hs : IsTorusForcedRow ν a b v D 0 f (fun t => ∑ i, F i t) (fun _ => 0) u w)
    {φ : TorusHk P ℝ} {z : ℝ → TorusHk P ℝ} {zw : ℝ → TorusHk (P + 1) ℝ}
    (hz : WeakScalarTorusSolution ν (-b) (-a) (fun t y => -v (-t) y) P φ z zw)
    {q : ι → ℝ → ℝ}
    (hpair : ∀ i, q i =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      -σ * inner ℝ (torusHkValueCLM (F i t))
        (torusH1GradientL2CLM (E := ℝ)
          (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t))))) :
    (∀ i, IntervalIntegrable (q i) volume a b) ∧
    σ * inner ℝ (u b) (truncateTorusHk (Nat.zero_le P) φ) =
      σ * inner ℝ (u a) (truncateTorusHk (Nat.zero_le P) (z (-a))) +
        ∑ i, ∫ t in a..b, q i t := by
  classical
  have hqi (i : ι) : IntervalIntegrable (q i) volume a b := by
    have hg := weak_scalar_forced_test_integrable hab (hF i) (hz.2.1 0)
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (hg.const_mul (-σ))).congr (hpair i).symm
  refine ⟨hqi, ?_⟩
  have hsum : MemLp (fun t => ∑ i, F i t) 2 (volume.restrict (Set.Icc a b)) :=
    memLp_finsetSum Finset.univ (f := F) (fun i _ => hF i)
  have he := (weak_quiet_forced_duhamel hab hd hsum hs hz
    (Filter.EventuallyEq.rfl)).2
  have hi : (∑ i, ∫ t in a..b, q i t) =
      σ * ∫ t in a..b, -inner ℝ (torusHkValueCLM (∑ i, F i t))
        (torusH1GradientL2CLM (E := ℝ)
          (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le P)) (zw (-t)))) := by
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hqi i),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae_restrict
    have hpa := (Filter.eventually_all_finset Finset.univ).mpr (fun i _ => hpair i)
    rw [Set.uIoc_of_le hab]
    filter_upwards [hpa.filter_mono (ae_mono
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))] with t ht
    simp only [map_sum, sum_inner]
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ht i hi]
    ring
  rw [hi, he, mul_add]

/-- Raising an insertion to the common weak differential order preserves its
native pairing with the actual incoming flux. Only the test is truncated. -/
theorem weak_quiet_source_adjoint_lift_pair {J r m R Kc : ℕ} {ε a b C : ℝ}
    (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (1 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (Adj : TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc C)
    (hm : r + 1 ≤ m) (hP : 0 + m ≤ Kc) (u : TorusHk (0 + r) ℝ)
    (φ : TorusHk (0 + m) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le (0 + r)) u)
      ((Adj.liftOrder hm).adj 0 hP φ) =
    -inner ℝ (torusHkValueCLM (weakQuietSourceFlux (Nat.zero_le J) ε hε a b A hA t ht
      (hC.of_le (by simp)) hp u))
      (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ)) := by
  have hh := weak_quiet_source_native_pair hε A hA t ht hC hp Adj
    (by omega : 0 + (r + 1) ≤ Kc) u
    (truncateTorusHk (Nat.add_le_add_left hm 0) φ)
  exact hh

/-- The aggregate formal source pairs with the literal sum of the actual
physical fluxes. Separate supplied carriers may be used for each constituent:
the zero-width kernel relation only has to identify their order-zero values. -/
theorem weak_quiet_source_sum_native_pair {ι : Type} [Fintype ι]
    {J m R R' Kc Kc' : ℕ} {ε a b t C : ℝ} (hε : 0 < ε)
    (ht : t ∈ Set.Icc a b) (hm : 1 ≤ m) (r : ι → ℕ) (hr : ∀ i, r i + 1 ≤ m)
    (A : ∀ i, ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (r i) => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : ∀ i, coefficientSeminorm ε J a b (A i) ≠ ⊤)
    (hc : ∀ i, ContDiff ℝ (1 : ℕ) (A i t))
    (hp : ∀ i, AVenhance.IsZ2Periodic (A i t))
    (Ci : ι → ℝ)
    (Ai : ∀ i, TorusAdj (weakQuietPrimalSource (r i) (A i t)) (r i + 1) R Kc (Ci i))
    (Adj : TorusAdj (fun ψ y => ∑ i, weakQuietPrimalSource (r i) (A i t) ψ y)
      m R' Kc' C)
    (hcap : 0 + m ≤ Kc) (hcap' : 0 + m ≤ Kc')
    (u : ∀ i, TorusHk (0 + r i) ℝ) (u0 : TorusHk 0 ℝ)
    (hu : ∀ i, truncateTorusHk (Nat.zero_le (0 + r i)) (u i) = u0)
    (φ : TorusHk (0 + m) ℝ) :
    inner ℝ u0 (Adj.adj 0 hcap' φ) =
      -inner ℝ (∑ i, torusHkValueCLM
        (weakQuietSourceFlux (Nat.zero_le J) ε hε a b (A i) (hA i) t ht
          ((hc i).of_le (by simp)) (hp i) (u i)))
        (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ)) := by
  classical
  let As := TorusAdj.sum Finset.univ (fun i => (Ai i).liftOrder (hr i))
  have heq := weak_quiet_formal_adjoint_unique Adj As hcap' hcap
  rw [heq]
  change inner ℝ u0 ((∑ i, ((Ai i).liftOrder (hr i)).adj 0 hcap) φ) = _
  rw [sum_apply, inner_sum, sum_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hu i]
  exact weak_quiet_source_adjoint_lift_pair hε (A i) (hA i) t ht (hc i) (hp i)
    (Ai i) (hr i) hcap (u i) φ

/-- Mass conjugation acts on the genuine aggregate source pairing by its
literal square-root ratio. The high carriers still need only share their
order-zero value. -/
theorem weak_quiet_source_sum_scaled_native_pair {ι : Type} [Fintype ι]
    {J m R R' Kc Kc' : ℕ} {ε a b t C σ : ℝ} (hε : 0 < ε)
    (ht : t ∈ Set.Icc a b) (hm : 1 ≤ m) (r : ι → ℕ) (hr : ∀ i, r i + 1 ≤ m)
    (A : ∀ i, ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (r i) => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : ∀ i, coefficientSeminorm ε J a b (A i) ≠ ⊤)
    (hc : ∀ i, ContDiff ℝ (1 : ℕ) (A i t))
    (hp : ∀ i, AVenhance.IsZ2Periodic (A i t))
    (Ci : ι → ℝ)
    (Ai : ∀ i, TorusAdj (weakQuietPrimalSource (r i) (A i t)) (r i + 1) R Kc (Ci i))
    (Adj : TorusAdj (fun ψ y => σ * ∑ i, weakQuietPrimalSource (r i) (A i t) ψ y)
      m R' Kc' C)
    (hcap : 0 + m ≤ Kc) (hcap' : 0 + m ≤ Kc')
    (u : ∀ i, TorusHk (0 + r i) ℝ) (u0 : TorusHk 0 ℝ)
    (hu : ∀ i, truncateTorusHk (Nat.zero_le (0 + r i)) (u i) = u0)
    (φ : TorusHk (0 + m) ℝ) :
    inner ℝ u0 (Adj.adj 0 hcap' φ) =
      -σ * inner ℝ (∑ i, torusHkValueCLM
        (weakQuietSourceFlux (Nat.zero_le J) ε hε a b (A i) (hA i) t ht
          ((hc i).of_le (by simp)) (hp i) (u i)))
        (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ)) := by
  classical
  let As := TorusAdj.sum Finset.univ (fun i => (Ai i).liftOrder (hr i))
  have hh := weak_quiet_source_sum_native_pair hε ht hm r hr A hA hc hp Ci Ai As
    hcap hcap u u0 hu φ
  have heq := weak_quiet_formal_adjoint_unique Adj (As.smul σ) hcap' hcap
  rw [heq]
  change inner ℝ u0 (σ • As.adj 0 hcap φ) = _
  rw [real_inner_smul_right, hh]
  ring

end AVRegularity.WeakEntryProofs.Assembly
end
