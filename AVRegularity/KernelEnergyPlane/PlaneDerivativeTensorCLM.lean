-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.CouplingBounds
public import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
public import AVRegularity.KernelEnergy.TorusGraphProjection
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
public import AVRegularity.KernelEnergy.TorusMultiplierCLM
public import AVRegularity.CoupledEnergyPlane.CarrierMapOperator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.Pi

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.KernelEnergyPlane

/-! Finite-family Bochner convergence from the genuine component spaces. -/

variable {T ι : Type*} [MeasurableSpace T] [Fintype ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

theorem timeFamily_cutoff_sum (μ : Measure T) (L : ∀ i, E i →L[ℝ] E i)
    (U : Lp (∀ i, E i) 2 μ) :
    (ContinuousLinearMap.pi (fun i => (L i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := E) i))).compLpL 2 μ U =
      ∑ i, (ContinuousLinearMap.single ℝ E i).compLpL 2 μ
        ((L i).compLpL 2 μ ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U)) := by
  classical
  apply Lp.ext
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i =>
    (ContinuousLinearMap.single ℝ E i).compLpL 2 μ
      ((L i).compLpL 2 μ ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U)))
  have he (i : ι) := ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.single ℝ E i)
    ((L i).compLpL 2 μ ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U))
  have hl (i : ι) := ContinuousLinearMap.coeFn_compLpL (L i)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U)
  have hp (i : ι) := ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) U
  filter_upwards [hs, ae_all_iff.mpr he, ae_all_iff.mpr hl, ae_all_iff.mpr hp,
    ContinuousLinearMap.coeFn_compLpL
      (ContinuousLinearMap.pi (fun i => (L i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := E) i))) U]
    with t hs he hl hp hu
  rw [hu, hs]
  simp only [Finset.sum_apply, he, hl, hp, ContinuousLinearMap.single_apply,
    ContinuousLinearMap.proj_apply,
    Finset.univ_sum_single]
  rfl

theorem timeFamily_cutoff_tendsto (μ : Measure T) (L : ∀ i, ℕ → E i →L[ℝ] E i)
    (U : Lp (∀ i, E i) 2 μ)
    (hc : ∀ i, Tendsto (fun N => (L i N).compLpL 2 μ
      ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U)) atTop
      (𝓝 ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U))) :
    Tendsto (fun N =>
      (ContinuousLinearMap.pi (fun i => (L i N).comp (ContinuousLinearMap.proj (R := ℝ) (φ := E) i))).compLpL 2 μ U)
      atTop (𝓝 U) := by
  classical
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    (((ContinuousLinearMap.single ℝ E i).compLpL 2 μ).continuous.tendsto _).comp (hc i))
  have hid := timeFamily_cutoff_sum μ (fun i => ContinuousLinearMap.id ℝ (E i)) U
  have hid' : (ContinuousLinearMap.pi (fun i =>
      (ContinuousLinearMap.id ℝ (E i)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := E) i))) =
      ContinuousLinearMap.id ℝ (∀ i, E i) := by ext u i; rfl
  have hU : (ContinuousLinearMap.id ℝ (∀ i, E i)).compLpL 2 μ U = U := by
    apply Lp.ext
    exact ContinuousLinearMap.coeFn_compLpL _ U
  have hcomp (i : ι) : (ContinuousLinearMap.id ℝ (E i)).compLpL 2 μ
      ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).compLpL 2 μ U := by
    apply Lp.ext
    exact ContinuousLinearMap.coeFn_compLpL _ _
  rw [hid', hU] at hid
  simp only [hcomp] at hid
  rw [← hid] at hsum
  simpa only [timeFamily_cutoff_sum, Function.comp_apply] using hsum

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace AVRegularity.KernelEnergyPlane

/-! Continuous linear images of convergent carriers identify a residual flux limit. -/

variable {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem timeResidualMinusCLM_tendsto (A B : J) (L : H →L[ℝ] J)
    (X : ℕ → H) (x : H) (hX : Tendsto X atTop (𝓝 x))
    (Y : ℕ → J) (hY : ∀ N, Y N = A) (hB : A - L x = B) :
    Tendsto (fun N => Y N - L (X N)) atTop (𝓝 B) := by
  have hleft : Tendsto Y atTop (𝓝 A) := by
    simpa only [funext hY] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A))
  have h := hleft.sub ((L.continuous.tendsto x).comp hX)
  simpa only [hB, Function.comp_apply] using h

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.KernelEnergyPlane

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E]

theorem timeSub_ae (μ : Measure T) (U V : Lp E 2 μ) :
    (U - V) =ᵐ[μ] fun t => U t - V t := Lp.coeFn_sub U V

theorem timeSubReadout_integral (μ : Measure T) (U V : Lp E 2 μ) (R : E → ℝ)
    (f g : T → E) (hf : U =ᵐ[μ] f) (hg : V =ᵐ[μ] g) :
    (∫ t, R ((U - V) t) ∂μ) = ∫ t, R (f t - g t) ∂μ := by
  apply integral_congr_ae
  filter_upwards [timeSub_ae μ U V, hf, hg] with t ht hf hg
  rw [ht, hf, hg]

theorem timeClass_sub_eq_of_ae_add (μ : Measure T) (U V W : Lp E 2 μ)
    (f g : T → E) (hU : U =ᵐ[μ] fun t => f t + g t)
    (hV : V =ᵐ[μ] g) (hW : W =ᵐ[μ] f) : U - V = W := by
  apply Lp.ext
  filter_upwards [timeSub_ae μ U V, hU, hV, hW] with t ht hU hV hW
  rw [ht, hU, hV, hW, add_sub_cancel_right]

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace AVRegularity.KernelEnergyPlane

/-! A contracting feedback in an equivalent readout norm has a fixed point
in the original complete space. The proof uses a contracting iterate,
as in the plane Volterra construction. -/

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem weightedFeedback_iterate_bound (L : E →L[ℝ] J) (T : E → E)
    (hc : ∀ x y, ‖L (T x - T y)‖ ≤ (1 / 2 : ℝ) * ‖L (x - y)‖)
    (n : ℕ) (x y : E) :
    ‖L (T^[n] x - T^[n] y)‖ ≤ (1 / 2 : ℝ) ^ n * ‖L (x - y)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (hc _ _).trans ((mul_le_mul_of_nonneg_left ih (by norm_num)).trans_eq
      (by rw [pow_succ]; ring))

theorem exists_weightedFeedback_fixedPoint [CompleteSpace E]
    (L : E →L[ℝ] J) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖x‖ ≤ M * ‖L x‖) (T : E → E)
    (hc : ∀ x y, ‖L (T x - T y)‖ ≤ (1 / 2 : ℝ) * ‖L (x - y)‖) :
    ∃ x, T x = x := by
  have ht : Tendsto (fun n : ℕ => M * (1 / 2 : ℝ) ^ n * ‖L‖) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [mul_zero, zero_mul] using (hp.const_mul M).mul_const ‖L‖
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds zero_lt_one)).exists
  let c : NNReal := ⟨M * (1 / 2 : ℝ) ^ n * ‖L‖,
    mul_nonneg (mul_nonneg hM (pow_nonneg (by norm_num) n)) (norm_nonneg _)⟩
  have hcontract : ContractingWith c (T^[n]) := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have h := (hb (T^[n] x - T^[n] y)).trans
      (mul_le_mul_of_nonneg_left (weightedFeedback_iterate_bound L T hc n x y) hM)
    have h' := mul_le_mul_of_nonneg_left (L.le_opNorm (x - y))
      (mul_nonneg hM (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n))
    exact (h.trans_eq (mul_assoc _ _ _).symm).trans (h'.trans_eq (by
      change M * (1 / 2 : ℝ) ^ n * (‖L‖ * ‖x - y‖) =
        (M * (1 / 2 : ℝ) ^ n * ‖L‖) * ‖x - y‖
      ring))
  exact ⟨hcontract.fixedPoint, hcontract.isFixedPt_fixedPoint_iterate⟩

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public section
namespace AVRegularity.KernelEnergyPlane

/-! Scalar absorption behind the kernel feedback and its uniqueness. -/

theorem kernelFeedback_quarter_bound (ν θ X Y Z : ℝ) (hν : 0 < ν)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 8) (hZ : 0 ≤ Z)
    (hX : X ≤ (ν * θ) ^ 2 * Y) (hY : Y ≤ (16 / ν ^ 2) * Z) :
    X ≤ (1 / 4 : ℝ) * Z := by
  have hθsq : 16 * θ ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hb : (ν * θ) ^ 2 * (16 / ν ^ 2) = 16 * θ ^ 2 := by
    field_simp
  calc
    X ≤ (ν * θ) ^ 2 * ((16 / ν ^ 2) * Z) :=
      hX.trans (mul_le_mul_of_nonneg_left hY (sq_nonneg _))
    _ = (16 * θ ^ 2) * Z := by rw [← mul_assoc, hb]
    _ ≤ _ := mul_le_mul_of_nonneg_right hθsq hZ

theorem kernelFeedback_gradient_eq_zero (ν θ X Y : ℝ) (hν : 0 < ν)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 8) (hX0 : 0 ≤ X)
    (hX : X ≤ (16 / ν ^ 2) * Y) (hY : Y ≤ (ν * θ) ^ 2 * X) : X = 0 := by
  have hθsq : 16 * θ ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hb : (16 / ν ^ 2) * (ν * θ) ^ 2 = 16 * θ ^ 2 := by field_simp
  have hi := hX.trans (mul_le_mul_of_nonneg_left hY
    (div_nonneg (by norm_num) (sq_nonneg _)))
  rw [← mul_assoc, hb] at hi
  have hi' := hi.trans (mul_le_mul_of_nonneg_right hθsq hX0)
  linarith

theorem kernelEnergy_perturbed_scalar (d E R G F M ν ε : ℝ)
    (hε : 0 < ε) (hR : 0 ≤ R) (hF : 0 ≤ F) (_hG : 0 ≤ G)
    (hM : Real.sqrt E ≤ M)
    (hd : d ≤ -(5 * ν / 4) * R + 2 * Real.sqrt G * Real.sqrt E +
      2 * Real.sqrt F * Real.sqrt R) :
    d + (5 * ν / 4 - ε) * R ≤ 2 * M * Real.sqrt G + (1 / ε) * F := by
  have hy := AVRegularity.coupledFluxYoung (show 0 < 4 * ε by positivity)
    (Real.sqrt F) (Real.sqrt R)
  rw [Real.sq_sqrt hR, Real.sq_sqrt hF] at hy
  have hb : 2 * Real.sqrt F * Real.sqrt R ≤ ε * R + (1 / ε) * F := by
    calc
      _ ≤ 2 * ((4 * ε / 8) * R + (2 / (4 * ε)) * F) := by linarith only [hy]
      _ = _ := by field_simp; ring
  have hg := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg G)
  linarith

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

variable {T J I : Type*} [MeasurableSpace T] [Fintype I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem assembleTimeFlux_zero_empty (μ : Measure T)
    {D : I → Type*} [∀ i, Fintype (D i)] [∀ i, IsEmpty (D i)]
    (G : Lp J 2 μ) (C : ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ) :
    assembleTimeFlux μ 0 G C F = F := by
  simp only [assembleTimeFlux, zero_smul, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.sum_const_zero, add_zero, zero_add]

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.KernelEnergyPlane

section
variable {T ι : Type*} [MeasurableSpace T] [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]

theorem timeFamily_input_memLp (μ : Measure T) (F : ∀ i, T → E i)
    (hF : ∀ i, MemLp (F i) 2 μ) (Z : Lp (∀ i, E i) 2 μ) (i : ι) :
    MemLp (fun t => F i t + Z t i) 2 μ :=
  AVRegularity.CoupledEnergy.Variational.timeMemLp_pointwise_add μ 2 (F i)
    (fun t => Z t i) (hF i) ((memLp_pi_iff.mp (Lp.memLp Z)) i)
end

/-! Readout of the bounded Bochner operator, before specializing its spaces. -/

section
open AVRegularity.KernelEnergy
variable {T H G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem timeOperatorCLM_action_ae (μ : Measure T) (L : T → H →L[ℝ] G)
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M) (U : Lp H 2 μ) :
    timeOperatorCLM μ L hL M hM hb U =ᵐ[μ] fun t => L t (U t) :=
  timeOperatorValue_ae μ L hL M hM hb U
end

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

variable {T H ι : Type*} [MeasurableSpace T] [Fintype ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

def timeOperatorComponent (μ : Measure T) (L : T → H →L[ℝ] (∀ i, G i))
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M) (i : ι) :
    Lp H 2 μ →L[ℝ] Lp (G i) 2 μ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := G) i).compLpL 2 μ).comp
    (timeOperatorCLM μ L hL M hM hb)

theorem timeOperatorComponent_ae (μ : Measure T) (L : T → H →L[ℝ] (∀ i, G i))
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M) (i : ι) (U : Lp H 2 μ) :
    timeOperatorComponent μ L hL M hM hb i U =ᵐ[μ] fun t => L t (U t) i := by
  have hp := ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.proj (R := ℝ) (φ := G) i)
    (timeOperatorCLM μ L hL M hM hb U)
  have hf := timeOperatorCLM_action_ae μ L hL M hM hb U
  filter_upwards [hp, hf] with t hp hf
  exact hp.trans (congrArg (fun q => q i) hf)

theorem timeOperatorComponent_readout_ae (μ : Measure T) (L : T → H →L[ℝ] (∀ i, G i))
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M) (i : ι)
    (U : Lp H 2 μ) (w : T → H) (hw : U =ᵐ[μ] w) :
    timeOperatorComponent μ L hL M hM hb i U =ᵐ[μ] fun t => L t (w t) i := by
  filter_upwards [timeOperatorComponent_ae μ L hL M hM hb i U, hw] with t ht hw
  exact ht.trans (congrArg (fun q => L t q i) hw)

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergyPlane

/-! Empty local coupling indices for the kernel equation's forced formulation. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {k : ℕ}

theorem noLocalOrders (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) : False := by
  have hd := Finset.mem_filter.1 d.property
  have := Finset.mem_Icc.1 hd.1
  omega

def noLocalCoefficient (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) :
    ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i) :=
  (noLocalOrders (k := k) i j d).elim

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Arithmetic of plane representatives, asserted almost everywhere.
The carrier arithmetic itself remains exact. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}

omit [FiniteDimensional ℝ E] in
theorem planeJet_add_ae (f g : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (f + g).toFunction.jet a =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => f.toFunction.jet a x + g.toFunction.jet a x := by
  have he : (f + g).val a = f.val a + g.val a := rfl
  filter_upwards [planeHk_toFunction_jet_ae (f + g) a, planeHk_toFunction_jet_ae f a,
    planeHk_toFunction_jet_ae g a, Lp.coeFn_add (f.val a) (g.val a)] with x hsum hf hg ha
  rw [hsum, he, ha, hf, hg]
  rfl

omit [FiniteDimensional ℝ E] in
theorem planeJet_smul_ae (q : ℝ) (f : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (q • f).toFunction.jet a =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => q • f.toFunction.jet a x := by
  have he : (q • f).val a = q • f.val a := rfl
  filter_upwards [planeHk_toFunction_jet_ae (q • f) a, planeHk_toFunction_jet_ae f a,
    Lp.coeFn_smul q (f.val a)] with x hsum hf ha
  rw [hsum, he, ha, hf]
  rfl

theorem planeCarrier_eq_of_value_ae (f g : PlaneHk Set.univ K E)
    (he : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      g.toFunction.jet (valueIndex2 K)) : f = g := by
  apply PlaneHk.ext_value isOpen_univ
  apply Lp.ext
  filter_upwards [planeHk_toFunction_jet_ae f (valueIndex2 K),
    planeHk_toFunction_jet_ae g (valueIndex2 K), he] with x hf hg hx
  exact hf.symm.trans (hx.trans hg)


omit [FiniteDimensional ℝ E] in
theorem planeJet_sum_ae {J : Type*} [Fintype J] (f : J → PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (∑ j, f j).toFunction.jet a =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => ∑ j, (f j).toFunction.jet a x := by
  have he : (∑ j, f j : PlaneHk Set.univ K E).val a = ∑ j, (f j).val a := by
    change (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : JetIndex2 K =>
      Lp E 2 (volume.restrict (Set.univ : Set (Vec 2)))) a)
      ((planeHkGraph (E := E) Set.univ K).toSubmodule.subtype (∑ j, f j)) = _
    rw [map_sum, map_sum]
    rfl
  have hj : ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)), ∀ j,
      (f j).toFunction.jet a x = (f j).val a x :=
    ae_all_iff.mpr (fun j => planeHk_toFunction_jet_ae (f j) a)
  filter_upwards [planeHk_toFunction_jet_ae (∑ j, f j) a,
    Lp.coeFn_fun_finsetSum Finset.univ (fun j => (f j).val a), hj] with x hx hsum hterms
  rw [hx, he, hsum]
  exact Finset.sum_congr rfl (fun j _ => (hterms j).symm)

omit [FiniteDimensional ℝ E] in
theorem planeJet_sum_ae_of_eq {J : Type*} [Fintype J]
    (f : J → PlaneHk Set.univ K E) (a : JetIndex2 K) (g : J → Vec 2 → E)
    (he : ∀ j, (f j).toFunction.jet a =ᵐ[volume.restrict (Set.univ : Set (Vec 2))] g j) :
    (∑ j, f j).toFunction.jet a =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => ∑ j, g j x := by
  filter_upwards [planeJet_sum_ae f a, ae_all_iff.mpr he] with x hx hj
  exact hx.trans (Finset.sum_congr rfl (fun j _ => hj j))
end

/-! Uniform factorial budgets for the zeroth and first mapped regularizer inputs. -/

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

private theorem mappedInput_factorial_bound (ρ : ℝ) (k : ℕ) (C : H →L[ℝ] G)
    (Z : PlaneHk Set.univ k H) {R : ℝ} (hR : 0 ≤ R) (hZ : ‖Z‖ ≤ R) :
    factorialNormSq ρ (mapPlaneHk C Z).val ≤
      ‖C‖ ^ 2 * factorialWeightMax ρ k * R ^ 2 := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  have hs : ‖Z.val‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg Z) hR).mpr hZ
  exact (mapPlaneHk_factorialNormSq_le ρ C Z).trans
    ((mul_le_mul_of_nonneg_left ((factorialNormSq_upper ρ Z.val).trans
      (mul_le_mul_of_nonneg_left hs hm)) (sq_nonneg ‖C‖)).trans_eq (mul_assoc _ _ _).symm)

theorem mappedLowerInput_factorial_bound (ρ : ℝ) (k : ℕ) (C : H →L[ℝ] G)
    (V : PlaneHk Set.univ (k + 1) H) :
    factorialNormSq ρ (mapPlaneHk C (truncatePlaneHk (Nat.le_succ k) V)).val ≤
      ‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2 :=
  mappedInput_factorial_bound ρ k C _ (norm_nonneg V) (truncatePlaneHk_norm_le _ V)

theorem mappedGradientInput_factorial_bound (ρ : ℝ) (k : ℕ) (C : H →L[ℝ] G)
    (V : PlaneHk Set.univ (k + 1) H) (q : Fin 2) :
    factorialNormSq ρ (mapPlaneHk C
      (derivativePlaneHk (K := k) (r := 1) (fun _ : Fin 1 => q) V)).val ≤
      ‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2 :=
  mappedInput_factorial_bound ρ k C _ (norm_nonneg V) (derivativePlaneHk_norm_le _ V)
end

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergyPlane

/-! The two committed plane fiber maps agree by uniqueness of their weak jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem kernelMapPlaneHkOperator_apply {K : ℕ} (L : E →L[ℝ] F) (u : PlaneHk Set.univ K E) :
    AVRegularity.CoupledEnergyPlane.mapPlaneHkOperator K L u = AVRegularity.KernelEnergy.mapPlaneHk L u := by
  rw [AVRegularity.CoupledEnergyPlane.mapPlaneHkOperator_apply]
  apply PlaneHk.ext_value isOpen_univ
  rw [AVRegularity.CoupledEnergyPlane.mapPlaneHk_component, AVRegularity.KernelEnergy.mapPlaneHk_jet_eq_compLp]

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Reuse the existing ordered derivative and fiber maps to bundle the
derivative tensor as one continuous linear map. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeKernelDerivativeTensorCLM (K r : ℕ) : PlaneHk Set.univ (K + r) E →L[ℝ]
    PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  ∑ w : DerivativeWord2 r,
    (AVRegularity.CoupledEnergyPlane.mapPlaneHkOperator K (tensorEntryCLM w)).comp
      (derivativePlaneHk w)

@[simp] theorem planeKernelDerivativeTensorCLM_apply (K r : ℕ) (u : PlaneHk Set.univ (K + r) E) :
    planeKernelDerivativeTensorCLM K r u = planeDerivativeTensor u := by
  simp only [planeKernelDerivativeTensorCLM, sum_apply, ContinuousLinearMap.comp_apply,
    kernelMapPlaneHkOperator_apply, planeDerivativeTensor, planeFamilyTensor]

end AVRegularity.KernelEnergyPlane
end
end
