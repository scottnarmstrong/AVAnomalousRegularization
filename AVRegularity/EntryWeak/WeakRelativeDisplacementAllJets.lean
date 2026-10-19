-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.ChildOperatorCloseness
public import AVRegularity.EntryWeak.MetricCloseEllipticity
import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
public import AVRegularity.CycleComparison.Lift.FiniteOperatorFinsetSynthesis
import AVRegularity.CycleReference.CoreFlux
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Genuine value-one reserves and centered scalar maps center every tested operator component. -/

variable {ι : Type*} [Fintype ι]

theorem scalarLiftApply_component_mean_zero (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (f : ℝ → Vec 2 → ι → ℝ)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v w,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v w 1))
    (hmean : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ t Y v w ξ,
      fieldCellMean (fun z => c m α t Y z v w ξ) = 0)
    (t : ℝ) (Y : Vec 2) (v : ι) :
    fieldCellMean (fun z => liftApply n c f t Y z v) = 0 := by
  have hc : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ w,
      Continuous (fun z => c m α t Y z v w) := by
    intro m hm α w
    exact (scalarCoefficient_goodField H m c α v w
      (Qc ⟨m, Nat.lt_succ_of_le hm⟩ α v w) t).continuous_slice Y
  exact liftApply_component_mean_zero_of_centered_coefficients
    (ι := ι) (h := fun _ => ℝ) n c f t Y v hc
    (fun m hm α w ξ => hmean m hm α t Y v w ξ)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A finer child window fits inside the enlarged parent renewal window. -/

theorem child_window_parent_distance {u s a h h' R : ℝ}
    (hR : 0 ≤ R) (hh : h' ≤ h) (hs : |s - a| ≤ 2 * h)
    (hu : |u - s| ≤ R * h') : |u - a| ≤ (R + 2) * h := by
  calc
    _ ≤ |u - s| + |s - a| := abs_sub_le _ _ _
    _ ≤ R * h + 2 * h := add_le_add
      (hu.trans (mul_le_mul_of_nonneg_left hh hR)) hs
    _ = _ := by ring

theorem child_window_operator_bound_of_parent_bound
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (k : ℕ) (pk : ℤ) (hpk : Odd pk) (s' : ℝ) (c : ChainChild)
    (g : ChainGeom) (hg : GeomSpatialSmooth g) (h h' R B : ℝ)
    (hh : 0 ≤ h) (hh' : h' ≤ h) (hR : 0 ≤ R)
    (ha : |s' - g.2.2| ≤ 2 * h)
    (hp : ∀ u r, |u - g.2.2| ≤ (R + 2) * h → |r - g.2.2| ≤ (R + 2) * h →
      ∀ x, ‖fderiv ℝ (fun y => g.1 u y r) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ B)
    (u r : ℝ) (hu : |u - s'| ≤ R * h') (hr : |r - s'| ≤ R * h') (x : Vec 2) :
    ‖fderiv ℝ (fun y => (D.childGeom k pk s' c g).1 u y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      (1 + B) ^ 2 * (1 + (2 * R * h') * ((4 * Real.pi ^ 2) * ocA D.α D.q D.Λ k)) - 1 := by
  have hu' := child_window_parent_distance hR hh' ha hu
  have hr' := child_window_parent_distance hR hh' ha hr
  have ha0 : |g.2.2 - g.2.2| ≤ (R + 2) * h := by
    rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hh
  have huj := hp u g.2.2 hu' ha0
  have hrj := hp g.2.2 r ha0 hr'
  have hc := childGeom_operator_close_of_parent_bounds D hΛ hζ k pk hpk s' c g hg
    u r B B huj hrj x
  have htime : |u - r| ≤ 2 * R * h' := by
    have ht := abs_sub_le u s' r
    have hr' : |s' - r| ≤ R * h' := by simpa only [abs_sub_comm] using hr
    linarith
  have hA : 0 ≤ (4 * Real.pi ^ 2) * ocA D.α D.q D.Λ k := by
    have he := Construction.Stream.ocEpsilon_pos (q := D.q) (n := k) hΛ
    unfold ocA
    exact mul_nonneg (by positivity) (Real.rpow_nonneg he.le _)
  have hb0 : 0 ≤ B := (norm_nonneg _).trans (huj x)
  apply hc.trans
  have ht := mul_le_mul_of_nonneg_right htime hA
  have ht' := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) ht)
    (sq_nonneg (1 + B))
  nlinarith [ht']

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Cutoff-independent temporal H¹ norm control for finite cell solutions. -/

/-- The finite cell energy estimate bounds the temporal H¹ norm independently of the cutoff. -/
theorem molecularFinite_bochner_norm_bound {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u du : ℝ → ComplexCellL2) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : MemLp (fun t => (y t).val) 2 (volume.restrict (Icc a b)))
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (molecularGeneratorB G v V hv hb t))
      (fun t => cellGalerkinSource N (cellSourceFunctional 0 (S t) (F t)).toLinearMap)
      u du y) :
    ‖hy.toLp (fun t => (y t).val)‖ ^ 2 ≤
      (b - a + 2) *
        ((‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2) *
          Real.exp ((1 + 8 * V ^ 2) * (b - a))) := by
  let R := (1 + 8 * V ^ 2)
  let budget := ‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2
  let E := budget * Real.exp (R * (b - a))
  let grad := fun s => ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hbgt : 0 ≤ budget := by
    have hi : 0 ≤ ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => by positivity)
    exact add_nonneg (sq_nonneg _) hi
  have he := molecularFinite_energy_bound hab N G v V hG hv hb S F hS hF u du y hy h
  have hucont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.time.norm_sq_ac.continuousOn
  have hug : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b :=
    hucont.intervalIntegrable_of_Icc hab
  have hgint : IntervalIntegrable grad volume a b :=
    cellTime_gradientSq_intervalIntegrable hab _ hy
  have hepoint : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ E := by
    intro t ht
    have het := he t ht
    have hd : 0 ≤ ∫ s in a..t, (1 / 2) * grad s :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => by dsimp only [grad]; positivity)
    have hex : Real.exp (R * (t - a)) ≤ Real.exp (R * (b - a)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hR
    have hm := mul_le_mul_of_nonneg_left hex hbgt
    dsimp only [E, R, budget, grad] at hd hm ⊢
    linarith
  have hegrad : (∫ s in a..b, grad s) ≤ 2 * E := by
    have heb := he b ⟨hab, le_rfl⟩
    change ‖u b‖ ^ 2 + (∫ s in a..b, (1 / 2) * grad s) ≤ E at heb
    rw [intervalIntegral.integral_const_mul] at heb
    nlinarith [sq_nonneg ‖u b‖]
  have heu : (∫ s in a..b, ‖u s‖ ^ 2) ≤ (b - a) * E := by
    have hm := intervalIntegral.integral_mono_on hab hug
      (continuous_const.intervalIntegrable a b) (fun s hs => hepoint s ⟨hs.1, hs.2⟩)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have hi : (∫ s in a..b, ‖(y s).val‖ ^ 2) =
      (∫ s in a..b, ‖u s‖ ^ 2) + ∫ s in a..b, grad s := by
    rw [← intervalIntegral.integral_add hug hgint]
    apply intervalIntegral.integral_congr_ae_restrict
    have ha := h.agrees.filter_mono (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
    filter_upwards [ha] with t ht
    rw [ht, cellH1_norm_sq]
    rfl
  have hn := cellTimeL2_norm_sq_integral (fun t => (y t).val) hy
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hi] at hn
  rw [hn]
  change (∫ s in a..b, ‖u s‖ ^ 2) + (∫ s in a..b, grad s) ≤ (b - a + 2) * E
  nlinarith

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Constant single-coordinate inputs produce each actual normalized exponential lift test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarSingleInputReserve (H : ℕ) (u w : ι) :
    JointSourceReserve H (fun (_ : ℝ) (_ _ : Vec 2) => (Pi.single u (1 : ℝ) : ι → ℝ) w) :=
  (JointSourceReserve.const H (if w = u then (1 : ℝ) else 0)).congrSource (by
    funext t z Y
    by_cases hw : w = u
    · simp only [hw, ite_true, Pi.single_eq_same]
    · simp only [ite_eq_right hw, Pi.single_eq_of_ne hw])

def normalizedScalarLiftTestReserve (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ w,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v w 1)) :
    JointSourceReserve H (fun t z Y => normalizedLiftTestField c n A u v 1 t Y z) :=
  normalizedLiftApplyComponentReserve H n c A
    (fun (_ : ℝ) (_ : Vec 2) => (Pi.single u (1 : ℝ) : ι → ℝ)) v Qc
    (fun w => scalarSingleInputReserve (H + n) u w)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

/-! Slow cutoffs extend weak incoming edges without changing their carrier germs. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def weakCutoffEdges (χ : Vec 2 → ℝ) (edge : ConstituentEdges D h) :
    ConstituentEdges D h :=
  fun v u d => (edge v u d).map fun γ =>
    { γ with
      coeff := fun α t X z => χ X • γ.coeff α t X z
      periodic := fun α t X k z => by simp only [γ.periodic α t X k z] }

def weakTimeClampEdges (a b : ℝ) (edge : ConstituentEdges D h) : ConstituentEdges D h :=
  fun v u d => (edge v u d).map fun γ =>
    { γ with
      coeff := fun α t X z => γ.coeff α (max a (min b t)) X z
      periodic := fun α t X k z => γ.periodic α (max a (min b t)) X k z }

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Finite child composition budgets vanish with the primitive chart error. -/

def finiteChartBudget : ℕ → ℝ → ℝ
  | 0, δ => δ
  | n + 1, δ => (1 + finiteChartBudget n δ) ^ 2 * (1 + δ) - 1

theorem finiteChartBudget_zero (n : ℕ) : finiteChartBudget n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteChartBudget, ih]; ring

theorem finiteChartBudget_nonneg (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ finiteChartBudget n δ := by
  induction n with
  | zero => exact hδ
  | succ n ih =>
    simp only [finiteChartBudget]
    have hs : 1 ≤ (1 + finiteChartBudget n δ) ^ 2 := by nlinarith
    have hp := mul_le_mul hs (show 1 ≤ 1 + δ by linarith) (by norm_num) (by positivity)
    nlinarith [hp]

theorem finiteChartBudget_continuous (n : ℕ) : Continuous (finiteChartBudget n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact (((continuous_const.add ih).pow 2).mul (continuous_const.add continuous_id)).sub
      continuous_const

theorem finiteChartBudget_mono_order {δ : ℝ} (hδ : 0 ≤ δ) :
    Monotone (fun n => finiteChartBudget n δ) := by
  apply monotone_nat_of_le_succ
  intro n
  have hb := finiteChartBudget_nonneg n hδ
  simp only [finiteChartBudget]
  nlinarith [mul_nonneg (sq_nonneg (1 + finiteChartBudget n δ)) hδ,
    sq_nonneg (finiteChartBudget n δ)]

theorem finiteChartBudget_small (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 32 ∧ finiteChartBudget n δ ≤ 1 / 32 := by
  have hc : ContinuousAt (finiteChartBudget n) 0 := (finiteChartBudget_continuous n).continuousAt
  obtain ⟨ε, hε, hb⟩ := Metric.continuousAt_iff.1 hc (1 / 32) (by norm_num)
  let δ := min (ε / 2) (1 / 64)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist δ 0 < ε := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδε
  have hh := hb hd
  rw [finiteChartBudget_zero, Real.dist_eq, sub_zero] at hh
  exact ⟨δ, hδ, (min_le_right _ _).trans (by norm_num), (le_abs_self _).trans hh.le⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Mixed native order lowering retains every inverse power of the parent length. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem transitionT_independent_slow_rescaled_eq
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (E : ℝ) (hE : 0 < E) (I A : List (Fin 2)) (hA : A.length ≤ I.length)
    (Z : P × Vec 2) :
    transitionT (K Z.1) I A (E • Z.2) = E⁻¹ ^ (I.length - A.length) *
      transitionT (fun y => K Z.1 (E • y)) I A Z.2 := by
  have hs a b : ContDiff ℝ (⊤ : ℕ∞) (fun y => K Z.1 y a b) :=
    (hK a b).comp (contDiff_const.prodMk contDiff_id)
  have hh := CycleJointProofs.transitionT_spatial_rescaling (K Z.1) hs E hE I A Z.2
  have hcount : (I.length : ℤ) - (A.length : ℤ) = ((I.length - A.length : ℕ) : ℤ) :=
    (Int.natCast_sub hA).symm
  rw [hh, hcount, zpow_natCast, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hE.ne', one_pow, one_mul]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Finite differential terms preserve genuine coefficient germs on an open slow carrier. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure LeftTermSlowEq (U : Set (Vec 2)) (c d : LeftTerm E F) : Prop where
  order : c.order = d.order
  word : HEq c.word d.word
  coeff : SlowOpenFieldEq U c.coeff d.coeff

variable {U : Set (Vec 2)} {c d : LeftTerm E F}

theorem LeftTermSlowEq.fastDerivative (he : LeftTermSlowEq U c d) (k : Fin 2) :
    LeftTermSlowEq U (c.fastDerivative k) (d.fastDerivative k) :=
  ⟨he.order, he.word, he.coeff.fastPartial k⟩

theorem LeftTermSlowEq.slowCoefficientDerivative (hU : IsOpen U)
    (he : LeftTermSlowEq U c d) (k : Fin 2) :
    LeftTermSlowEq U (c.slowCoefficientDerivative k) (d.slowCoefficientDerivative k) :=
  ⟨he.order, he.word, he.coeff.slowPartial hU k⟩

theorem LeftTermSlowEq.smul (he : LeftTermSlowEq U c d) (a : ℝ) :
    LeftTermSlowEq U (c.smul a) (d.smul a) := by
  refine ⟨he.order, he.word, ?_⟩
  intro X hX z
  exact congrArg (fun f : E →L[ℝ] F => a • f) (he.coeff X hX z)

theorem LeftTermSlowEq.slowInputDerivative (he : LeftTermSlowEq U c d) (k : Fin 2) :
    LeftTermSlowEq U (c.slowInputDerivative k) (d.slowInputDerivative k) := by
  rcases c with ⟨n, w, f⟩
  rcases d with ⟨n', w', g⟩
  rcases he with ⟨ho, hw, hf⟩
  dsimp only at ho hw hf
  subst n'
  have hww : w = w' := eq_of_heq hw
  subst w'
  exact ⟨rfl, HEq.rfl, hf⟩

theorem LeftTermSlowEq.fieldSmul (he : LeftTermSlowEq U c d) (a : Vec 2 → Vec 2 → ℝ) :
    LeftTermSlowEq U (c.fieldSmul a) (d.fieldSmul a) := by
  refine ⟨he.order, he.word, ?_⟩
  intro X hX z
  exact congrArg (fun f : E →L[ℝ] F => a X z • f) (he.coeff X hX z)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem LeftTermSlowEq.postcompose (he : LeftTermSlowEq U c d) (T : F →L[ℝ] G) :
    LeftTermSlowEq U (c.postcompose T) (d.postcompose T) := by
  refine ⟨he.order, he.word, ?_⟩
  intro X hX z
  exact congrArg (fun f : E →L[ℝ] F => T.comp f) (he.coeff X hX z)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

/-! Finite planar metric jets follow from chart entry jets without inverse denominators. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def planarGramJetBudget (n : ℕ) (C : ℝ) : ℝ :=
  2 * ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C * C

theorem planarGramJetBudget_nonneg (n : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ planarGramJetBudget n C := by
  unfold planarGramJetBudget
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun a _ => by positivity))

theorem planar_inverse_gram_derivative_bound
    (A : P → Matrix (Fin 2) (Fin 2) ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hdet : ∀ y, (A y).det = 1) (n : ℕ) (x : P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a ≤ n, ∀ i j, ‖iteratedFDeriv ℝ a (fun y => A y i j) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => (A y)⁻¹ * ((A y)⁻¹)ᵀ) x‖ ≤ planarGramJetBudget n C := by
  have hs (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ i j) := by
    have he : (fun y => (A y)⁻¹ i j) =
        fun y => (if i = j then 1 else -1) * A y j.rev i.rev :=
      funext (fun y => planar_inverse_entry_formula (A y) (hdet y) i j)
    rw [he]
    exact contDiff_const.mul ((contDiff_apply_apply ℝ ℝ j.rev i.rev).comp hA)
  have hi (a : ℕ) (ha : a ≤ n) (i j : Fin 2) :
      ‖iteratedFDeriv ℝ a (fun y => (A y)⁻¹ i j) x‖ ≤ C := by
    rw [planar_inverse_entry_derivative_norm A hdet i j a x]
    exact hb a ha j.rev i.rev
  have hp (i j k : Fin 2) :
      ‖iteratedFDeriv ℝ n (fun y => (A y)⁻¹ i k * (A y)⁻¹ j k) x‖ ≤
        ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C * C := by
    refine (norm_iteratedFDeriv_mul_le (hs i k) (hs j k) x (by simp)).trans ?_
    apply Finset.sum_le_sum
    intro a ha
    have ha' : a ≤ n := by have := Finset.mem_range.mp ha; omega
    have hia := hi a ha' i k
    have hja := hi (n - a) (Nat.sub_le _ _) j k
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hia (by positivity)) hja
      (norm_nonneg _) (by positivity)
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ * ((A y)⁻¹)ᵀ) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    exact ((hs i 0).mul (hs j 0)).add ((hs i 1).mul (hs j 1))
  apply matrix_derivative_norm_le_of_entries _ hG n x _ (planarGramJetBudget_nonneg n C hC)
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  change ‖iteratedFDeriv ℝ n
    ((fun y => (A y)⁻¹ i 0 * (A y)⁻¹ j 0) + fun y => (A y)⁻¹ i 1 * (A y)⁻¹ j 1) x‖ ≤ _
  rw [iteratedFDeriv_add_apply
    (((hs i 0).mul (hs j 0)).contDiffAt.of_le (by simp))
    (((hs i 1).mul (hs j 1)).contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans ((add_le_add (hp i j 0) (hp i j 1)).trans_eq (by
    unfold planarGramJetBudget
    ring))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Two units of parent-window reserve are spent at each child step. -/

def finiteChainWindowRadius (J n : ℕ) : ℝ := 2 * ((J - n : ℕ) : ℝ) + 1

theorem finiteChainWindowRadius_nonneg (J n : ℕ) : 0 ≤ finiteChainWindowRadius J n := by
  unfold finiteChainWindowRadius
  positivity

theorem finiteChainWindowRadius_le (J n : ℕ) : finiteChainWindowRadius J n ≤ 2 * (J : ℝ) + 1 := by
  unfold finiteChainWindowRadius
  have h : ((J - n : ℕ) : ℝ) ≤ J := by exact_mod_cast Nat.sub_le J n
  linarith

theorem finiteChainWindowRadius_succ (J n : ℕ) (hn : n + 1 ≤ J) :
    finiteChainWindowRadius J n = finiteChainWindowRadius J (n + 1) + 2 := by
  have h : J - n = (J - (n + 1)) + 1 := by omega
  unfold finiteChainWindowRadius
  rw [h, Nat.cast_add, Nat.cast_one]
  ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Genuine coefficient reserves give good and centered arbitrary smooth coarse tests. -/

variable {ι : Type*} [Fintype ι]

theorem scalarLiftSmoothTest_goodField (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v w,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v w 1)) (t : ℝ) :
    GoodField H (liftApply n c (fun _ => f) t) := by
  refine GoodField.of_forall_apply (h := fun _ : ι => ℝ) (fun v => ?_)
  simp only [liftApply]
  refine GoodField.sum _ (fun m hm => GoodField.sum _ (fun α _ => GoodField.sum _ (fun u _ => ?_)))
  let q := Qc ⟨m, Finset.mem_range.mp hm⟩ α v u
  have hc := scalarCoefficient_goodField H m c α v u q t
  have hg : ContDiff ℝ (H : ℕ∞) (fun X => orderedDerivative α f X u) :=
    (contDiff_pi.mp (orderedDerivative_contDiff α hf) u).of_le (by exact_mod_cast le_top)
  refine ⟨hc.1.clm_apply (hg.comp contDiff_fst), ?_⟩
  intro X k z
  exact congrArg (fun L : ℝ →L[ℝ] ℝ => L (orderedDerivative α f X u)) (hc.2 X k z)

theorem scalarLiftSmoothTest_centField (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v w,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v w 1))
    (hmean : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ t Y v w ξ,
      fieldCellMean (fun z => c m α t Y z v w ξ) = 0) (t : ℝ) :
    CoefField True H (liftApply n c (fun _ => f) t) := by
  let Φ := liftApply n c (fun _ => f) t
  have hg : GoodField H Φ := scalarLiftSmoothTest_goodField H n c f hf Qc t
  refine ⟨hg, ?_⟩
  intro _ Y
  funext v
  have hm : fieldCellMean (fun z => Φ Y z v) = 0 :=
    scalarLiftApply_component_mean_zero H n c (fun _ => f) Qc hmean t Y v
  exact (fieldCellMean_pi_apply (Φ Y) (hg.continuous_slice Y) v).symm.trans hm

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Finite uniform data bounds imply genuine Bochner Sobolev data. -/

theorem boundedCellSource_memLp {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (a b : ℝ) (f : ℝ → Vec 2 → E)
    (hm : Measurable (Function.uncurry f)) (B : ℝ) (hb : ∀ t x, ‖f t x‖ ≤ B) :
    MemLp (Function.uncurry f) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weak_unitCube_volume_lt_top⟩
  apply MemLp.of_bound hm.aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun p => hb p.1 p.2)

theorem complexFiniteJet_memLp (l : ℕ) (a b : ℝ) (q : ℝ → Vec 2 → ℝ)
    (hq : ∀ t, ContDiff ℝ (l : ℕ∞) (q t))
    (hm : Measurable (Function.uncurry q)) (Nq : ℝ)
    (hb : ∀ t j, j ≤ l → ∀ x, ‖iteratedFDeriv ℝ j (q t) x‖ ≤ Nq)
    (c : JetIndex2 l) :
    MemLp (fun p : ℝ × Vec 2 => complexFiniteJet l (q p.1) c p.2) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
  boundedCellSource_memLp a b (fun t x => complexFiniteJet l (q t) c x)
    (complexFiniteJet_joint_measurable l q hq hm c) Nq
    (fun t x => (complexFiniteJet_norm_le l (q t) (hq t) c x).trans
      (hb t c.1.val (Nat.le_of_lt_succ c.1.isLt) x))

theorem complexFiniteData_memLp (l : ℕ) (a b : ℝ) (q : ℝ → Vec 2 → ℝ)
    (hq : ∀ t, ContDiff ℝ (l : ℕ∞) (q t))
    (hm : Measurable (Function.uncurry q)) (Nq : ℝ)
    (hb : ∀ t j, j ≤ l → ∀ x, ‖iteratedFDeriv ℝ j (q t) x‖ ≤ Nq) :
    MemLp (dataHkSlice l (fun t => complexFiniteJet l (q t))) 2
      (volume.restrict (Set.Icc a b)) :=
  dataHkSlice_memLp l _ _ (complexFiniteJet_memLp l a b q hq hm Nq hb)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A jointly measurable representative with the same spatial classes retains product L². -/

theorem cellProduct_memLp_of_sections (I : Set ℝ) (f g : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : Measurable (Function.uncurry g))
    (he : ∀ᵐ t ∂volume.restrict I, f t =ᵐ[volume.restrict AVenhance.unitCube] g t) :
    MemLp (Function.uncurry g) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  let f' := hf.aestronglyMeasurable.mk (Function.uncurry f)
  have hfm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfe : Function.uncurry f =ᵐ[(volume.restrict I).prod (volume.restrict AVenhance.unitCube)] f' :=
    hf.aestronglyMeasurable.ae_eq_mk
  have hs := Measure.ae_ae_of_ae_prod hfe
  have hge : f' =ᵐ[(volume.restrict I).prod (volume.restrict AVenhance.unitCube)] Function.uncurry g := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hfm hg)).2
    filter_upwards [hs, he] with t ht he
    filter_upwards [ht, he] with x hx hy
    exact hx.symm.trans hy
  exact hf.ae_eq (hfe.trans hge)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Indexed finite weak chains use the literal child geometry recursion. -/

def finiteWeakChainGeom (D : OCData) (base : ℕ) (Y : Vec 2)
    (p : ℕ → ℤ) (c : ℕ → ChainChild) : ℕ → ChainGeom
  | 0 => (D.flowOf base, Y, D.slotAnchor (base + 1) (p 0))
  | n + 1 => D.childGeom (base + 1 + n) (p n)
      (D.slotAnchor (base + 1 + (n + 1)) (p (n + 1))) (c n)
      (finiteWeakChainGeom D base Y p c n)

theorem finiteWeakChainGeom_anchor (D : OCData) (base : ℕ) (Y : Vec 2)
    (p : ℕ → ℤ) (c : ℕ → ChainChild) (n : ℕ) :
    (finiteWeakChainGeom D base Y p c n).2.2 = D.slotAnchor (base + 1 + n) (p n) := by
  cases n <;> rfl

theorem finiteWeakChainGeom_smooth (D : OCData) (base : ℕ) (Y : Vec 2)
    (p : ℕ → ℤ) (c : ℕ → ChainChild) (n : ℕ) :
    GeomSpatialSmooth (finiteWeakChainGeom D base Y p c n) := by
  induction n with
  | zero =>
    intro u r
    exact (CycleReference.streamFlow_joint_smooth (D.hΦ base)).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  | succ n ih => exact geomSpatialSmooth_childGeom D _ _ _ _ ih

theorem finiteWeakChainGeom_eq_chain (D : OCData) (base : ℕ) (Y : Vec 2)
    (p : ℕ → ℤ) (c : ℕ → ChainChild) (n : ℕ) :
    finiteWeakChainGeom D base Y p c n =
      (⟨base, List.ofFn (fun j : Fin (n + 1) => p j), Y,
        List.ofFn (fun j : Fin n => c j)⟩ : RealChain).geom D := by
  induction n with
  | zero => simp [finiteWeakChainGeom, RealChain.geom, OCData.geomAux]
  | succ n ih =>
    rw [List.ofFn_succ' (fun j : Fin (n + 1 + 1) => p j),
      List.ofFn_succ' (fun j : Fin (n + 1) => c j)]
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
    rw [geom_append_child D base _ Y _ (by simp)]
    rw [← ih]
    simp only [List.length_ofFn]
    have hp : (List.ofFn (fun j : Fin (n + 1) => p j)).getLastD 0 = p n := by
      rw [List.ofFn_succ']
      simp
    rw [hp]
    rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Mixed native order lowering retains every inverse power of the parent length. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem transitionT_independent_slow_rescaled_local_jet_bound
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (E : ℝ) (hE : 0 < E) (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (X : P × Vec 2)
    (hKC : ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => K Z.1 (E • Z.2) a b) X‖ ≤ C)
    (I A : List (Fin 2)) (hA : A.length ≤ I.length) (n : ℕ) (hn : n + I.length ≤ N)
    :
    ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 => transitionT (K Z.1) I A (E • Z.2)) X‖ ≤
      E⁻¹ ^ (I.length - A.length) * (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length := by
  let KN := fun z y => K z (E • y)
  have hs a b : ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => KN Z.1 Z.2 a b) :=
    (hK a b).comp (contDiff_fst.prodMk (contDiff_snd.const_smul E))
  have he : (fun Z : P × Vec 2 => transitionT (K Z.1) I A (E • Z.2)) =
      fun Z => E⁻¹ ^ (I.length - A.length) • transitionT (KN Z.1) I A Z.2 :=
    funext (transitionT_independent_slow_rescaled_eq K hK E hE I A hA)
  rw [he, iteratedFDeriv_const_smul_apply'
    ((transitionT_independent_slow_smooth KN hs I A).contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_pos.mpr hE).le _)]
  exact mul_le_mul_of_nonneg_left
    (transitionT_independent_slow_local_jet_bound KN hs N C hC X hKC I A n hn)
    (pow_nonneg (inv_pos.mpr hE).le _)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The finite classical source adapter retains its actual scalar L² value. -/

theorem dataHkSlice_value (K : ℕ) (D : ℝ → RawJet2 K ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) :
    (dataHkSlice K D t).val (valueIndex2 K) = cellSourceSlice (fun s x => D s (valueIndex2 K) x) t := by
  rw [dataHkSlice_eq_toHk K D t ht]
  simp only [TorusHkFunction.toHk, torusJetToL2, cellSourceSlice,
    dite_eq_left (ht.2.1 (valueIndex2 K))]

theorem complexFiniteData_value (K : ℕ) (q : ℝ → Vec 2 → ℝ)
    (hq : ∀ t, ContDiff ℝ (K : ℕ∞) (q t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (q t)) (t : ℝ) :
    (dataHkSlice K (fun s => complexFiniteJet K (q s)) t).val (valueIndex2 K) =
      cellSourceSlice (fun s x => (q s x : ℂ)) t := by
  rw [dataHkSlice_value K _ t (complexFiniteJet_periodicWeak K (q t) (hq t) (hp t))]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The base chart is uniformly close on its enlarged renewal window. -/

theorem finite_weak_base_chart_close_of_small_window (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (base : ℕ) (hbase : 1 ≤ base)
    (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild) (R δ : ℝ)
    (hshort : 2 * R * ocTauPP D.α D.q D.Λ (base + 1) ≤
      (2 : ℝ) ^ (-25 : ℤ) * (ocA D.α D.q D.Λ base)⁻¹)
    (hsmall : 2 ^ 23 * (2 * R * ocTauPP D.α D.q D.Λ (base + 1)) * ocA D.α D.q D.Λ base ≤ δ)
    (u r : ℝ)
    (hu : |u - D.slotAnchor (base + 1) (p 0)| ≤ R * ocTauPP D.α D.q D.Λ (base + 1))
    (hr : |r - D.slotAnchor (base + 1) (p 0)| ≤ R * ocTauPP D.α D.q D.Λ (base + 1))
    (x : Vec 2) :
    ‖fderiv ℝ (fun y => (finiteWeakChainGeom D base Y p c 0).1 u y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ δ := by
  have htime : |u - r| ≤ 2 * R * ocTauPP D.α D.q D.Λ (base + 1) := by
    have ht := abs_sub_le u (D.slotAnchor (base + 1) (p 0)) r
    have hr' : |D.slotAnchor (base + 1) (p 0) - r| ≤
        R * ocTauPP D.α D.q D.Λ (base + 1) := by simpa only [abs_sub_comm] using hr
    linarith
  have hb := actual_coarse_flow_close D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq base hbase r u
    (htime.trans hshort) x
  have hA : 0 ≤ ocA D.α D.q D.Λ base := by
    unfold ocA
    exact Real.rpow_nonneg (Scales.epsilon_basic hq.1 hΛ).1.le _
  exact hb.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htime (by positivity)) hA).trans hsmall)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Ordered covariant left terms depend only on the coefficient germs inside their open carrier. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set (Vec 2)}

theorem leftTermSlowEq_slowDerivativeTerms (hU : IsOpen U) {c d : LeftTerm E F}
    (he : LeftTermSlowEq U c d) (k : Fin 2) :
    List.Forall₂ (LeftTermSlowEq U) (c.slowDerivativeTerms k) (d.slowDerivativeTerms k) :=
  List.Forall₂.cons (he.slowCoefficientDerivative hU k)
    (List.Forall₂.cons (he.slowInputDerivative k) List.Forall₂.nil)

theorem covariantLeftTermStep_slow_local_congr (hU : IsOpen U) (η : ℝ) (k : Fin 2)
    (P Q : ℕ → List (LeftTerm E F))
    (he : ∀ j, List.Forall₂ (LeftTermSlowEq U) (P j) (Q j)) (j : ℕ) :
    List.Forall₂ (LeftTermSlowEq U) (covariantLeftTermStep η k P j) (covariantLeftTermStep η k Q j) := by
  unfold covariantLeftTermStep
  apply List.rel_append
  · exact List.rel_map (fun _ _ h => h.fastDerivative k) (he j)
  · by_cases hj : j = 0
    · simp only [ite_eq_left hj]
      exact List.Forall₂.nil
    · simp only [ite_eq_right hj]
      exact List.rel_map (fun _ _ h => h.smul (Real.sqrt η))
        (List.rel_flatMap (he (j - 1)) (fun _ _ h => leftTermSlowEq_slowDerivativeTerms hU h k))

theorem covariantLeftTermList_slow_local_congr (hU : IsOpen U) (η : ℝ) (w : List (Fin 2))
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq U) l r) :
    ∀ j, List.Forall₂ (LeftTermSlowEq U) (covariantLeftTermList η w l j) (covariantLeftTermList η w r j) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro j
    rw [covariantLeftTermList_nil, covariantLeftTermList_nil]
    by_cases hj : j = 0
    · simpa only [ite_eq_left hj] using he
    · simp only [ite_eq_right hj]
      exact List.Forall₂.nil
  | append_singleton w k ih =>
    intro j
    rw [covariantLeftTermList_append_singleton, covariantLeftTermList_append_singleton]
    exact covariantLeftTermStep_slow_local_congr hU η k _ _ ih j

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite weak charts preserve area through every child step. -/

def GeomAreaPreserving (g : ChainGeom) : Prop :=
  ∀ u r x, (jacMatrix (fun y => g.1 u y r) x).det = 1

theorem childGeom_area_preserving (D : OCData) (k : ℕ) (hε : 0 < D.eps k)
    (pk : ℤ) (hpk : Odd pk) (s' : ℝ) (c : ChainChild) {g : ChainGeom}
    (hg : GeomSpatialSmooth g) (ha : GeomAreaPreserving g) :
    GeomAreaPreserving (D.childGeom k pk s' c g) := by
  intro u r x
  rw [childGeom_jacobian_factorization D k pk s' c g hg u r x,
    Matrix.det_mul, Matrix.det_mul, ha,
    childShearMap_jacobian_det_one D k hε pk hpk, ha]
  norm_num

theorem finiteWeakChainGeom_area_preserving (D : OCData) (hΛ : 1 ≤ D.Λ)
    (base : ℕ) (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild) (n : ℕ)
    (hp : ∀ j < n, Odd (p j)) :
    GeomAreaPreserving (finiteWeakChainGeom D base Y p c n) := by
  induction n with
  | zero =>
    intro u r x
    exact CycleReference.streamFlow_jacMatrix_det_one (D.hΦ base) u r x
  | succ n ih =>
    apply childGeom_area_preserving D (base + 1 + n)
      (Construction.Stream.ocEpsilon_pos hΛ) (p n) (hp n (by omega))
    · exact finiteWeakChainGeom_smooth D base Y p c n
    · exact ih (fun j hj => hp j (by omega))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! A literal mixed Piola summand retains the inverse parent-length lowering power. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem native_independent_slow_piola_summand_local_jet_bound
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (E : ℝ) (hE : 0 < E) (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (X : P × Vec 2)
    (hKC : ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => K Z.1 (E • Z.2) a b) X‖ ≤ C)
    (I A : List (Fin 2)) (hA : A.length ≤ I.length) (n : ℕ) (hn : n + I.length ≤ N)
    (B : P × Vec 2 → ℝ) (hB : ContDiff ℝ (n : ℕ∞) B) (MB : ℝ)
    (hBj : ∀ j ≤ n, ‖iteratedFDeriv ℝ j B X‖ ≤ MB)
    (a i : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Z : P × Vec 2 =>
      K Z.1 (E • Z.2) a i * B Z * transitionT (K Z.1) I A (E • Z.2)) X‖ ≤
      ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB *
        (E⁻¹ ^ (I.length - A.length) * (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun Z : P × Vec 2 => (Z.1, E • Z.2)) := by fun_prop
  have hnn : n ≤ N := by omega
  have hh := CycleJointProofs.triple_product_weighted_jet_bound
    (fun Z : P × Vec 2 => K Z.1 (E • Z.2) a i) B
    (fun Z : P × Vec 2 => transitionT (K Z.1) I A (E • Z.2)) X n
    (((hK a i).comp hmap).of_le (by simp)) hB
    (((transitionT_independent_slow_smooth K hK I A).comp hmap).of_le (by simp))
    1 C MB _ zero_le_one
    (fun j hj => by simpa only [one_pow, one_mul] using hKC a i j (hj.trans hnn))
    (fun j hj => by simpa only [one_pow, one_mul] using hBj j hj)
    (fun j hj => by simpa only [one_pow, one_mul] using
      transitionT_independent_slow_rescaled_local_jet_bound K hK E hE N C hC X hKC I A hA j (by omega))
  simpa only [one_pow, one_mul] using hh

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The indexed weak-chain estimates apply to every actual finite real chain. -/

def realChainSlotSeq (A : RealChain) (n : ℕ) : ℤ := A.slots.getD n 0

def realChainChildSeq (A : RealChain) (n : ℕ) : ChainChild := A.children.getD n ⟨0, 0⟩

theorem realChain_slots_ofFn (A : RealChain) (hl : A.slots.length = A.children.length + 1) :
    List.ofFn (fun j : Fin (A.children.length + 1) => realChainSlotSeq A j) = A.slots := by
  rw [← hl]
  simp only [realChainSlotSeq, List.getD_eq_getElem _ _ (Fin.is_lt _), List.ofFn_getElem]

theorem realChain_children_ofFn (A : RealChain) :
    List.ofFn (fun j : Fin A.children.length => realChainChildSeq A j) = A.children := by
  simp only [realChainChildSeq, List.getD_eq_getElem _ _ (Fin.is_lt _), List.ofFn_getElem]

theorem realChain_ofFn_eq (A : RealChain) (hl : A.slots.length = A.children.length + 1) :
    (⟨A.baseLevel, List.ofFn (fun j : Fin (A.children.length + 1) => realChainSlotSeq A j), A.base,
      List.ofFn (fun j : Fin A.children.length => realChainChildSeq A j)⟩ : RealChain) = A := by
  rw [realChain_slots_ofFn A hl, realChain_children_ofFn A]

theorem realChainSlotSeq_last (A : RealChain) (hl : A.slots.length = A.children.length + 1) :
    realChainSlotSeq A A.children.length = A.slot := by
  unfold RealChain.slot
  rw [← realChain_slots_ofFn A hl, List.ofFn_succ']
  simp

theorem realChainSlotSeq_odd (D : OCData) (A : RealChain) {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    (hA : IsAdmissibleChain D b j₀ i p A) (n : ℕ) (hn : n ≤ A.children.length) :
    Odd (realChainSlotSeq A n) := by
  rcases hA with ⟨_, _, hl, _, ho, _, _⟩
  have hlt : n < A.slots.length := by omega
  unfold realChainSlotSeq
  rw [List.getD_eq_getElem A.slots 0 hlt]
  exact ho _ (List.getElem_mem hlt)

theorem realChainSlotSeq_scheduled (D : OCData) (A : RealChain) {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    (hA : IsAdmissibleChain D b j₀ i p A) (n : ℕ) (hn : n < A.children.length) :
    IsScheduledIn D (A.baseLevel + 1 + n) (realChainSlotSeq A (n + 1)) (realChainSlotSeq A n) := by
  rcases hA with ⟨_, _, hl, _, _, hs, _⟩
  have hn' : n + 1 < A.slots.length := by omega
  unfold realChainSlotSeq
  rw [List.getD_eq_getElem A.slots 0 hn', List.getD_eq_getElem A.slots 0 (by omega : n < A.slots.length)]
  exact hs n hn'

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Uniform positive jets of the literal dimensionless relative displacement. -/

theorem weak_relative_displacement_positive_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (D.relDisp m slot u r) x‖ ≤
      |u - r| * (2 * Real.pi) ^ (n + 1) * ocA D.α D.q D.Λ m := by
  let I := ∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ m slot t
  let F := fun y => I • ocShearVel D.α D.q D.Λ m slot y
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (ocShearVel_spatial_smooth _ _ _ _ _).const_smul I
  have hε : 0 < D.eps m := Construction.Stream.ocEpsilon_pos hΛ
  have he : D.relDisp m slot u r = rescaledChart (D.eps m) F := by
    funext y
    dsimp only [OCData.relDisp, rescaledChart, F, I]
  rw [he, rescaledChart_positive_derivative_norm (D.eps m) hε F hF n hn]
  apply (scaled_shear_positive_derivative_bound (α := D.α) hΛ slot hp I (D.eps m)
    hε le_rfl n hn (D.eps m • x)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pulse_integral_abs_le D hζ m slot u r) (by positivity))
    (by unfold ocA; positivity)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Finite covariant polynomial coefficients are genuine bounded sources after exponential normalization. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def normalizedCoefficientFamily (A : Vec 2 →L[ℝ] ℝ)
    (P : ℕ → ℝ → Vec 2 → Vec 2 → E) (j : ℕ) (t : ℝ) (z Y : Vec 2) : E :=
  (Real.exp (A Y))⁻¹ • P j t Y z

def normalizedCovariantStepReserve (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (P : ℕ → ℝ → Vec 2 → Vec 2 → E) (k : Fin 2) (j : ℕ)
    (QP : ∀ i, JointSourceReserve (H + 1) (normalizedCoefficientFamily A P i)) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      covariantCoefficientStep η k (fun i => P i t) j Y z) := by
  let f := normalizedCoefficientFamily A P j
  let g := normalizedCoefficientFamily A P (j - 1)
  have he (i : ℕ) (t : ℝ) : P i t =
      fun X y => Real.exp (A X) • normalizedCoefficientFamily A P i t y X := by
    funext X y
    simp only [normalizedCoefficientFamily, smul_smul,
      mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hfast (t : ℝ) (z Y : Vec 2) :
      (Real.exp (A Y))⁻¹ • fastPartial k (P j t) Y z =
        fastPartial k (fun X y => f t y X) Y z := by
    rw [he j t]
    exact normalized_fastPartial_exp_smul A k _ t z Y
      (((QP j).fast_contDiff t Y).differentiable (by simp) z)
  by_cases hj : j = 0
  · have hfield : (fun t z Y => (Real.exp (A Y))⁻¹ •
        covariantCoefficientStep η k (fun i => P i t) j Y z) =
        fun t z Y => fastPartial k (fun X y => f t y X) Y z := by
      funext t z Y
      simp only [covariantCoefficientStep, hj, ite_true, add_zero]
      simpa only [hj] using hfast t z Y
    rw [hfield]
    exact (QP j).fastPartial H (by omega) k
  · have hslow (t : ℝ) (z Y : Vec 2) :
        (Real.exp (A Y))⁻¹ • slowPartial k (P (j - 1) t) Y z =
          sourceCovariantSlow A k g t z Y := by
      rw [he (j - 1) t]
      exact normalized_slowPartial_exp_smul A k _ t z Y
        ((((QP (j - 1)).regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable
          (by simp) Y)
    have hfield : (fun t z Y => (Real.exp (A Y))⁻¹ •
        covariantCoefficientStep η k (fun i => P i t) j Y z) =
        fun t z Y => fastPartial k (fun X y => f t y X) Y z +
          Real.sqrt η • sourceCovariantSlow A k g t z Y := by
      funext t z Y
      simp only [covariantCoefficientStep, ite_eq_right hj, smul_add]
      rw [smul_comm (Real.exp (A Y))⁻¹ (Real.sqrt η), hfast, hslow]
    rw [hfield]
    exact ((QP j).fastPartial H (by omega) k).add
      (((QP (j - 1)).covariantSlow H (by omega) A k).map
        (Real.sqrt η • ContinuousLinearMap.id ℝ E))

def normalizedCovariantListReserve {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Qf : JointSourceReserve H f) (R : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (w : List (Fin 2)) (hR : w.length + R ≤ H) (j : ℕ) :
    JointSourceReserve R (fun t z Y => (Real.exp (A Y))⁻¹ •
      covariantListCoefficients η w (fun X y => Real.exp (A X) • f t y X) j Y z) := by
  induction w using List.reverseRecOn generalizing R j with
  | nil =>
      by_cases hj : j = 0
      · simp only [covariantListCoefficients_nil, hj, ite_true, smul_smul,
          inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
        exact Qf.mono R (by simpa using hR)
      · simp only [covariantListCoefficients_nil, ite_eq_right hj, smul_zero]
        exact JointSourceReserve.zero R
  | append_singleton w k ih =>
      have hr : w.length + (R + 1) ≤ H := by
        simp only [List.length_append, List.length_singleton] at hR
        omega
      let P := fun i t => covariantListCoefficients η w
        (fun X y => Real.exp (A X) • f t y X) i
      have he : (fun t z Y => (Real.exp (A Y))⁻¹ •
          covariantListCoefficients η (w ++ [k])
            (fun X y => Real.exp (A X) • f t y X) j Y z) =
          fun t z Y => (Real.exp (A Y))⁻¹ •
            covariantCoefficientStep η k (fun i => P i t) j Y z := by
        funext t z Y
        rw [covariantListCoefficients_append_singleton]
      rw [he]
      exact normalizedCovariantStepReserve R A η P k j (fun i => ih (R + 1) hr i)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Positive jets of every child shear are uniformly controlled at finer label scales. -/

theorem rescaled_child_shear_derivative_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (hpk : Odd pk)
    (u r ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ D.eps k)
    (c : ChainChild) (g : ChainGeom) (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (rescaledChart ρ (childShearMap D k pk u r c g)) x‖ ≤
      1 + |u - r| * (2 * Real.pi) ^ (n + 1) * ocA D.α D.q D.Λ k := by
  have he : 0 < D.eps k := Construction.Stream.ocEpsilon_pos hΛ
  let γ := D.eps k • (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))
  let I := ∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ k pk t
  let F := fun y => I • ocShearVel D.α D.q D.Λ k pk (y + γ)
  have hs : ContDiff ℝ (⊤ : ℕ∞) F :=
    ((ocShearVel_spatial_smooth _ _ _ _ _).comp
      (contDiff_id.add contDiff_const)).const_smul I
  have hmap : childShearMap D k pk u r c g = id + F :=
    funext (childShearMap_physical D k he pk u r c g)
  rw [rescaledChart_positive_derivative_norm ρ hρ _
    (childShearMap_spatial_smooth D k pk u r c g) n hn x, hmap,
    iteratedFDeriv_add_apply ((contDiff_id : ContDiff ℝ (n : ℕ) id).contDiffAt)
      (hs.contDiffAt.of_le (by simp))]
  have hid : ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n (id : Vec 2 → Vec 2) (ρ • x)‖ ≤ 1 := by
    by_cases hn1 : n = 1
    · subst n
      simp [norm_iteratedFDeriv_one, fderiv_id]
    · change ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n (fun y : Vec 2 => y) (ρ • x)‖ ≤ 1
      rw [identity_iteratedFDeriv_eq_zero n (by omega) (ρ • x), norm_zero, mul_zero]
      norm_num
  have hF : ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n F (ρ • x)‖ ≤
      |I| * (2 * Real.pi) ^ (n + 1) * ocA D.α D.q D.Λ k := by
    have hb := scaled_shear_positive_derivative_bound (α := D.α) hΛ pk hpk I ρ hρ hρe n hn (ρ • x + γ)
    change ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n
      (fun y => (fun z => I • ocShearVel D.α D.q D.Λ k pk z) (y + γ)) (ρ • x)‖ ≤ _
    rw [iteratedFDeriv_comp_add_right (f := fun z => I • ocShearVel D.α D.q D.Λ k pk z)
      n γ (ρ • x)]
    exact hb
  calc
    _ ≤ ρ ^ (n - 1) * (‖iteratedFDeriv ℝ n id (ρ • x)‖ +
        ‖iteratedFDeriv ℝ n F (ρ • x)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hρ.le _)
    _ = ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n id (ρ • x)‖ +
        ρ ^ (n - 1) * ‖iteratedFDeriv ℝ n F (ρ • x)‖ := mul_add _ _ _
    _ ≤ 1 + |I| * (2 * Real.pi) ^ (n + 1) * ocA D.α D.q D.Λ k := add_le_add hid hF
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pulse_integral_abs_le D hζ k pk u r) (by positivity))
      (by unfold ocA; positivity))

/-! The literal relative shear has a uniform budget including its value, needed for centered differences. -/

theorem weak_relative_displacement_value_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ) (x : Vec 2) :
    ‖D.relDisp m slot u r x‖ ≤ |u - r| * (2 * Real.pi) * ocA D.α D.q D.Λ m := by
  let I := ∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ m slot t
  have hε : 0 < D.eps m := Construction.Stream.ocEpsilon_pos hΛ
  have hb := scaled_shear_derivative_norm_le (α := D.α) (q := D.q) (m := m)
    hΛ slot hp I 0 (D.eps m • x)
  simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one] at hb
  have ha : D.eps m ^ D.α * (D.eps m)⁻¹ = ocA D.α D.q D.Λ m := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one hε.ne']
    unfold ocA
    congr 1
    ring
  change ‖(D.eps m)⁻¹ • (I • ocShearVel D.α D.q D.Λ m slot (D.eps m • x))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  calc
    _ ≤ (D.eps m)⁻¹ * (|I| * (2 * Real.pi * D.eps m ^ D.α)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hε.le)
    _ = |I| * (2 * Real.pi) * ocA D.α D.q D.Λ m := by rw [← ha]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pulse_integral_abs_le D hζ m slot u r) (by positivity))
      (by unfold ocA; positivity)

theorem weak_relative_displacement_all_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (D.relDisp m slot u r) x‖ ≤
      |u - r| * (2 * Real.pi) ^ (n + 1) * ocA D.α D.q D.Λ m := by
  by_cases hn : n = 0
  · subst n
    simpa only [norm_iteratedFDeriv_zero, Nat.zero_add, pow_one] using
      weak_relative_displacement_value_bound D hΛ hζ m slot hp u r x
  · exact weak_relative_displacement_positive_jet_bound D hΛ hζ m slot hp u r n (by omega) x

theorem weak_relative_displacement_menu_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (K n : ℕ) (hn : n ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (D.relDisp m slot u r) x‖ ≤
      |u - r| * (2 * Real.pi) ^ (K + 1) * ocA D.α D.q D.Λ m := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hA : 0 ≤ ocA D.α D.q D.Λ m := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  exact (weak_relative_displacement_all_jet_bound D hΛ hζ m slot hp u r n x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hpi (by omega)) (abs_nonneg (u - r))) hA)

end AVRegularity.EntryWeakProofs
end
end
