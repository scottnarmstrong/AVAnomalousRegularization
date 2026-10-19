-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.IncrementProvider
public import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Construction.Scales.Times
public import AVenhance.Infra.Ingredients.Parameters
public import AVenhance.Statements.Construction.BarNorm

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Velocity.Jets

/-! Generic pointwise, radius, sum, and addition facts for the paper barNorm. -/

/-- A continuous function has its `L∞` norm equal to the supremum of its pointwise norm. -/
theorem continuous_eLpNorm_top_eq_iSup (f : Vec 2 → ℝ) (hf : Continuous f) :
    eLpNorm f ⊤ volume = ⨆ x, ‖f x‖ₑ := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm]
  apply le_antisymm essSup_le_iSup
  apply iSup_le
  intro x
  have hae := ae_le_essSup (f := fun y : Vec 2 => ‖f y‖ₑ) (μ := volume)
  have heq : (fun y => min ‖f y‖ₑ (essSup (fun z => ‖f z‖ₑ) volume)) =
      fun y => ‖f y‖ₑ := by
    apply Measure.eq_of_ae_eq (hae.mono (fun y hy => min_eq_left hy))
    · exact hf.enorm.min continuous_const
    · exact hf.enorm
  exact (min_eq_left_iff).mp (congrFun heq x)

/-- Pointwise form of the scalar construction seminorm. -/
theorem barNorm_eq_pointwise (f : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) :
    AVenhance.barNorm n R f =
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n *
          ⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
            ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ := by
  unfold AVenhance.barNorm
  congr 2
  funext J
  apply continuous_eLpNorm_top_eq_iSup
  have hc := hf.continuous_iteratedFDeriv'
  fun_prop

/-- Addition has constant one in the scalar construction seminorm. -/
theorem barNorm_add_le (f g : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.barNorm n R (f + g) ≤ AVenhance.barNorm n R f + AVenhance.barNorm n R g := by
  have hfg : ContDiff ℝ n (f + g) := hf.add hg
  rw [barNorm_eq_pointwise (f + g) n R hfg, barNorm_eq_pointwise f n R hf,
    barNorm_eq_pointwise g n R hg, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply iSup_le
  intro J
  apply iSup_le
  intro x
  rw [iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, add_apply]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup_of_le J (le_iSup_of_le x le_rfl))
    (le_iSup_of_le J (le_iSup_of_le x le_rfl)))

/-- Changing the radius multiplies the order-n seminorm by the radius ratio to order n. -/
theorem barNorm_radius_change {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    AVenhance.barNorm n S f = AVenhance.barNorm n R f * ENNReal.ofReal (R / S) ^ n := by
  rw [barNorm_eq_pointwise f n S hf, barNorm_eq_pointwise f n R hf]
  let a : ENNReal := ENNReal.ofReal R
  let b : ENNReal := ENNReal.ofReal S
  let q : ENNReal := ENNReal.ofReal (R / S)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact (ENNReal.ofReal_pos.mpr hR).ne'
  have hatop : a ≠ ⊤ := by dsimp [a]; exact ENNReal.ofReal_ne_top
  have hb0 : b ≠ 0 := by
    dsimp [b]
    exact (ENNReal.ofReal_pos.mpr hS).ne'
  have hbtop : b ≠ ⊤ := by dsimp [b]; exact ENNReal.ofReal_ne_top
  have hq : q = a / b := by
    dsimp [q, a, b]
    exact ENNReal.ofReal_div_of_pos hS
  have hsingle : a⁻¹ * q = b⁻¹ := by
    rw [hq, div_eq_mul_inv]
    calc
      a⁻¹ * (a * b⁻¹) = (a⁻¹ * a) * b⁻¹ := by rw [mul_assoc]
      _ = b⁻¹ := by rw [ENNReal.inv_mul_cancel ha0 hatop, one_mul]
  have hfactor : a⁻¹ ^ n * q ^ n = b⁻¹ ^ n := by
    rw [← mul_pow, hsingle]
  let w : ENNReal := ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / n.factorial)
  let D : ENNReal := ⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
    ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ
  change w * b⁻¹ ^ n * D = (w * a⁻¹ ^ n * D) * q ^ n
  rw [← hfactor]
  ac_rfl

/-- Finite sums retain constant one in `barNorm`. -/
theorem barNorm_sum_le {ι : Type*} (S : Finset ι) (f : ι → Vec 2 → ℝ)
    (n : ℕ) (R : ℝ) (hf : ∀ i ∈ S, ContDiff ℝ n (f i)) :
    AVenhance.barNorm n R (∑ i ∈ S, f i) ≤ ∑ i ∈ S, AVenhance.barNorm n R (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [AVenhance.barNorm]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hS : ∀ k ∈ S, ContDiff ℝ n (f k) :=
      fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have hsum : ContDiff ℝ n (∑ k ∈ S, f k) := by
      convert ContDiff.sum hS using 1
      ext x
      simp
    exact (barNorm_add_le _ _ n R (hf i (Finset.mem_insert_self i S)) hsum).trans
      (add_le_add le_rfl (ih hS))

end AVRegularity.Velocity.Jets
end
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.Velocity.Jets

/-! Fixed-order derivative bounds for the smooth transition and its affine rescalings. -/

noncomputable def fastProfileDerivativeBound {ζ : ℝ → ℝ}
    (hζ : AVRegularity.IsFastProfile ζ) (n : ℕ) : ℝ :=
  Classical.choose (AVRegularity.Velocity.exists_uniform_fastProfile_iteratedDeriv_bound hζ n)

theorem fastProfileDerivativeBound_nonneg {ζ : ℝ → ℝ}
    (hζ : AVRegularity.IsFastProfile ζ) (n : ℕ) :
    0 ≤ fastProfileDerivativeBound hζ n :=
  (Classical.choose_spec
    (AVRegularity.Velocity.exists_uniform_fastProfile_iteratedDeriv_bound hζ n)).1

theorem fastProfileDerivativeBound_spec {ζ : ℝ → ℝ}
    (hζ : AVRegularity.IsFastProfile ζ) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n ζ t| ≤ fastProfileDerivativeBound hζ n :=
  (Classical.choose_spec
    (AVRegularity.Velocity.exists_uniform_fastProfile_iteratedDeriv_bound hζ n)).2 t

/-- The fast cutoff derivative estimate, with the `tau⁻ⁿ` rescaling cancelled
by the prefactor `tauⁿ`. -/
theorem fastCutoff_iteratedDeriv_bound {ζ : ℝ → ℝ} (hζ : AVRegularity.IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) (k : ℤ) (n : ℕ) (t : ℝ) :
    τ ^ n * |iteratedDeriv n
      (fun x : ℝ => ζ ((x - (k : ℝ) * τ) / τ)) t| ≤ fastProfileDerivativeBound hζ n := by
  let c := τ⁻¹
  let d := -(k : ℝ)
  have harg : (fun x : ℝ => (x - (k : ℝ) * τ) / τ) =
      fun x => c * x + d := by
    funext x
    dsimp [c, d]
    field_simp [ne_of_gt hτ]
    ring
  have hζn : ContDiff ℝ n ζ := hζ.1.of_le (by simp)
  let g : ℝ → ℝ := fun y => ζ (y + d)
  have hg : ContDiff ℝ n g := by
    dsimp [g]
    exact hζn.comp (by fun_prop)
  have hcomp : (fun x : ℝ => ζ (c * x + d)) = fun x => g (c * x) := by
    funext x
    rfl
  have hfun : (fun x : ℝ => ζ ((x - (k : ℝ) * τ) / τ)) =
      fun x => ζ (c * x + d) := by
    funext x
    rw [show (x - (k : ℝ) * τ) / τ = c * x + d from congrFun harg x]
  rw [hfun, hcomp, iteratedDeriv_comp_const_mul hg c,
    iteratedDeriv_comp_add_const]
  have hc : |c| = τ⁻¹ := by
    dsimp [c]
    exact abs_of_pos (inv_pos.mpr hτ)
  have hpow : τ ^ n * (τ⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hτ), one_pow]
  calc
    τ ^ n * |c ^ n * iteratedDeriv n ζ (c * t + d)| =
        τ ^ n * (|c| ^ n * |iteratedDeriv n ζ (c * t + d)|) := by
          rw [abs_mul, abs_pow]
    _ ≤ τ ^ n * (fastProfileDerivativeBound hζ n * |c| ^ n) := by
      calc
        τ ^ n * (|c| ^ n * |iteratedDeriv n ζ (c * t + d)|) =
            (τ ^ n * |c| ^ n) * |iteratedDeriv n ζ (c * t + d)| := by ring
        _ ≤ (τ ^ n * |c| ^ n) * fastProfileDerivativeBound hζ n :=
          mul_le_mul_of_nonneg_left
            (fastProfileDerivativeBound_spec hζ n _)
            (mul_nonneg (pow_nonneg hτ.le n) (pow_nonneg (abs_nonneg c) n))
        _ = τ ^ n * (fastProfileDerivativeBound hζ n * |c| ^ n) := by ring
    _ = fastProfileDerivativeBound hζ n := by
      rw [hc]
      calc
        τ ^ n * (fastProfileDerivativeBound hζ n * (τ⁻¹) ^ n) =
            fastProfileDerivativeBound hζ n * (τ ^ n * (τ⁻¹) ^ n) := by ring
        _ = fastProfileDerivativeBound hζ n := by rw [hpow, mul_one]

private theorem smoothTransition_iteratedDeriv_zero_left {n : ℕ} {x : ℝ}
    (hx : x < 0) : iteratedDeriv n Real.smoothTransition x = 0 := by
  have hEq : Set.EqOn Real.smoothTransition (fun _ : ℝ => 0) (Set.Iio 0) := by
    intro y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  have h := hEq.iteratedDeriv_of_isOpen isOpen_Iio n hx
  simpa using h

private theorem smoothTransition_iteratedDeriv_zero_right {n : ℕ} {x : ℝ}
    (hn : 1 ≤ n) (hx : 1 < x) : iteratedDeriv n Real.smoothTransition x = 0 := by
  have hEq : Set.EqOn Real.smoothTransition (fun _ : ℝ => 1) (Set.Ioi 1) := by
    intro y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  have h := hEq.iteratedDeriv_of_isOpen isOpen_Ioi n hx
  rw [h, iteratedDeriv_const]
  simp [Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)]

private theorem smoothTransition_deriv_tsupport_subset {n : ℕ} (hn : 1 ≤ n) :
    tsupport (iteratedDeriv n Real.smoothTransition) ⊆ Set.Icc (0 : ℝ) 1 := by
  change closure {x : ℝ | iteratedDeriv n Real.smoothTransition x ≠ 0} ⊆ _
  apply closure_minimal
  · intro x hx
    change iteratedDeriv n Real.smoothTransition x ≠ 0 at hx
    by_cases hleft : x < 0
    · exact False.elim (hx (smoothTransition_iteratedDeriv_zero_left hleft))
    · by_cases hright : 1 < x
      · exact False.elim (hx (smoothTransition_iteratedDeriv_zero_right hn hright))
      · exact ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
  · exact isClosed_Icc

/-- Every fixed derivative of `Real.smoothTransition` is bounded on the line.
The order-zero bound follows from its range; positive-order derivatives are
supported in `[0,1]`. -/
theorem exists_uniform_smoothTransition_iteratedDeriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |iteratedDeriv n Real.smoothTransition t| ≤ C := by
  by_cases hn : n = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro t
    rw [hn, iteratedDeriv_zero]
    rw [abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact Real.smoothTransition.le_one t
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let K : Set ℝ := Set.Icc 0 1
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    have hcont : Continuous (fun t : ℝ => |iteratedDeriv n Real.smoothTransition t|) := by
      exact (hsmooth.continuous_iteratedDeriv n (by simp)).abs
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont.continuousOn
    let C : ℝ := max B 0
    refine ⟨C, le_max_right B 0, ?_⟩
    intro t
    by_cases ht : t ∈ K
    · have hmem : |iteratedDeriv n Real.smoothTransition t| ∈
          (fun x : ℝ => |iteratedDeriv n Real.smoothTransition x|) '' K :=
        ⟨t, ht, rfl⟩
      exact (hB hmem).trans (le_max_left B 0)
    · have hnotderiv : t ∉ tsupport (iteratedDeriv n Real.smoothTransition) := by
        intro hmem
        exact ht ((smoothTransition_deriv_tsupport_subset hnpos) hmem)
      have hevent : (fun x => iteratedDeriv n Real.smoothTransition x) =ᶠ[nhds t] 0 :=
        (notMem_tsupport_iff_eventuallyEq).mp hnotderiv
      have hzero : iteratedDeriv n Real.smoothTransition t = 0 := hevent.self_of_nhds
      simp [C, hzero]

noncomputable def smoothTransitionDerivativeBound (n : ℕ) : ℝ :=
  Classical.choose (exists_uniform_smoothTransition_iteratedDeriv_bound n)

theorem smoothTransitionDerivativeBound_nonneg (n : ℕ) :
    0 ≤ smoothTransitionDerivativeBound n :=
  (Classical.choose_spec (exists_uniform_smoothTransition_iteratedDeriv_bound n)).1

theorem smoothTransitionDerivativeBound_spec (n : ℕ) (t : ℝ) :
    |iteratedDeriv n Real.smoothTransition t| ≤ smoothTransitionDerivativeBound n :=
  (Classical.choose_spec (exists_uniform_smoothTransition_iteratedDeriv_bound n)).2 t

theorem affine_smoothTransition_iteratedDeriv_bound
    (n : ℕ) (c d t : ℝ) :
    |iteratedDeriv n (fun x : ℝ => Real.smoothTransition (c * x + d)) t| ≤
      smoothTransitionDerivativeBound n * |c| ^ n := by
  let g : ℝ → ℝ := fun y => Real.smoothTransition (y + d)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hHn : ContDiff ℝ n Real.smoothTransition := hsmooth.of_le (by simp)
  have hg : ContDiff ℝ n g := by
    dsimp [g]
    exact hHn.comp (by fun_prop)
  have hcomp : (fun x : ℝ => Real.smoothTransition (c * x + d)) =
      fun x => g (c * x) := by
    funext x
    rfl
  rw [hcomp, iteratedDeriv_comp_const_mul hg c, iteratedDeriv_comp_add_const]
  calc
    |c ^ n * iteratedDeriv n Real.smoothTransition (c * t + d)| =
        |c| ^ n * |iteratedDeriv n Real.smoothTransition (c * t + d)| := by
          rw [abs_mul, abs_pow]
    _ ≤ |c| ^ n * smoothTransitionDerivativeBound n :=
      mul_le_mul_of_nonneg_left (smoothTransitionDerivativeBound_spec n _) (by positivity)
    _ = smoothTransitionDerivativeBound n * |c| ^ n := by ring

noncomputable def smoothTransitionProductDerivativeBound (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * smoothTransitionDerivativeBound i *
      smoothTransitionDerivativeBound (n - i)

theorem smoothTransitionProductDerivativeBound_nonneg (n : ℕ) :
    0 ≤ smoothTransitionProductDerivativeBound n := by
  unfold smoothTransitionProductDerivativeBound
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (smoothTransitionDerivativeBound_nonneg _))
    (smoothTransitionDerivativeBound_nonneg _)

/-- Leibniz' formula and the affine transition bounds give a scale-sharp
bound for the product of two transitions with opposite slopes. -/
theorem affine_smoothTransition_product_iteratedDeriv_bound
    (n : ℕ) (c d e t : ℝ) :
    |iteratedDeriv n (fun x : ℝ =>
      Real.smoothTransition (c * x + d) * Real.smoothTransition (-c * x + e)) t| ≤
        smoothTransitionProductDerivativeBound n * |c| ^ n := by
  let f : ℝ → ℝ := fun x => Real.smoothTransition (c * x + d)
  let g : ℝ → ℝ := fun x => Real.smoothTransition (-c * x + e)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hHn : ContDiff ℝ n Real.smoothTransition := hsmooth.of_le (by simp)
  have hf : ContDiff ℝ n f := hHn.comp (by fun_prop)
  have hg : ContDiff ℝ n g := hHn.comp (by fun_prop)
  have hmul := iteratedDeriv_mul (x := t) hf.contDiffAt hg.contDiffAt
  change |iteratedDeriv n (f * g) t| ≤ _
  rw [hmul]
  calc
    |∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * iteratedDeriv i f t * iteratedDeriv (n - i) g t| ≤
      ∑ i ∈ Finset.range (n + 1),
        |(n.choose i : ℝ) * iteratedDeriv i f t * iteratedDeriv (n - i) g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * smoothTransitionDerivativeBound i *
          smoothTransitionDerivativeBound (n - i)) * |c| ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by simp only [Finset.mem_range] at hi; omega
      have hfi := affine_smoothTransition_iteratedDeriv_bound i c d t
      have hgi := affine_smoothTransition_iteratedDeriv_bound (n - i) (-c) e t
      have hpowAbs : |(-c : ℝ)| = |c| := by simp
      have hscalei : 0 ≤ smoothTransitionDerivativeBound i * |c| ^ i :=
        mul_nonneg (smoothTransitionDerivativeBound_nonneg i) (pow_nonneg (abs_nonneg c) i)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        (n.choose i : ℝ) * |iteratedDeriv i f t| *
            |iteratedDeriv (n - i) g t| ≤
          (n.choose i : ℝ) *
            (smoothTransitionDerivativeBound i * |c| ^ i) *
            (smoothTransitionDerivativeBound (n - i) * |c| ^ (n - i)) := by
          have hgi' : |iteratedDeriv (n - i) g t| ≤
              smoothTransitionDerivativeBound (n - i) * |c| ^ (n - i) := by
            simpa [g, hpowAbs] using hgi
          calc
            (n.choose i : ℝ) * |iteratedDeriv i f t| *
                |iteratedDeriv (n - i) g t| =
              (n.choose i : ℝ) *
                (|iteratedDeriv i f t| * |iteratedDeriv (n - i) g t|) := by ring
            _ ≤ (n.choose i : ℝ) *
                ((smoothTransitionDerivativeBound i * |c| ^ i) *
                  (smoothTransitionDerivativeBound (n - i) * |c| ^ (n - i))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hfi hgi' (abs_nonneg _) hscalei)
                (Nat.cast_nonneg _)
            _ = (n.choose i : ℝ) *
                (smoothTransitionDerivativeBound i * |c| ^ i) *
                (smoothTransitionDerivativeBound (n - i) * |c| ^ (n - i)) := by ring
        _ = ((n.choose i : ℝ) * smoothTransitionDerivativeBound i *
              smoothTransitionDerivativeBound (n - i)) *
                (|c| ^ i * |c| ^ (n - i)) := by ring
        _ = ((n.choose i : ℝ) * smoothTransitionDerivativeBound i *
              smoothTransitionDerivativeBound (n - i)) * |c| ^ n := by
          rw [← pow_add, Nat.add_sub_of_le hi']
    _ = smoothTransitionProductDerivativeBound n * |c| ^ n := by
      rw [smoothTransitionProductDerivativeBound, ← Finset.sum_mul]

/-- Each slow envelope is a product of two oppositely rescaled
transitions, so its order-n derivative costs exactly `tauP⁻ⁿ`. -/
theorem slowEnvelope_iteratedDeriv_bound
    {α q : ℝ} {Λ m : ℕ} {l : ℤ} {t : ℝ}
    (hτP : 0 < AVRegularity.ocTauP α q Λ m) (n : ℕ) :
    AVRegularity.ocTauP α q Λ m ^ n *
      |iteratedDeriv n (AVRegularity.slowEnvelope α q Λ m l) t| ≤
        smoothTransitionProductDerivativeBound n := by
  let τP := AVRegularity.ocTauP α q Λ m
  let τPP := AVRegularity.ocTauPP α q Λ m
  let A := ((l : ℝ) - 1 / 2) * τPP + τP
  let B := ((l : ℝ) + 1 / 2) * τPP - τP
  have hfirst (x : ℝ) : (x - ((l : ℝ) - 1 / 2) * τPP - τP) / τP =
      τP⁻¹ * x + (-A / τP) := by
    field_simp [ne_of_gt hτP]
    dsimp [A]
    ring
  have hsecond (x : ℝ) : (((l : ℝ) + 1 / 2) * τPP - τP - x) / τP =
      -τP⁻¹ * x + (B / τP) := by
    field_simp [ne_of_gt hτP]
    dsimp [B]
    ring
  have henv : AVRegularity.slowEnvelope α q Λ m l = fun x : ℝ =>
      Real.smoothTransition (τP⁻¹ * x + (-A / τP)) *
        Real.smoothTransition (-τP⁻¹ * x + (B / τP)) := by
    funext x
    unfold AVRegularity.slowEnvelope
    dsimp [τP, τPP, A, B]
    rw [hfirst, hsecond]
  rw [henv]
  have hprod := affine_smoothTransition_product_iteratedDeriv_bound
    n τP⁻¹ (-A / τP) (B / τP) t
  have habs : |τP⁻¹| = τP⁻¹ := abs_of_pos (inv_pos.mpr hτP)
  have hpow : τP ^ n * (τP⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hτP), one_pow]
  calc
    τP ^ n * |iteratedDeriv n
        (fun x : ℝ => Real.smoothTransition (τP⁻¹ * x + -A / τP) *
          Real.smoothTransition (-τP⁻¹ * x + B / τP)) t| ≤
      τP ^ n * (smoothTransitionProductDerivativeBound n * |τP⁻¹| ^ n) :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg hτP.le n)
    _ = smoothTransitionProductDerivativeBound n := by
      rw [habs]
      calc
        τP ^ n * (smoothTransitionProductDerivativeBound n * (τP⁻¹) ^ n) =
            smoothTransitionProductDerivativeBound n *
              (τP ^ n * (τP⁻¹) ^ n) := by ring
        _ = smoothTransitionProductDerivativeBound n := by rw [hpow, mul_one]

end AVRegularity.Velocity.Jets
end
end

section
@[expose] public section
namespace AVRegularity.Velocity.Jets

/-- A fast pulse has one of the two adjacent integer labels. -/
theorem fast_active_labels {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ t : ℝ} (hτ : 0 < τ) {k : ℤ}
    (hk : ζ ((t - (k : ℝ) * τ) / τ) ≠ 0) :
    k = ⌊t / τ⌋ ∨ k = ⌊t / τ⌋ + 1 := by
  have hs : (t - (k : ℝ) * τ) / τ ∈ tsupport ζ := subset_tsupport ζ hk
  have hi := hζ.2.2.1 hs
  have heq : (t - (k : ℝ) * τ) / τ = t / τ - (k : ℝ) := by
    field_simp
  rw [heq] at hi
  have hlo := Int.floor_le (t / τ)
  have hhi := Int.lt_floor_add_one (t / τ)
  have hkl : ⌊t / τ⌋ ≤ k := by
    by_contra h
    have hcast : (k : ℝ) + 1 ≤ (⌊t / τ⌋ : ℝ) := by
      exact_mod_cast (show k + 1 ≤ ⌊t / τ⌋ by omega)
    linarith [hi.2]
  have hku : k ≤ ⌊t / τ⌋ + 1 := by
    by_contra h
    have hcast : (⌊t / τ⌋ : ℝ) + 2 ≤ (k : ℝ) := by
      exact_mod_cast (show ⌊t / τ⌋ + 2 ≤ k by omega)
    linarith [hi.1]
  omega

/-- Uniform finite overlap of the fast cutoff family. -/
theorem fast_active_finite_card {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    {k : ℤ | ζ ((t - (k : ℝ) * τ) / τ) ≠ 0}.Finite ∧
      Set.ncard {k : ℤ | ζ ((t - (k : ℝ) * τ) / τ) ≠ 0} ≤ 2 := by
  classical
  let S : Set ℤ := {⌊t / τ⌋, ⌊t / τ⌋ + 1}
  have hsub : {k : ℤ | ζ ((t - (k : ℝ) * τ) / τ) ≠ 0} ⊆ S := by
    intro k hk
    rcases fast_active_labels hζ hτ hk with h | h <;> simp [S, h]
  have hfin : S.Finite := (Set.finite_singleton _).insert _
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  dsimp [S]
  rw [Set.ncard_pair (by omega : (⌊t / τ⌋ : ℤ) ≠ ⌊t / τ⌋ + 1)]

/-- The support restriction in the fast profile `IsFastProfile` gives its physical window. -/
theorem fast_support_window {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) (k : ℤ) (t : ℝ)
    (hk : ζ ((t - (k : ℝ) * τ) / τ) ≠ 0) :
    |t - (k : ℝ) * τ| ≤ (2 / 3 : ℝ) * τ := by
  have hs := hζ.2.2.1 (subset_tsupport ζ hk)
  have ha := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
  rwa [abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at ha

/-- A nonzero two-transition envelope lies strictly inside its margins. -/
theorem slow_support_window {α q : ℝ} {Λ m : ℕ} {l : ℤ} {t : ℝ}
    (hp : 0 < ocTauP α q Λ m) (hne : slowEnvelope α q Λ m l t ≠ 0) :
    ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m < t ∧
      t < ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m := by
  have hleft : 0 < (t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m -
      ocTauP α q Λ m) / ocTauP α q Λ m := by
    by_contra h
    apply hne
    rw [slowEnvelope, Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)]
    simp
  have hright : 0 < (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m -
      ocTauP α q Λ m - t) / ocTauP α q Λ m := by
    by_contra h
    apply hne
    rw [slowEnvelope, Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)]
    simp
  have hL := (div_pos_iff_of_pos_right hp).mp hleft
  have hR := (div_pos_iff_of_pos_right hp).mp hright
  constructor <;> linarith

/-- Positivity of the middle time scale, including level zero. -/
theorem ocTauP_pos {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    0 < ocTauP α q Λ m := by
  unfold ocTauP
  exact div_pos (AVRegularity.Construction.Stream.ocTauPP_pos hΛ)
    (by exact_mod_cast (show 0 < ocL α q Λ m by simp [ocL]))

end AVRegularity.Velocity.Jets
end
end

section
@[expose] public section
namespace AVRegularity.Velocity

/-! Abstract scale and cutoff interface for the OC all-order jet argument. -/

/-- The scalar, label, and cutoff data consumed by the all-order stream argument.
This record intentionally contains no stream-jet or inverse-flow conclusion. -/
structure JetRecursionData (α s q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) where
  epsilon : ℕ → ℝ
  tau : ℕ → ℝ
  tauP : ℕ → ℝ
  tauPP : ℕ → ℝ
  velocityAmplitude : ℕ → ℝ
  shearAmplitude : ℕ → ℝ
  label : ℕ → ℤ → ℤ
  fastCutoff : ℕ → ℤ → ℝ → ℝ
  slowCutoff : ℕ → ℤ → ℝ → ℝ
  /-- The source large-cutoff derivative constant `Chat`. -/
  Chat : ℝ
  /-- The source fine-cutoff derivative constant `Czeta`. -/
  Czeta : ℝ
  radius : ℕ → ℝ
  jetSize : ℕ → ℝ
  hαpos : 0 < α
  hαlt : α < 1 / 3
  hspos : 0 < s
  hslt : s < (1 - α) / 2
  hq : IsAdmissibleQ α s q
  hΛ : 128 ≤ Λ
  /-- The source `Ingredients.Nstar_ge_256` scale consequence. -/
  nstar_ge_256 : 256 ≤ AVenhance.Nstar (1 + α)
  hζ : IsFastProfile ζ
  epsilon_eq_oc : ∀ m, epsilon m = ocEpsilon q Λ m
  tau_eq_oc : ∀ m, tau m = ocTau α q Λ m
  tauP_eq_oc : ∀ m, tauP m = ocTauP α q Λ m
  tauPP_eq_oc : ∀ m, tauPP m = ocTauPP α q Λ m
  epsilon_zero : epsilon 0 = 1
  epsilon_pos : ∀ m, 0 < epsilon m
  epsilon_le_one : ∀ m, epsilon m ≤ 1
  epsilon_ratio : ∀ m, 1 ≤ m →
    (Λ : ℝ) ≤ epsilon (m - 1) / epsilon m
  epsilon_gap_ratio : ∀ m j, j ≤ m →
    epsilon m / epsilon j ≤ (1 / 128 : ℝ) ^ (m - j)
  tau_pos : ∀ m, 1 ≤ m → 0 < tau m
  tauP_pos : ∀ m, 1 ≤ m → 0 < tauP m
  tauPP_pos : ∀ m, 1 ≤ m → 0 < tauPP m
  velocityAmplitude_eq : ∀ m, velocityAmplitude m = epsilon m ^ (α - 1)
  shearAmplitude_eq : ∀ m, shearAmplitude m = epsilon m ^ (1 + α)
  block_small : ∀ m, 1 ≤ m →
    velocityAmplitude (m - 1) * tauPP m ≤
      (2 : ℝ) ^ (-25 : ℤ) * epsilon (m - 1) ^ (2 * ocDelta α q)
  cutoff_speed : ∀ m, 1 ≤ m → epsilon m / tau m ≤ (2 : ℝ) ^ 35
  fast_smooth : ∀ m k, ContDiff ℝ (⊤ : ℕ∞) (fastCutoff m k)
  slow_smooth : ∀ m l, ContDiff ℝ (⊤ : ℕ∞) (slowCutoff m l)
  fast_support : ∀ m k t, fastCutoff m k t ≠ 0 →
    |t - (k : ℝ) * tau m| ≤ (2 / 3 : ℝ) * tau m
  slow_support : ∀ m l t, slowCutoff m l t ≠ 0 →
    ((l : ℝ) - 1 / 2) * tauPP m + tauP m < t ∧
      t < ((l : ℝ) + 1 / 2) * tauPP m - tauP m
  one_le_Chat : 1 ≤ Chat
  one_le_Czeta : 1 ≤ Czeta
  slowEnvelope_derivative_bound : ∀ m, 1 ≤ m → ∀ l j,
    j ≤ AVenhance.Nstar (1 + α) → ∀ t,
      tauP m ^ j * |iteratedDeriv j (AVRegularity.slowEnvelope α q Λ m l) t| ≤ Chat
  fast_profile_derivative_bound : ∀ j,
    j ≤ AVenhance.Nstar (1 + α) → ∀ t,
      |iteratedDeriv j ζ t| ≤ Czeta
  fast_active_finite : ∀ m t,
    {k : ℤ | fastCutoff m k t ≠ 0}.Finite
  fast_active_card : ∀ m t,
    Set.ncard {k : ℤ | fastCutoff m k t ≠ 0} ≤ 2
  fast_derivative_bound : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m k t,
    tau m ^ n * |iteratedDeriv n (fastCutoff m k) t| ≤ C
  slow_derivative_bound : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m l t,
    tauP m ^ n * |iteratedDeriv n (slowCutoff m l) t| ≤ C
  radius_zero : radius 0 = 1
  jetSize_zero : jetSize 0 = 1
  radius_step : ∀ m, radius (m + 1) =
    (9 / 4) * radius m + 2 ^ 7 * (epsilon (m + 1))⁻¹
  jetSize_step : ∀ m, jetSize (m + 1) = jetSize m +
    2 ^ 7 * velocityAmplitude (m + 1) * epsilon (m + 1) ^ 2 * radius m ^ 2 +
      2 ^ 18 * velocityAmplitude (m + 1)

/-- The one-step wavelength contraction supplied by `JetRecursionData`. -/
theorem JetRecursionData.epsilon_succ_le {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) :
    D.epsilon (m + 1) ≤ D.epsilon m / (Λ : ℝ) := by
  have hratio := D.epsilon_ratio (m + 1) (by omega)
  have hratio' : (Λ : ℝ) ≤ D.epsilon m / D.epsilon (m + 1) := by
    simpa using hratio
  have hnext : 0 < D.epsilon (m + 1) := D.epsilon_pos _
  have hΛbound : 128 ≤ Λ := D.hΛ
  have hΛnat : 0 < Λ := by omega
  have hΛ : 0 < (Λ : ℝ) := by exact_mod_cast hΛnat
  have hmul := (le_div_iff₀ hnext).mp hratio'
  have htarget : D.epsilon (m + 1) * (Λ : ℝ) ≤ D.epsilon m := by
    simpa [mul_comm] using hmul
  exact (le_div_iff₀ hΛ).2 htarget

end AVRegularity.Velocity
end
end

section
@[expose] public section
namespace AVRegularity.Velocity.Jets

/-- Canonical radius majorant, with the source recurrence. -/
noncomputable def ocJetRadius (q : ℝ) (Λ : ℕ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => (9 / 4) * ocJetRadius q Λ m + 2 ^ 7 * (ocEpsilon q Λ (m + 1))⁻¹

/-- Canonical stream-jet amplitude majorant. -/
noncomputable def ocJetSize (α q : ℝ) (Λ : ℕ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => ocJetSize α q Λ m +
      2 ^ 7 * ocA α q Λ (m + 1) * ocEpsilon q Λ (m + 1) ^ 2 *
        ocJetRadius q Λ m ^ 2 + 2 ^ 18 * ocA α q Λ (m + 1)

/-- Iterating the adjacent wavelength separation gives the all-level ratio. -/
theorem ocEpsilon_gap_ratio {q : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (m j : ℕ) (hj : j ≤ m) :
    ocEpsilon q Λ m / ocEpsilon q Λ j ≤ (1 / 128 : ℝ) ^ (m - j) := by
  have hstep (n : ℕ) : ocEpsilon q Λ (n + 1) ≤
      ocEpsilon q Λ n * (1 / 128 : ℝ) := by
    have hratio := Scales.epsilon_ratio_lower hq hΛ (by omega : 1 ≤ n + 1)
    have hratio' : (Λ : ℝ) ≤ ocEpsilon q Λ n / ocEpsilon q Λ (n + 1) := by
      simpa using hratio
    have hmul := (le_div_iff₀ (Scales.epsilon_basic hq hΛ).1).mp hratio'
    have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    have hbound : 128 * ocEpsilon q Λ (n + 1) ≤ ocEpsilon q Λ n :=
      (mul_le_mul_of_nonneg_right hΛr (Scales.epsilon_basic hq hΛ).1.le).trans hmul
    linarith
  have hdecay (k : ℕ) : ocEpsilon q Λ (j + k) ≤
      ocEpsilon q Λ j * (1 / 128 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          ocEpsilon q Λ (j + (k + 1)) ≤
              ocEpsilon q Λ (j + k) * (1 / 128 : ℝ) := by
            simpa only [Nat.add_assoc] using hstep (j + k)
          _ ≤ (ocEpsilon q Λ j * (1 / 128 : ℝ) ^ k) * (1 / 128 : ℝ) :=
            mul_le_mul_of_nonneg_right ih (by norm_num)
          _ = ocEpsilon q Λ j * (1 / 128 : ℝ) ^ (k + 1) := by
            rw [pow_succ, mul_assoc]
  apply (div_le_iff₀ (Scales.epsilon_basic hq hΛ).1).2
  simpa only [Nat.add_sub_of_le hj, mul_comm] using hdecay (m - j)

/-- Finite-order derivative bounds can be combined into one constant. -/
theorem finite_derivative_budget {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    1 ≤ 1 + ∑ n ∈ Finset.range (N + 1), f n ∧
      ∀ n, n ≤ N → f n ≤ 1 + ∑ k ∈ Finset.range (N + 1), f k := by
  have hsum : 0 ≤ ∑ n ∈ Finset.range (N + 1), f n :=
    Finset.sum_nonneg (fun n _ => hf n)
  refine ⟨by linarith, ?_⟩
  intro n hn
  have hle := Finset.single_le_sum (fun k _ => hf k)
    (show n ∈ Finset.range (N + 1) by simp; omega)
  linarith

end AVRegularity.Velocity.Jets
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open scoped BigOperators
namespace AVRegularity.Velocity.Jets

/-! Conditional spatial barNorm induction over the abstract OC scale interface. -/

/-- The first all-order increment estimate consumed by the spatial stream induction.
This is a conditional interface; the inverse-flow argument must derive it. -/
def JetIncrementBounds {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ, ∀ n : ℕ,
    AVenhance.barNorm n (2 ^ 7 * (D.epsilon m)⁻¹)
      (Φ m t - Φ (m - 1) t) ≤ ENNReal.ofReal (10 * D.epsilon m ^ (1 + α))

/-- The scale ratio turns an order-n increment into the geometric weight used
to sum it at the target level. -/
theorem epsilon_gap_power_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {m j n : ℕ} (hjm : j ≤ m) (hn : 2 ≤ n) :
    (D.epsilon m / D.epsilon j) ^ ((n : ℝ) - (1 + α)) ≤
      (1 / 2 : ℝ) ^ (m - j) := by
  have hej : 0 < D.epsilon j := D.epsilon_pos j
  have hem : 0 < D.epsilon m := D.epsilon_pos m
  have hratio := D.epsilon_gap_ratio m j hjm
  have hrpos : 0 < D.epsilon m / D.epsilon j := div_pos hem hej
  have hbase : 0 < (1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hratio' : D.epsilon m / D.epsilon j ≤
      (1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast] using hratio
  have hratioPow := Real.rpow_le_rpow hrpos.le hratio'
    (by
      have hncast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hexpPos : 0 < (n : ℝ) - (1 + α) := by linarith [D.hαlt, hncast]
      exact hexpPos.le)
  have hexp : (2 : ℝ) / 3 ≤ (n : ℝ) - (1 + α) := by
    have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [D.hαlt]
  have hpowBaseLe : (1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hratioExp := Real.rpow_le_rpow_of_exponent_ge hbase hpowBaseLe hexp
  have hsmall : (1 / 128 : ℝ) ^ (2 / 3 : ℝ) ≤ 1 / 2 := by
    calc
      (1 / 128 : ℝ) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (-(14 / 3 : ℝ)) := by
        rw [show (1 / 128 : ℝ) = (2 : ℝ) ^ (-7 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hpowq : ((1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ)) ^ (2 / 3 : ℝ) =
      ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ (m - j) := by
    have hx : 0 ≤ (1 / 128 : ℝ) := by norm_num
    calc
      ((1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ)) ^ (2 / 3 : ℝ) =
          (1 / 128 : ℝ) ^ (((m - j : ℕ) : ℝ) * (2 / 3 : ℝ)) :=
        (Real.rpow_mul hx _ _).symm
      _ = (1 / 128 : ℝ) ^ ((2 / 3 : ℝ) * ((m - j : ℕ) : ℝ)) := by
        congr 1
        ring
      _ = ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ ((m - j : ℕ) : ℝ) :=
        Real.rpow_mul hx _ _
      _ = ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ (m - j) := by
        rw [Real.rpow_natCast]
  have hpowHalf : ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ (m - j) ≤
      (1 / 2 : ℝ) ^ (m - j) :=
    pow_le_pow_left₀ (by positivity) hsmall (m - j)
  have hnat : ((1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ)) ^ (2 / 3 : ℝ) ≤
      (1 / 2 : ℝ) ^ (m - j) := by
    rw [hpowq]
    exact hpowHalf
  exact hratioPow.trans (hratioExp.trans hnat)

/-- The telescoping sum of all-order increments bounds the stream seminorm at
any positive target radius. -/
theorem barNorm_telescope_bound_of_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦzero : ∀ t x, Φ 0 t x = 0)
    (hΦsmooth : ∀ m t, ContDiff ℝ (⊤ : ℕ∞) (Φ m t))
    (hinc : JetIncrementBounds D Φ) (m : ℕ) (t : ℝ) (n : ℕ)
    {R : ℝ} (hR : 0 < R) :
    AVenhance.barNorm n R (Φ m t) ≤ ENNReal.ofReal (∑ j ∈ Finset.range m,
      (10 * D.epsilon (j + 1) ^ (1 + α)) *
        ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n) := by
  let d : ℕ → Vec 2 → ℝ := fun j => Φ (j + 1) t - Φ j t
  have hsumId : Φ m t = ∑ j ∈ Finset.range m, d j := by
    induction m with
    | zero =>
        funext x
        simp [d, hΦzero t x]
    | succ m ih =>
        rw [Finset.sum_range_succ]
        rw [← ih]
        funext x
        simp [d]
  have hfun : ∀ j ∈ Finset.range m, ContDiff ℝ n (d j) := by
    intro j _
    have hl : ContDiff ℝ (n : ℕ∞) (Φ (j + 1) t) :=
      (hΦsmooth (j + 1) t).of_le (by simp)
    have hr : ContDiff ℝ (n : ℕ∞) (Φ j t) :=
      (hΦsmooth j t).of_le (by simp)
    exact hl.sub hr
  have hsum := barNorm_sum_le (Finset.range m) d n R hfun
  have hnonneg : ∀ j ∈ Finset.range m,
      0 ≤ 10 * D.epsilon (j + 1) ^ (1 + α) *
        ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n := by
    intro j hj
    have he := D.epsilon_pos (j + 1)
    positivity
  rw [hsumId]
  calc
    AVenhance.barNorm n R (∑ j ∈ Finset.range m, d j) ≤
        ∑ j ∈ Finset.range m, AVenhance.barNorm n R (d j) := hsum
    _ ≤ ∑ j ∈ Finset.range m,
        ENNReal.ofReal (10 * D.epsilon (j + 1) ^ (1 + α) *
          ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      have he := D.epsilon_pos (j + 1)
      have hRj : 0 < 2 ^ 7 * (D.epsilon (j + 1))⁻¹ := by positivity
      have hbar := hinc (j + 1) (by omega) t n
      have hbar' : AVenhance.barNorm n (2 ^ 7 * (D.epsilon (j + 1))⁻¹) (d j) ≤
          ENNReal.ofReal (10 * D.epsilon (j + 1) ^ (1 + α)) := by
        simpa [d] using hbar
      have hK : 0 ≤ 10 * D.epsilon (j + 1) ^ (1 + α) := by positivity
      have hdiff : ContDiff ℝ (n : ℕ∞)
          (fun x : Vec 2 => Φ (j + 1) t x - Φ j t x) := by
        exact ((hΦsmooth (j + 1) t).sub (hΦsmooth j t)).of_le (by simp)
      have hscaled := barNorm_radius_change hdiff hRj hR
      calc
        AVenhance.barNorm n R (d j) =
            AVenhance.barNorm n (2 ^ 7 * (D.epsilon (j + 1))⁻¹) (d j) *
              ENNReal.ofReal ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n :=
          hscaled
        _ ≤ ENNReal.ofReal (10 * D.epsilon (j + 1) ^ (1 + α)) *
              ENNReal.ofReal ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n :=
          mul_le_mul_of_nonneg_right hbar' (by positivity)
        _ = ENNReal.ofReal (10 * D.epsilon (j + 1) ^ (1 + α) *
              ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n) := by
            rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hK]
    _ = ENNReal.ofReal (∑ j ∈ Finset.range m,
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
          ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / R) ^ n) := by
      rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]

private theorem rpow_scale_factorization {a b β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) :
    a ^ β * (b / a) ^ n = b ^ β * (b / a) ^ ((n : ℝ) - β) := by
  have hab : 0 < b / a := div_pos hb ha
  rw [← Real.rpow_natCast (b / a) n]
  calc
    a ^ β * (b / a) ^ (n : ℝ) =
        a ^ β * ((b / a) ^ β * (b / a) ^ ((n : ℝ) - β)) := by
          rw [← Real.rpow_add hab]
          congr 1
          exact congrArg (fun z : ℝ => (b / a) ^ z) (by ring)
    _ = (a ^ β * (b / a) ^ β) * (b / a) ^ ((n : ℝ) - β) := by ring
    _ = b ^ β * (b / a) ^ ((n : ℝ) - β) := by
      rw [Real.div_rpow hb.le ha.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos ha β)]

private theorem half_gap_sum_le_two (m : ℕ) :
    (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (m - (j + 1))) ≤ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hprev :
          (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ ((m + 1) - (j + 1))) =
            (1 / 2 : ℝ) * ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (m - (j + 1)) := by
        calc
          (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ ((m + 1) - (j + 1))) =
              ∑ j ∈ Finset.range m,
                (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (m - (j + 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [show (m + 1) - (j + 1) = (m - (j + 1)) + 1 by
              have := Finset.mem_range.mp hj
              omega, pow_succ]
            ring
          _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.range m,
                (1 / 2 : ℝ) ^ (m - (j + 1)) := by rw [Finset.mul_sum]
      rw [hprev]
      rw [show (m + 1) - (m + 1) = 0 by omega, pow_zero]
      calc
        (1 / 2 : ℝ) * (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (m - (j + 1))) + 1 ≤
            (1 / 2 : ℝ) * 2 + 1 := by
              exact add_le_add (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
        _ = 2 := by norm_num

/-- The abstract scale gap closes the high-order part of the upstream
all-order stream summation, conditional on all-order increment jets. -/
theorem barNorm_high_order_bound_of_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦzero : ∀ t x, Φ 0 t x = 0)
    (hΦsmooth : ∀ m t, ContDiff ℝ (⊤ : ℕ∞) (Φ m t))
    (hinc : JetIncrementBounds D Φ) (m : ℕ)
    (t : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    AVenhance.barNorm n (2 ^ 7 * (D.epsilon m)⁻¹) (Φ m t) ≤
      ENNReal.ofReal (20 * D.epsilon m ^ (1 + α)) := by
  have hR : 0 < (2 : ℝ) ^ 7 * (D.epsilon m)⁻¹ :=
    mul_pos (by norm_num) (inv_pos.mpr (D.epsilon_pos m))
  have htel := barNorm_telescope_bound_of_increment_bounds
    D hΦzero hΦsmooth hinc m t n (R := (2 : ℝ) ^ 7 * (D.epsilon m)⁻¹) hR
  have hsum :
      (∑ j ∈ Finset.range m,
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
          ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) /
            (2 ^ 7 * (D.epsilon m)⁻¹)) ^ n) ≤
        20 * D.epsilon m ^ (1 + α) := by
    have hterms : ∀ j ∈ Finset.range m,
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
            ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) /
              (2 ^ 7 * (D.epsilon m)⁻¹)) ^ n ≤
          (10 * D.epsilon m ^ (1 + α)) *
            (1 / 2 : ℝ) ^ (m - (j + 1)) := by
      intro j hj
      have hjm : j + 1 ≤ m := by have := Finset.mem_range.mp hj; omega
      have haj : 0 < D.epsilon (j + 1) := D.epsilon_pos _
      have hb : 0 < D.epsilon m := D.epsilon_pos _
      have hratio :
          ((2 : ℝ) ^ 7 * (D.epsilon (j + 1))⁻¹) /
            ((2 : ℝ) ^ 7 * (D.epsilon m)⁻¹) = D.epsilon m / D.epsilon (j + 1) := by
        field_simp [ne_of_gt haj, ne_of_gt hb]
      rw [hratio]
      have hgap := epsilon_gap_power_bound D hjm hn
      have hfactor : D.epsilon (j + 1) ^ (1 + α) *
          (D.epsilon m / D.epsilon (j + 1)) ^ n =
        D.epsilon m ^ (1 + α) *
          (D.epsilon m / D.epsilon (j + 1)) ^ ((n : ℝ) - (1 + α)) :=
        rpow_scale_factorization haj hb (β := 1 + α) n
      have hscale : D.epsilon (j + 1) ^ (1 + α) *
          (D.epsilon m / D.epsilon (j + 1)) ^ n ≤
        D.epsilon m ^ (1 + α) * (1 / 2 : ℝ) ^ (m - (j + 1)) := by
        rw [hfactor]
        exact mul_le_mul_of_nonneg_left hgap
          (Real.rpow_nonneg hb.le (1 + α))
      calc
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
            (D.epsilon m / D.epsilon (j + 1)) ^ n =
          10 * (D.epsilon (j + 1) ^ (1 + α) *
            (D.epsilon m / D.epsilon (j + 1)) ^ n) := by ring
        _ ≤ (10 * D.epsilon m ^ (1 + α)) *
            (1 / 2 : ℝ) ^ (m - (j + 1)) := by
          calc
            10 * (D.epsilon (j + 1) ^ (1 + α) *
                (D.epsilon m / D.epsilon (j + 1)) ^ n) ≤
              10 * (D.epsilon m ^ (1 + α) *
                (1 / 2 : ℝ) ^ (m - (j + 1))) :=
              mul_le_mul_of_nonneg_left hscale (by norm_num)
            _ = (10 * D.epsilon m ^ (1 + α)) *
                (1 / 2 : ℝ) ^ (m - (j + 1)) := by ring
    calc
      (∑ j ∈ Finset.range m,
          (10 * D.epsilon (j + 1) ^ (1 + α)) *
            ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) /
              (2 ^ 7 * (D.epsilon m)⁻¹)) ^ n) ≤
        ∑ j ∈ Finset.range m,
          (10 * D.epsilon m ^ (1 + α)) *
            (1 / 2 : ℝ) ^ (m - (j + 1)) :=
        Finset.sum_le_sum (fun j hj => hterms j hj)
      _ = (10 * D.epsilon m ^ (1 + α)) *
          ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (m - (j + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ 20 * D.epsilon m ^ (1 + α) := by
        have heps : 0 < D.epsilon m := D.epsilon_pos m
        have he : 0 ≤ 10 * D.epsilon m ^ (1 + α) := by positivity
        have hgeom := half_gap_sum_le_two m
        calc
          (10 * D.epsilon m ^ (1 + α)) *
              ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (m - (j + 1)) ≤
            (10 * D.epsilon m ^ (1 + α)) * 2 := mul_le_mul_of_nonneg_left hgeom he
          _ = 20 * D.epsilon m ^ (1 + α) := by ring
  exact htel.trans (ENNReal.ofReal_le_ofReal hsum)

end AVRegularity.Velocity.Jets
end
end

section
@[expose] public section
namespace AVRegularity.Velocity

/-! The primitive data of the all-order jet recursion, instantiated by the construction. -/

open Jets

/-- The scales and profiles of the construction satisfy every primitive jet-recursion field.
The finite cutoff budgets depend on the profile and the order, while the radius
and amplitude are the explicit source recurrences. -/
noncomputable def ocJetRecursionData
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    JetRecursionData α s q Λ ζ where
  epsilon := ocEpsilon q Λ
  tau := ocTau α q Λ
  tauP := ocTauP α q Λ
  tauPP := ocTauPP α q Λ
  velocityAmplitude := ocA α q Λ
  shearAmplitude := fun m => ocEpsilon q Λ m ^ (1 + α)
  label := ocLabel α q Λ
  fastCutoff := fun m k t => ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)
  slowCutoff := slowEnvelope α q Λ
  Chat := 1 + ∑ j ∈ Finset.range (AVenhance.Nstar (1 + α) + 1),
    smoothTransitionProductDerivativeBound j
  Czeta := 1 + ∑ j ∈ Finset.range (AVenhance.Nstar (1 + α) + 1),
    fastProfileDerivativeBound hζ j
  radius := ocJetRadius q Λ
  jetSize := ocJetSize α q Λ
  hαpos := hα₀
  hαlt := hα₁
  hspos := hs₀
  hslt := hs₁
  hq := hq
  hΛ := hΛ
  nstar_ge_256 := AVenhance.Infra.Ingredients.Nstar_ge_256 (by linarith) (by linarith)
  hζ := hζ
  epsilon_eq_oc := fun _ => rfl
  tau_eq_oc := fun _ => rfl
  tauP_eq_oc := fun _ => rfl
  tauPP_eq_oc := fun _ => rfl
  epsilon_zero := by simp [ocEpsilon]
  epsilon_pos := fun _ => (Scales.epsilon_basic hq.1 hΛ).1
  epsilon_le_one := fun _ => (Scales.epsilon_basic hq.1 hΛ).2.1
  epsilon_ratio := fun _ hm => Scales.epsilon_ratio_lower hq.1 hΛ hm
  epsilon_gap_ratio := ocEpsilon_gap_ratio hq.1 hΛ
  tau_pos := fun _ _ => AVRegularity.Construction.Stream.ocTau_pos (by omega)
  tauP_pos := fun _ _ => Jets.ocTauP_pos (by omega)
  tauPP_pos := fun _ _ => AVRegularity.Construction.Stream.ocTauPP_pos (by omega)
  velocityAmplitude_eq := by intro m; unfold ocA; congr 1; ring
  shearAmplitude_eq := fun _ => rfl
  block_small := fun _ hm =>
    (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm).2.2.2.2.1
  cutoff_speed := fun _ hm =>
    (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm).2.2.2.2.2.1
  fast_smooth := by
    intro m k
    exact hζ.1.comp (by fun_prop)
  slow_smooth := by
    intro m l
    unfold slowEnvelope
    fun_prop
  fast_support := by
    intro m k t hk
    exact fast_support_window hζ (AVRegularity.Construction.Stream.ocTau_pos (by omega)) k t hk
  slow_support := by
    intro m l t ht
    exact slow_support_window (Jets.ocTauP_pos (by omega)) ht
  one_le_Chat := (finite_derivative_budget smoothTransitionProductDerivativeBound_nonneg _).1
  one_le_Czeta := (finite_derivative_budget (fastProfileDerivativeBound_nonneg hζ) _).1
  slowEnvelope_derivative_bound := by
    intro m hm l j hj t
    exact (slowEnvelope_iteratedDeriv_bound (Jets.ocTauP_pos (by omega)) j).trans
      ((finite_derivative_budget smoothTransitionProductDerivativeBound_nonneg _).2 j hj)
  fast_profile_derivative_bound := by
    intro j hj t
    exact (fastProfileDerivativeBound_spec hζ j t).trans
      ((finite_derivative_budget (fastProfileDerivativeBound_nonneg hζ) _).2 j hj)
  fast_active_finite := fun m t =>
    (fast_active_finite_card hζ (AVRegularity.Construction.Stream.ocTau_pos (by omega)) t).1
  fast_active_card := fun m t =>
    (fast_active_finite_card hζ (AVRegularity.Construction.Stream.ocTau_pos (by omega)) t).2
  fast_derivative_bound := by
    intro n
    refine ⟨fastProfileDerivativeBound hζ n, fastProfileDerivativeBound_nonneg hζ n, ?_⟩
    intro m k t
    exact fastCutoff_iteratedDeriv_bound hζ
      (AVRegularity.Construction.Stream.ocTau_pos (by omega)) k n t
  slow_derivative_bound := by
    intro n
    refine ⟨smoothTransitionProductDerivativeBound n,
      smoothTransitionProductDerivativeBound_nonneg n, ?_⟩
    intro m l t
    exact slowEnvelope_iteratedDeriv_bound (Jets.ocTauP_pos (by omega)) n
  radius_zero := rfl
  jetSize_zero := rfl
  radius_step := fun _ => rfl
  jetSize_step := fun _ => rfl

end AVRegularity.Velocity
end
end
