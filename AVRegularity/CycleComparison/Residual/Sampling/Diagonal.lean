-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TimeIntegration
import Mathlib.Analysis.Calculus.Deriv.Pi

@[expose] public section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Calculus of `orderedDerivative`: the word jets are the iterated Fréchet derivatives evaluated
on (reversed) basis vectors, hence continuous, smooth, and homogeneous under dilation. -/

namespace Sampling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_zero (β : DerivativeWord2 0) (g : Vec 2 → E) :
    orderedDerivative β g = g := by
  simp [orderedDerivative]

theorem orderedDerivative_snoc {m : ℕ} (β : DerivativeWord2 m) (i : Fin 2) (g : Vec 2 → E) :
    orderedDerivative (Fin.snoc β i : DerivativeWord2 (m + 1)) g =
      fun x => fderiv ℝ (orderedDerivative β g) x (basisVec i) := by
  simp only [orderedDerivative, List.ofFn_succ', List.concat_eq_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_orderedDerivative (n : ℕ) {m : ℕ} (β : DerivativeWord2 m) (g : Vec 2 → E)
    (hg : ContDiff ℝ ((n + m : ℕ) : ℕ∞) g) :
    ContDiff ℝ (n : ℕ∞) (orderedDerivative β g) := by
  induction m generalizing n with
  | zero =>
    rw [orderedDerivative_zero]
    simpa using hg
  | succ m ih =>
    have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last m)) := (Fin.snoc_init_self β).symm
    rw [hβ, orderedDerivative_snoc]
    have h1 : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (orderedDerivative (Fin.init β) g) :=
      ih (n + 1) (Fin.init β) (by
        have : n + 1 + m = n + (m + 1) := by omega
        rw [this]; exact hg)
    have h2 : ContDiff ℝ (n : ℕ∞) (fderiv ℝ (orderedDerivative (Fin.init β) g)) :=
      h1.fderiv_right (by exact_mod_cast le_refl _)
    exact h2.clm_apply contDiff_const

theorem orderedDerivative_eq_iteratedFDeriv {m : ℕ} (β : DerivativeWord2 m) (g : Vec 2 → E)
    (hg : ContDiff ℝ (m : ℕ∞) g) :
    orderedDerivative β g =
      fun x => iteratedFDeriv ℝ m g x (fun k => basisVec (β (Fin.rev k))) := by
  induction m with
  | zero =>
    rw [orderedDerivative_zero]
    funext x
    simp [iteratedFDeriv_zero_apply]
  | succ m ih =>
    have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last m)) := (Fin.snoc_init_self β).symm
    have hg' : ContDiff ℝ (m : ℕ∞) g := hg.of_le (by exact_mod_cast Nat.le_succ m)
    have ih' := ih (Fin.init β) hg'
    rw [hβ, orderedDerivative_snoc, ih']
    funext x
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ m g) :=
      hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m)
    rw [iteratedFDeriv_succ_apply_left]
    set w : Fin m → Vec 2 := fun k => basisVec (Fin.init β (Fin.rev k)) with hw
    have hA : HasFDerivAt (fun y => iteratedFDeriv ℝ m g y w)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Vec 2) E w).comp
          (fderiv ℝ (iteratedFDeriv ℝ m g) x)) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Vec 2) E w).hasFDerivAt.comp x
        (hdiff x).hasFDerivAt
    rw [hA.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
    congr 3
    · simp [Fin.snoc_last, Fin.rev_zero]
    · funext k
      simp [hw, Fin.tail, Fin.init, Fin.rev_succ, Fin.snoc_castSucc]

theorem continuous_orderedDerivative_uncurry {m : ℕ} (β : DerivativeWord2 m)
    (f : Vec 2 → Vec 2 → E) (hf : ∀ y, ContDiff ℝ (m : ℕ∞) (fun X => f X y))
    (hc : Continuous (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ m (fun X => f X p.2) p.1)) :
    Continuous (fun p : Vec 2 × Vec 2 => orderedDerivative β (fun X => f X p.2) p.1) := by
  have : (fun p : Vec 2 × Vec 2 => orderedDerivative β (fun X => f X p.2) p.1) =
      fun p => iteratedFDeriv ℝ m (fun X => f X p.2) p.1 (fun k => basisVec (β (Fin.rev k))) := by
    funext p
    rw [orderedDerivative_eq_iteratedFDeriv β _ (hf p.2)]
  rw [this]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Vec 2) E
    (fun k => basisVec (β (Fin.rev k)))).continuous.comp hc

theorem orderedDerivative_comp_smul {m : ℕ} (β : DerivativeWord2 m) (g : Vec 2 → E)
    (hg : ContDiff ℝ (m : ℕ∞) g) (ρ : ℝ) (X : Vec 2) :
    orderedDerivative β (fun X' => g (ρ • X')) X = ρ ^ m • orderedDerivative β g (ρ • X) := by
  have hg' : ContDiff ℝ (m : ℕ∞) (fun X' => g (ρ • X')) :=
    hg.comp (contDiff_const_smul ρ)
  rw [orderedDerivative_eq_iteratedFDeriv β _ hg', orderedDerivative_eq_iteratedFDeriv β _ hg]
  have h := (ρ • ContinuousLinearMap.id ℝ (Vec 2)).iteratedFDeriv_comp_right hg X
    (i := m) le_rfl
  have h2 : (fun X' => g (ρ • X')) = g ∘ (ρ • ContinuousLinearMap.id ℝ (Vec 2)) := by
    funext X'; simp
  simp only [h2, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

end Sampling

alias orderedDerivative_comp_smul := Sampling.orderedDerivative_comp_smul

end AVRegularity
end

section
open Homogenization MeasureTheory Set
open scoped ENNReal Interval
namespace AVRegularity

/-! One-dimensional sampling: a point value is controlled by the mean and the total variation on an
interval, in `ℝ≥0∞`, and its restriction to coordinate lines of `Vec 2`. -/

namespace Sampling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem enorm_le_sampling_1d_complete [CompleteSpace E] (u u' : ℝ → E) (hd : ∀ t, HasDerivAt u (u' t) t)
    (hc : Continuous u') {a L : ℝ} (hL : 0 < L) {s : ℝ} (hs : s ∈ Icc a (a + L)) :
    ‖u s‖ₑ ≤ ENNReal.ofReal L⁻¹ * (∫⁻ r in Ioc a (a + L), ‖u r‖ₑ)
      + ∫⁻ r in Ioc a (a + L), ‖u' r‖ₑ := by
  set A : ℝ≥0∞ := ∫⁻ r in Ioc a (a + L), ‖u' r‖ₑ with hA
  have key : ∀ r ∈ Ioc a (a + L), ‖u s‖ₑ ≤ ‖u r‖ₑ + A := by
    intro r hr
    have hftc : ∫ x in r..s, u' x = u s - u r :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        (hc.intervalIntegrable _ _)
    have h1 : u s = u r + ∫ x in r..s, u' x := by rw [hftc]; abel
    have h2 : ‖∫ x in r..s, u' x‖ₑ ≤ A := by
      calc ‖∫ x in r..s, u' x‖ₑ ≤ ∫⁻ x in Ι r s, ‖u' x‖ₑ := by
            rcases le_total r s with h | h
            · rw [intervalIntegral.integral_of_le h, uIoc_of_le h]
              exact enorm_integral_le_lintegral_enorm _
            · rw [intervalIntegral.integral_of_ge h, uIoc_of_ge h, enorm_neg]
              exact enorm_integral_le_lintegral_enorm _
        _ ≤ A := by
            apply lintegral_mono_set
            intro x hx
            rcases le_total r s with h | h
            · rw [uIoc_of_le h] at hx
              exact ⟨lt_of_lt_of_le hr.1 hx.1.le, hx.2.trans hs.2⟩
            · rw [uIoc_of_ge h] at hx
              exact ⟨lt_of_le_of_lt hs.1 hx.1, hx.2.trans hr.2⟩
    calc ‖u s‖ₑ = ‖u r + ∫ x in r..s, u' x‖ₑ := by rw [← h1]
      _ ≤ ‖u r‖ₑ + ‖∫ x in r..s, u' x‖ₑ := enorm_add_le _ _
      _ ≤ ‖u r‖ₑ + A := by gcongr
  have hvol : ∫⁻ _ in Ioc a (a + L), ‖u s‖ₑ = ENNReal.ofReal L * ‖u s‖ₑ := by
    rw [setLIntegral_const, Real.volume_Ioc, mul_comm]; congr 2; ring_nf
  have hint : ENNReal.ofReal L * ‖u s‖ₑ ≤
      (∫⁻ r in Ioc a (a + L), ‖u r‖ₑ) + ENNReal.ofReal L * A := by
    rw [← hvol]
    calc ∫⁻ _ in Ioc a (a + L), ‖u s‖ₑ ≤ ∫⁻ r in Ioc a (a + L), (‖u r‖ₑ + A) :=
          setLIntegral_mono' measurableSet_Ioc key
      _ = (∫⁻ r in Ioc a (a + L), ‖u r‖ₑ) + ENNReal.ofReal L * A := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc,
            mul_comm A]
          congr 4; ring_nf
  have hLne : ENNReal.ofReal L ≠ 0 := by simpa using hL
  have hinv : ENNReal.ofReal L⁻¹ * ENNReal.ofReal L = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hL.le), inv_mul_cancel₀ hL.ne', ENNReal.ofReal_one]
  calc ‖u s‖ₑ = ENNReal.ofReal L⁻¹ * (ENNReal.ofReal L * ‖u s‖ₑ) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal L⁻¹ * ((∫⁻ r in Ioc a (a + L), ‖u r‖ₑ) + ENNReal.ofReal L * A) := by
        gcongr
    _ = _ := by rw [mul_add, ← mul_assoc, hinv, one_mul]

theorem enorm_le_sampling_1d (u u' : ℝ → E) (hd : ∀ t, HasDerivAt u (u' t) t)
    (hc : Continuous u') {a L : ℝ} (hL : 0 < L) {s : ℝ} (hs : s ∈ Icc a (a + L)) :
    ‖u s‖ₑ ≤ ENNReal.ofReal L⁻¹ * (∫⁻ r in Ioc a (a + L), ‖u r‖ₑ)
      + ∫⁻ r in Ioc a (a + L), ‖u' r‖ₑ := by
  let ι : E →L[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  have hι : ∀ x, ‖ι x‖ₑ = ‖x‖ₑ := fun x => by
    simp [ι, enorm_eq_nnnorm]
  have := enorm_le_sampling_1d_complete (fun r => ι (u r)) (fun r => ι (u' r))
    (fun t => ι.hasFDerivAt.comp_hasDerivAt t (hd t)) (ι.continuous.comp hc) hL hs
  simpa only [hι] using this

/-- Restriction of `enorm_le_sampling_1d` to the coordinate line through `P` in direction `j`. -/
theorem enorm_le_sampling_line (f : Vec 2 → E) (hf : ContDiff ℝ 1 f) (j : Fin 2) (P : Vec 2)
    {a L : ℝ} (hL : 0 < L) (hs : P j ∈ Icc a (a + L)) :
    ‖f P‖ₑ ≤ ENNReal.ofReal L⁻¹ * (∫⁻ r in Ioc a (a + L), ‖f (Function.update P j r)‖ₑ)
      + ∫⁻ r in Ioc a (a + L), ‖fderiv ℝ f (Function.update P j r) (basisVec j)‖ₑ := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hd : ∀ t, HasDerivAt (fun r => f (Function.update P j r))
      (fderiv ℝ f (Function.update P j t) (basisVec j)) t := by
    intro t
    have h1 : HasDerivAt (Function.update P j) (Pi.single j 1) t := hasDerivAt_update P j t
    exact (hdf _).hasFDerivAt.comp_hasDerivAt t h1
  have hc : Continuous (fun t => fderiv ℝ f (Function.update P j t) (basisVec j)) := by
    have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
    have h2 : Continuous (fun t : ℝ => Function.update P j t) := by
      exact continuous_const.update j continuous_id
    exact (h1.comp h2).clm_apply continuous_const
  have := enorm_le_sampling_1d (fun r => f (Function.update P j r)) _ hd hc hL
    (s := P j) hs
  simpa using this

end Sampling

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory Set
open scoped ENNReal NNReal
namespace AVRegularity

/-! Sampling on a square of `Vec 2`: for a `C²` field `u`, the value at a point of the square
`∏ [aᵢ, aᵢ + L]` is controlled by the `L²` norms of `u`, `∂₀u`, `∂₁u`, `∂₁∂₀u` on the square. -/

namespace Sampling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lintegral_pi_Ioc_two (g : Vec 2 → ℝ≥0∞) (hg : Measurable g) (a b : Vec 2) :
    ∫⁻ x in Set.pi univ (fun i => Ioc (a i) (b i)), g x =
      ∫⁻ s in Ioc (a 0) (b 0), ∫⁻ t in Ioc (a 1) (b 1), g ![s, t] := by
  have hset : Set.pi univ (fun i => Ioc (a i) (b i)) =
      MeasurableEquiv.finTwoArrow ⁻¹' (Ioc (a 0) (b 0) ×ˢ Ioc (a 1) (b 1)) := by
    ext x
    simp [Fin.forall_fin_two, MeasurableEquiv.finTwoArrow, and_assoc]
  have hpres := volume_preserving_finTwoArrow ℝ
  have h1 := hpres.setLIntegral_comp_preimage_emb MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : ℝ × ℝ => g ![p.1, p.2]) (Ioc (a 0) (b 0) ×ˢ Ioc (a 1) (b 1))
  have h2 : ∀ x : Vec 2, g ![(MeasurableEquiv.finTwoArrow x).1, (MeasurableEquiv.finTwoArrow x).2]
      = g x := by
    intro x
    congr 1
    ext i; fin_cases i <;> simp [MeasurableEquiv.finTwoArrow]
  rw [hset]
  simp only [h2] at h1
  rw [h1, Measure.volume_eq_prod, setLIntegral_prod]
  exact (hg.comp (by fun_prop : Measurable fun p : ℝ × ℝ => (![p.1, p.2] : Vec 2))).aemeasurable

theorem add_sq_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  induction a using ENNReal.recTopCoe with
  | top => simp
  | coe a =>
    induction b using ENNReal.recTopCoe with
    | top => simp
    | coe b =>
      have : ((a + b : ℝ≥0) ^ 2 : ℝ≥0) ≤ 2 * (a ^ 2 + b ^ 2) := by
        rw [← NNReal.coe_le_coe]; push_cast; nlinarith [sq_nonneg ((a:ℝ) - b)]
      exact_mod_cast this

theorem add_four_sq_le (a b c d : ℝ≥0∞) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  calc (a + b + c + d) ^ 2 = ((a + b) + (c + d)) ^ 2 := by ring_nf
    _ ≤ 2 * ((a + b) ^ 2 + (c + d) ^ 2) := add_sq_le_two_mul _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * (c ^ 2 + d ^ 2)) := by
        gcongr <;> exact add_sq_le_two_mul _ _
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by ring

theorem lintegral_sq_le_measure_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h : α → ℝ≥0∞) (hh : AEMeasurable h μ) :
    (∫⁻ x, h x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, h x ^ 2 ∂μ := by
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hh
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, one_pow, one_mul, ENNReal.rpow_two] at this
  have h2 : (∫⁻ x, h x ∂μ) ^ 2 ≤
      ((∫⁻ x, h x ^ 2 ∂μ) ^ (1 / (2:ℝ)) * μ univ ^ (1 / (2:ℝ))) ^ 2 := by
    gcongr
  refine h2.trans ?_
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (μ univ ^ _), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  simp [mul_comm]

theorem lintegral_pi_Ioc_eq_Icc (f : Vec 2 → ℝ≥0∞) (a b : Vec 2) :
    ∫⁻ x in Set.pi univ (fun i => Ioc (a i) (b i)), f x =
      ∫⁻ x in Set.pi univ (fun i => Icc (a i) (b i)), f x := by
  have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ)) (f := a)
    (g := b)
  rw [volume_pi]
  rw [Set.pi_univ_Icc]
  exact setLIntegral_congr h

theorem lintegral_pi_Ico_eq_Icc (f : Vec 2 → ℝ≥0∞) (a b : Vec 2) :
    ∫⁻ x in Set.pi univ (fun i => Ico (a i) (b i)), f x =
      ∫⁻ x in Set.pi univ (fun i => Icc (a i) (b i)), f x := by
  have h := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ)) (f := a)
    (g := b)
  rw [volume_pi]
  rw [Set.pi_univ_Icc]
  exact setLIntegral_congr h

theorem volume_pi_Icc_square (a : Vec 2) (L : ℝ) :
    volume (Set.pi univ (fun i => Icc (a i) (a i + L))) = ENNReal.ofReal L ^ 2 := by
  rw [Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp [sq]

omit [NormedSpace ℝ E] in
theorem measurable_lintegral_inner (G : Vec 2 → E) (hG : Continuous G) (S : Set ℝ) :
    Measurable fun r : ℝ => ∫⁻ ρ in S, ‖G ![r, ρ]‖ₑ := by
  have h : Measurable (fun p : ℝ × ℝ => ‖G ![p.1, p.2]‖ₑ) :=
    (hG.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Vec 2))).enorm.measurable
  exact h.lintegral_prod_right' (ν := volume.restrict S)

theorem update_update_two (X : Vec 2) (r ρ : ℝ) :
    Function.update (Function.update X 0 r) 1 ρ = ![r, ρ] := by
  ext i; fin_cases i <;> simp

theorem orderedDerivative_one (i : Fin 2) (u : Vec 2 → E) :
    orderedDerivative (![i] : DerivativeWord2 1) u = fun x => fderiv ℝ u x (basisVec i) := by
  simp [orderedDerivative]

theorem orderedDerivative_two (i j : Fin 2) (u : Vec 2 → E) :
    orderedDerivative (![i, j] : DerivativeWord2 2) u =
      fun x => fderiv ℝ (orderedDerivative (![i] : DerivativeWord2 1) u) x (basisVec j) := by
  simp [orderedDerivative]

/-- The four-term (non-squared) sampling bound on a square. -/
theorem enorm_le_square (u : Vec 2 → E) (hu : ContDiff ℝ ((2 : ℕ) : ℕ∞) u) {a : Vec 2} {L : ℝ}
    (hL : 0 < L) {X : Vec 2} (hX : X ∈ Set.pi univ fun i => Icc (a i) (a i + L)) :
    ‖u X‖ₑ ≤ ENNReal.ofReal L⁻¹ ^ 2 * (∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)), ‖u x‖ₑ)
      + ENNReal.ofReal L⁻¹ * (∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)),
          ‖orderedDerivative (![1] : DerivativeWord2 1) u x‖ₑ)
      + ENNReal.ofReal L⁻¹ * (∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)),
          ‖orderedDerivative (![0] : DerivativeWord2 1) u x‖ₑ)
      + ∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)),
          ‖orderedDerivative (![0, 1] : DerivativeWord2 2) u x‖ₑ := by
  have hu1 : ContDiff ℝ ((1 + 1 : ℕ) : ℕ∞) u := hu
  have hc0 : Continuous u := hu.continuous
  have hd0 : ContDiff ℝ ((1 : ℕ) : ℕ∞) (orderedDerivative (![0] : DerivativeWord2 1) u) :=
    contDiff_orderedDerivative 1 _ u hu1
  have hd1 : ContDiff ℝ ((1 : ℕ) : ℕ∞) (orderedDerivative (![1] : DerivativeWord2 1) u) :=
    contDiff_orderedDerivative 1 _ u hu1
  have hd01 : ContDiff ℝ ((0 : ℕ) : ℕ∞) (orderedDerivative (![0, 1] : DerivativeWord2 2) u) :=
    contDiff_orderedDerivative 0 _ u hu
  set ℓ := ENNReal.ofReal L⁻¹ with hℓ
  generalize hd0def : orderedDerivative (![0] : DerivativeWord2 1) u = d0 at *
  generalize hd1def : orderedDerivative (![1] : DerivativeWord2 1) u = d1 at *
  generalize hd01def : orderedDerivative (![0, 1] : DerivativeWord2 2) u = d01 at *
  have e0 : ∀ x, fderiv ℝ u x (basisVec 0) = d0 x := fun x => by
    rw [← hd0def, orderedDerivative_one]
  have e1 : ∀ x, fderiv ℝ u x (basisVec 1) = d1 x := fun x => by
    rw [← hd1def, orderedDerivative_one]
  have e01 : ∀ x, fderiv ℝ d0 x (basisVec 1) = d01 x := fun x => by
    rw [← hd0def, ← hd01def, orderedDerivative_two, orderedDerivative_one]
  have hX0 : X 0 ∈ Icc (a 0) (a 0 + L) := hX 0 (mem_univ _)
  have hX1 : X 1 ∈ Icc (a 1) (a 1 + L) := hX 1 (mem_univ _)
  -- the first line, in direction `0`
  have h0 := enorm_le_sampling_line u (by simpa using hu.of_le (by norm_num)) 0 X hL hX0
  simp only [e0] at h0
  -- second lines, in direction `1`
  have h1 : ∀ r : ℝ, ‖u (Function.update X 0 r)‖ₑ ≤
      ℓ * (∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖u ![r, ρ]‖ₑ)
        + ∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖d1 ![r, ρ]‖ₑ := by
    intro r
    have := enorm_le_sampling_line u (by simpa using hu.of_le (by norm_num)) 1
      (Function.update X 0 r) hL (by simpa using hX1)
    simpa only [update_update_two, e1] using this
  have h2 : ∀ τ : ℝ, ‖d0 (Function.update X 0 τ)‖ₑ ≤
      ℓ * (∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖d0 ![τ, ρ]‖ₑ)
        + ∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖d01 ![τ, ρ]‖ₑ := by
    intro τ
    have := enorm_le_sampling_line d0 (by simpa using hd0) 1
      (Function.update X 0 τ) hL (by simpa using hX1)
    simpa only [update_update_two, e01] using this
  have hm1 := measurable_lintegral_inner d1 hd1.continuous (Ioc (a 1) (a 1 + L))
  have hm01 := measurable_lintegral_inner d01 hd01.continuous (Ioc (a 1) (a 1 + L))
  have hmu := measurable_lintegral_inner u hc0 (Ioc (a 1) (a 1 + L))
  have hmd0 := measurable_lintegral_inner d0 hd0.continuous (Ioc (a 1) (a 1 + L))
  have hbr : ∀ (G : Vec 2 → E), Continuous G →
      ∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)), ‖G x‖ₑ =
        ∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖G ![s, t]‖ₑ := by
    intro G hG
    rw [← lintegral_pi_Ioc_eq_Icc (fun x => ‖G x‖ₑ) a (fun i => a i + L)]
    exact lintegral_pi_Ioc_two (fun x => ‖G x‖ₑ) hG.enorm.measurable a (fun i => a i + L)
  rw [hbr u hc0, hbr d1 hd1.continuous, hbr d0 hd0.continuous, hbr d01 hd01.continuous]
  have hA : ∫⁻ r in Ioc (a 0) (a 0 + L), ‖u (Function.update X 0 r)‖ₑ ≤
      ℓ * (∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖u ![s, t]‖ₑ)
        + ∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖d1 ![s, t]‖ₑ := by
    calc _ ≤ ∫⁻ r in Ioc (a 0) (a 0 + L), (ℓ * (∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖u ![r, ρ]‖ₑ)
        + ∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖d1 ![r, ρ]‖ₑ) := lintegral_mono fun r => h1 r
      _ = _ := by
        rw [lintegral_add_right _ hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hB : ∫⁻ r in Ioc (a 0) (a 0 + L), ‖d0 (Function.update X 0 r)‖ₑ ≤
      ℓ * (∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖d0 ![s, t]‖ₑ)
        + ∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖d01 ![s, t]‖ₑ := by
    calc _ ≤ ∫⁻ r in Ioc (a 0) (a 0 + L), (ℓ * (∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖d0 ![r, ρ]‖ₑ)
        + ∫⁻ ρ in Ioc (a 1) (a 1 + L), ‖d01 ![r, ρ]‖ₑ) := lintegral_mono fun r => h2 r
      _ = _ := by
        rw [lintegral_add_right _ hm01, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ‖u X‖ₑ ≤ _ := h0
    _ ≤ ℓ * (ℓ * (∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖u ![s, t]‖ₑ)
        + ∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖d1 ![s, t]‖ₑ)
        + (ℓ * (∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖d0 ![s, t]‖ₑ)
        + ∫⁻ s in Ioc (a 0) (a 0 + L), ∫⁻ t in Ioc (a 1) (a 1 + L), ‖d01 ![s, t]‖ₑ) := by
        gcongr
    _ = _ := by ring

theorem sq_arith (lam : ℝ≥0∞) (h0 : lam ≠ 0) (ht : lam ≠ ⊤)
    (x I0 I1 I2 I3 J0 J1 J2 J3 : ℝ≥0∞)
    (hx : x ≤ lam⁻¹ ^ 2 * I0 + lam⁻¹ * I1 + lam⁻¹ * I2 + I3)
    (h0' : I0 ^ 2 ≤ lam ^ 2 * J0) (h1 : I1 ^ 2 ≤ lam ^ 2 * J1) (h2 : I2 ^ 2 ≤ lam ^ 2 * J2)
    (h3 : I3 ^ 2 ≤ lam ^ 2 * J3) :
    x ^ 2 ≤ 4 * lam⁻¹ ^ 2 * (J0 + lam ^ 2 * J1 + lam ^ 2 * J2 + lam ^ 4 * J3) := by
  have key : lam⁻¹ * lam = 1 := ENNReal.inv_mul_cancel h0 ht
  calc x ^ 2 ≤ (lam⁻¹ ^ 2 * I0 + lam⁻¹ * I1 + lam⁻¹ * I2 + I3) ^ 2 := by gcongr
    _ ≤ 4 * ((lam⁻¹ ^ 2 * I0) ^ 2 + (lam⁻¹ * I1) ^ 2 + (lam⁻¹ * I2) ^ 2 + I3 ^ 2) :=
        add_four_sq_le _ _ _ _
    _ ≤ 4 * ((lam⁻¹ ^ 2 * (lam⁻¹ * lam) ^ 2 * J0) + ((lam⁻¹ * lam) ^ 2 * J1)
          + ((lam⁻¹ * lam) ^ 2 * J2) + lam ^ 2 * J3) := by
        gcongr
        · calc (lam⁻¹ ^ 2 * I0) ^ 2 = lam⁻¹ ^ 4 * I0 ^ 2 := by ring
            _ ≤ lam⁻¹ ^ 4 * (lam ^ 2 * J0) := by gcongr
            _ = _ := by ring
        · calc (lam⁻¹ * I1) ^ 2 = lam⁻¹ ^ 2 * I1 ^ 2 := by ring
            _ ≤ lam⁻¹ ^ 2 * (lam ^ 2 * J1) := by gcongr
            _ = _ := by ring
        · calc (lam⁻¹ * I2) ^ 2 = lam⁻¹ ^ 2 * I2 ^ 2 := by ring
            _ ≤ lam⁻¹ ^ 2 * (lam ^ 2 * J2) := by gcongr
            _ = _ := by ring
    _ = 4 * lam⁻¹ ^ 2 * (J0 + lam ^ 2 * J1 + lam ^ 2 * J2 + lam ^ 4 * J3) := by
        have : lam⁻¹ ^ 2 * lam ^ 4 = lam ^ 2 := by
          calc lam⁻¹ ^ 2 * lam ^ 4 = (lam⁻¹ * lam) ^ 2 * lam ^ 2 := by ring
            _ = _ := by rw [key]; simp
        have h' : 4 * lam⁻¹ ^ 2 * (J0 + lam ^ 2 * J1 + lam ^ 2 * J2 + lam ^ 4 * J3) =
            4 * (lam⁻¹ ^ 2 * J0 + (lam⁻¹ * lam) ^ 2 * J1 + (lam⁻¹ * lam) ^ 2 * J2
              + (lam⁻¹ ^ 2 * lam ^ 4) * J3) := by ring
        rw [h', this, key]; simp

/-- Squared sampling bound on a square, summed over all derivative words of length at most `2`. -/
theorem enorm_sq_le_square (u : Vec 2 → E) (hu : ContDiff ℝ ((2 : ℕ) : ℕ∞) u) {a : Vec 2}
    {L : ℝ} (hL : 0 < L) {X : Vec 2} (hX : X ∈ Set.pi univ fun i => Icc (a i) (a i + L)) :
    ‖u X‖ₑ ^ 2 ≤ ENNReal.ofReal (4 * (L⁻¹) ^ 2) * ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
      ENNReal.ofReal (L ^ (2 * m)) *
        ∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)), ‖orderedDerivative β u x‖ₑ ^ 2 := by
  have hu1 : ContDiff ℝ ((1 + 1 : ℕ) : ℕ∞) u := hu
  have hd0 : ContDiff ℝ ((1 : ℕ) : ℕ∞) (orderedDerivative (![0] : DerivativeWord2 1) u) :=
    contDiff_orderedDerivative 1 _ u hu1
  have hd1 : ContDiff ℝ ((1 : ℕ) : ℕ∞) (orderedDerivative (![1] : DerivativeWord2 1) u) :=
    contDiff_orderedDerivative 1 _ u hu1
  have hd01 : ContDiff ℝ ((0 : ℕ) : ℕ∞) (orderedDerivative (![0, 1] : DerivativeWord2 2) u) :=
    contDiff_orderedDerivative 0 _ u hu
  have h4 := enorm_le_square u hu hL hX
  have cs : ∀ G : Vec 2 → E, Continuous G →
      (∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)), ‖G x‖ₑ) ^ 2 ≤
        ENNReal.ofReal L ^ 2 * ∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)),
          ‖G x‖ₑ ^ 2 := by
    intro G hG
    have := lintegral_sq_le_measure_mul
      (volume.restrict (Set.pi univ (fun i => Icc (a i) (a i + L))))
      (fun x => ‖G x‖ₑ) hG.enorm.measurable.aemeasurable
    rwa [Measure.restrict_apply_univ, volume_pi_Icc_square] at this
  have hlam : ENNReal.ofReal L ≠ 0 := by simpa using hL
  have hℓ : ENNReal.ofReal L⁻¹ = (ENNReal.ofReal L)⁻¹ := ENNReal.ofReal_inv_of_pos hL
  rw [hℓ] at h4
  have hmain := sq_arith (ENNReal.ofReal L) hlam ENNReal.ofReal_ne_top _ _ _ _ _ _ _ _ _ h4
    (cs u hu.continuous) (cs _ hd1.continuous) (cs _ hd0.continuous) (cs _ hd01.continuous)
  refine hmain.trans ?_
  have hc : ENNReal.ofReal (4 * (L⁻¹) ^ 2) = 4 * (ENNReal.ofReal L)⁻¹ ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (inv_nonneg.2 hL.le), hℓ]
    simp
  rw [hc]
  gcongr
  have hw1 : ENNReal.ofReal (L ^ (2 * 1)) = ENNReal.ofReal L ^ 2 := by
    rw [ENNReal.ofReal_pow hL.le]
  have hw2 : ENNReal.ofReal (L ^ (2 * 2)) = ENNReal.ofReal L ^ 4 := by
    rw [ENNReal.ofReal_pow hL.le]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e0 : ∀ β : DerivativeWord2 0, orderedDerivative β u = u := fun β => orderedDerivative_zero β u
  simp only [e0, Finset.univ_unique, Finset.sum_singleton, mul_zero, pow_zero,
    ENNReal.ofReal_one, one_mul]
  have s1 := Finset.sum_le_sum_of_subset
    (f := fun β : DerivativeWord2 1 => ENNReal.ofReal (L ^ (2 * 1)) *
      ∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)), ‖orderedDerivative β u x‖ₑ ^ 2)
    (Finset.subset_univ {(![1] : DerivativeWord2 1), (![0] : DerivativeWord2 1)})
  rw [Finset.sum_pair (by decide), hw1] at s1
  have s2 := Finset.single_le_sum
    (f := fun β : DerivativeWord2 2 => ENNReal.ofReal (L ^ (2 * 2)) *
      ∫⁻ x in Set.pi univ (fun i => Icc (a i) (a i + L)), ‖orderedDerivative β u x‖ₑ ^ 2)
    (fun _ _ => zero_le) (Finset.mem_univ (![0, 1] : DerivativeWord2 2))
  simp only [hw1, hw2] at s1 s2 ⊢
  exact (le_of_eq (by ring)).trans (add_le_add (add_le_add le_rfl s1) s2)

end Sampling

end AVRegularity
end

section
open Homogenization MeasureTheory Set
open scoped ENNReal
namespace AVRegularity

/-! Dilation of the Lebesgue integral on `Vec 2`, and tilings of boxes `[0, cM)²` by half-open
lattice cells of side `c`. -/

namespace Sampling

/-- Change of variables for the dilation `w ↦ c • w` of `Vec 2`. -/
theorem setLIntegral_eq_comp_smul (f : Vec 2 → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (S : Set (Vec 2)) :
    ∫⁻ x in S, f x = ENNReal.ofReal (c ^ 2) * ∫⁻ w in (fun v : Vec 2 => c • v) ⁻¹' S, f (c • w) := by
  let φ := (Homeomorph.smul (isUnit_iff_ne_zero.2 hc.ne').unit : Vec 2 ≃ₜ Vec 2).toMeasurableEquiv
  have hφ : (φ : Vec 2 → Vec 2) = fun v => c • v := rfl
  have hmap : Measure.map (fun v : Vec 2 => c • v) (volume : Measure (Vec 2)) =
      ENNReal.ofReal (c ^ 2)⁻¹ • volume := by
    rw [Measure.map_addHaar_smul volume hc.ne']
    simp [abs_of_pos (pow_pos hc 2)]
  have h1 : ∫⁻ w in (fun v : Vec 2 => c • v) ⁻¹' S, f (c • w) =
      ∫⁻ x in S, f x ∂(Measure.map (fun v : Vec 2 => c • v) volume) := by
    rw [← hφ, φ.measurableEmbedding.restrict_map, φ.measurableEmbedding.lintegral_map]
    rfl
  rw [h1, hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg hc.le 2), mul_inv_cancel₀ (pow_pos hc 2).ne']
  simp

/-- The half-open lattice cell of side `c` with index `n`. -/
def cell (c : ℝ) (n : Fin 2 → ℕ) : Set (Vec 2) :=
  Set.pi univ fun i => Ico (c * n i) (c * (n i + 1))

theorem measurableSet_cell (c : ℝ) (n : Fin 2 → ℕ) : MeasurableSet (cell c n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem pairwiseDisjoint_cell {c : ℝ} (hc : 0 < c) :
    Set.PairwiseDisjoint (univ : Set (Fin 2 → ℕ)) (cell c) := by
  intro n _ n' _ hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  have h1 := hx i (mem_univ _)
  have h2 := hx' i (mem_univ _)
  simp only [mem_Ico] at h1 h2
  rcases lt_or_gt_of_ne hi with h | h
  · have : (n i : ℝ) + 1 ≤ n' i := by exact_mod_cast h
    nlinarith [h1.2, h2.1]
  · have : (n' i : ℝ) + 1 ≤ n i := by exact_mod_cast h
    nlinarith [h1.1, h2.2]

theorem iUnion_cell {c : ℝ} (hc : 0 < c) (M : ℕ) :
    (⋃ n ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range M), cell c n) =
      Set.pi univ fun _ => Ico 0 (c * M) := by
  ext x
  simp only [mem_iUnion, Fintype.mem_piFinset, Finset.mem_range, cell, mem_pi, mem_univ,
    forall_const, mem_Ico, exists_prop]
  constructor
  · rintro ⟨n, hn, hx⟩ i
    refine ⟨(mul_nonneg hc.le (Nat.cast_nonneg _)).trans (hx i).1, (hx i).2.trans_le ?_⟩
    have : (n i : ℝ) + 1 ≤ M := by exact_mod_cast hn i
    exact mul_le_mul_of_nonneg_left this hc.le
  · intro hx
    refine ⟨fun i => ⌊x i / c⌋₊, fun i => ?_, fun i => ?_⟩
    · have h0 : 0 ≤ x i / c := div_nonneg (hx i).1 hc.le
      have h1 : x i / c < M := by rw [div_lt_iff₀ hc]; linarith [(hx i).2]
      exact (Nat.floor_lt h0).2 h1
    · have h0 : 0 ≤ x i / c := div_nonneg (hx i).1 hc.le
      constructor
      · have := Nat.floor_le h0
        rw [le_div_iff₀ hc] at this; linarith
      · have := Nat.lt_floor_add_one (x i / c)
        rw [div_lt_iff₀ hc] at this; linarith

theorem lintegral_pi_Ico_eq_sum_cells (f : Vec 2 → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (M : ℕ) :
    ∫⁻ x in Set.pi univ (fun _ => Ico 0 (c * M)), f x =
      ∑ n ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range M), ∫⁻ x in cell c n, f x := by
  rw [← iUnion_cell hc M]
  exact lintegral_biUnion_finset ((pairwiseDisjoint_cell hc).subset (subset_univ _))
    (fun n _ => measurableSet_cell c n) f

theorem sum_cells_le_of_subset (f : Vec 2 → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (M : ℕ) (S : Set (Vec 2))
    (hS : Set.pi univ (fun _ => Ico 0 (c * M)) ⊆ S) :
    ∑ n ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range M), ∫⁻ x in cell c n, f x ≤
      ∫⁻ x in S, f x := by
  rw [← lintegral_pi_Ico_eq_sum_cells f hc M]
  exact lintegral_mono_set hS

theorem lintegral_unitCube_eq_Ico (f : Vec 2 → ℝ≥0∞) :
    ∫⁻ x in AVenhance.unitCube, f x = ∫⁻ x in Set.pi univ (fun _ : Fin 2 => Ico (0 : ℝ) 1), f x := by
  have h1 := Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (f := (0 : Vec 2)) (g := (1 : Vec 2))
  have h2 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (f := (0 : Vec 2)) (g := (1 : Vec 2))
  rw [← volume_pi] at h1 h2
  exact setLIntegral_congr (h1.trans h2.symm)

/-- Slow scaling: the slow cell integral (no regularity needed). -/
theorem lintegral_slowCell_comp_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec 2 → E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ X in slowCell ρ, ‖g (ρ • X)‖ₑ ^ 2 =
      ENNReal.ofReal (ρ⁻¹ ^ 2) * ∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ 2 := by
  have hpre : (fun v : Vec 2 => ρ • v) ⁻¹' (Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) 1) =
      slowCell ρ := by
    ext X
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_Icc, slowCell,
      Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    rw [mul_comm, ← le_div_iff₀ hρ, one_div, mul_nonneg_iff_of_pos_right hρ]
  have h1 := setLIntegral_eq_comp_smul (fun x => ‖g x‖ₑ ^ 2) hρ
    (Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) 1)
  rw [hpre] at h1
  have h2 : ∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ 2 =
      ∫⁻ x in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) 1), ‖g x‖ₑ ^ 2 := by
    rw [lintegral_unitCube_eq_Ico]
    exact lintegral_pi_Ico_eq_Icc (fun x => ‖g x‖ₑ ^ 2) 0 1
  rw [h2, h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
    inv_mul_cancel₀ hρ.ne']
  simp

end Sampling

alias lintegral_slowCell_comp_smul' := Sampling.lintegral_slowCell_comp_smul'

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory Set
open scoped ENNReal
namespace AVRegularity

/-! The two-scale sampling inequality for the diagonal `x ↦ z(x/ρ, x/e)` on the unit torus. -/

namespace Sampling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lattice vector of a cell index. -/
def cellVec (n : Fin 2 → ℕ) : Vec 2 := fun i => (n i : ℝ)

theorem cell_eq_pi_Ico (ϑ : ℝ) (n : Fin 2 → ℕ) :
    cell ϑ n = Set.pi univ fun i => Ico ((ϑ • cellVec n) i) ((ϑ • cellVec n) i + ϑ) := by
  unfold cell
  congr 1
  funext i
  simp only [Pi.smul_apply, cellVec, smul_eq_mul]
  congr 1
  ring

theorem slow_joint_continuous (z : Vec 2 → Vec 2 → E) (hz : IsSlowSmooth 2 z) {m : ℕ} (hm : m < 3)
    (β : DerivativeWord2 m) :
    Continuous (fun p : Vec 2 × Vec 2 => orderedDerivative β (fun X => z X p.2) p.1) := by
  have hm' : m ≤ 2 := by omega
  exact continuous_orderedDerivative_uncurry β z
    (fun y => (hz.1 y).of_le (by exact_mod_cast hm')) (hz.2 m hm')

/-- The sampling bound on one cell, after the change of variables to the unit cell. -/
theorem cell_bound (z : Vec 2 → Vec 2 → E) (hz : IsSlowSmooth 2 z) {ϑ : ℝ} (hϑ : 0 < ϑ) (n : Fin 2 → ℕ) :
    ∫⁻ y in Set.pi univ (fun _ : Fin 2 => Ico (0 : ℝ) 1),
        ‖z (ϑ • (cellVec n + y)) y‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * (ϑ⁻¹) ^ 2) * ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
        ENNReal.ofReal (ϑ ^ (2 * m)) * ∫⁻ X in cell ϑ n,
          ∫⁻ y in AVenhance.unitCube, ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
  set B : Set (Vec 2) := Set.pi univ (fun _ : Fin 2 => Ico (0 : ℝ) 1) with hB
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hcellIcc : ∀ f : Vec 2 → ℝ≥0∞, ∫⁻ x in Set.pi univ (fun i =>
      Icc ((ϑ • cellVec n) i) ((ϑ • cellVec n) i + ϑ)), f x = ∫⁻ x in cell ϑ n, f x := by
    intro f
    rw [cell_eq_pi_Ico, lintegral_pi_Ico_eq_Icc f (ϑ • cellVec n) (fun i => (ϑ • cellVec n) i + ϑ)]
  have hpt : ∀ y ∈ B, ‖z (ϑ • (cellVec n + y)) y‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * (ϑ⁻¹) ^ 2) * ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
        ENNReal.ofReal (ϑ ^ (2 * m)) * ∫⁻ X in cell ϑ n,
          ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
    intro y hy
    have hmem : ϑ • (cellVec n + y) ∈ Set.pi univ fun i =>
        Icc ((ϑ • cellVec n) i) ((ϑ • cellVec n) i + ϑ) := by
      intro i _
      have hy' := hy i (mem_univ _)
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mem_Icc, cellVec]
      constructor <;> nlinarith [hy'.1, hy'.2]
    have h := enorm_sq_le_square (fun X => z X y) (hz.1 y) hϑ hmem
    simp only [hcellIcc] at h
    exact h
  -- joint measurability of the slow jets
  have hmeas : ∀ m, m < 3 → ∀ β : DerivativeWord2 m,
      Measurable (fun p : Vec 2 × Vec 2 => ‖orderedDerivative β (fun X => z X p.2) p.1‖ₑ ^ 2) :=
    fun m hm β => ((slow_joint_continuous z hz hm β).enorm.measurable).pow_const 2
  have hinner : ∀ m, m < 3 → ∀ β : DerivativeWord2 m,
      Measurable (fun y : Vec 2 => ∫⁻ X in cell ϑ n,
        ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2) := fun m hm β =>
    (hmeas m hm β).lintegral_prod_left' (μ := volume.restrict (cell ϑ n))
  have hswap : ∀ m, m < 3 → ∀ β : DerivativeWord2 m,
      ∫⁻ y in B, ∫⁻ X in cell ϑ n, ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 =
      ∫⁻ X in cell ϑ n, ∫⁻ y in AVenhance.unitCube,
        ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
    intro m hm β
    simp only [lintegral_unitCube_eq_Ico]
    exact lintegral_lintegral_swap
      ((hmeas m hm β).comp measurable_swap).aemeasurable
  calc ∫⁻ y in B, ‖z (ϑ • (cellVec n + y)) y‖ₑ ^ 2
      ≤ ∫⁻ y in B, ENNReal.ofReal (4 * (ϑ⁻¹) ^ 2) * ∑ m ∈ Finset.range 3,
          ∑ β : DerivativeWord2 m, ENNReal.ofReal (ϑ ^ (2 * m)) * ∫⁻ X in cell ϑ n,
            ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := setLIntegral_mono' hBm hpt
    _ = ENNReal.ofReal (4 * (ϑ⁻¹) ^ 2) * ∑ m ∈ Finset.range 3,
          ∑ β : DerivativeWord2 m, ENNReal.ofReal (ϑ ^ (2 * m)) *
            ∫⁻ y in B, ∫⁻ X in cell ϑ n, ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_finsetSum' _ (fun m hm => ?_)]
        · refine Finset.sum_congr rfl fun m hm => ?_
          have hm' := Finset.mem_range.1 hm
          rw [lintegral_finsetSum' _ (fun β _ => ?_)]
          · exact Finset.sum_congr rfl fun β _ =>
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          · exact ((hinner m hm' β).const_mul _).aemeasurable
        · have hm' := Finset.mem_range.1 hm
          exact (Finset.measurable_sum _ fun β _ =>
            (hinner m hm' β).const_mul _).aemeasurable
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun β _ => ?_
        rw [hswap m (Finset.mem_range.1 hm) β]

/-- Two-scale sampling: the diagonal `x ↦ z(x/ρ, x/e)` on the unit torus. -/
theorem diag_sampling_sq_le (z : Vec 2 → Vec 2 → E) (hz : IsSlowSmooth 2 z)
    (hper : ∀ X, AVenhance.IsZ2Periodic (z X)) {ρ e : ℝ} (hρ : 0 < ρ) (he : 0 < e)
    (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ‖z (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (4 * ρ ^ 2) * ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
          ENNReal.ofReal ((e / ρ) ^ (2 * m)) *
            ∫⁻ X in slowCell ρ, ∫⁻ y in AVenhance.unitCube,
              ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
  have hϑ : 0 < e / ρ := div_pos he hρ
  have heM : e * M = 1 := by rw [← hM]; field_simp
  set P := Fintype.piFinset (fun _ : Fin 2 => Finset.range M) with hP
  set B : Set (Vec 2) := Set.pi univ (fun _ : Fin 2 => Ico (0 : ℝ) 1) with hB
  have hF : ∀ w : Vec 2, ‖z (ρ⁻¹ • (e • w)) (e⁻¹ • (e • w))‖ₑ ^ 2 =
      ‖z ((e / ρ) • w) w‖ₑ ^ 2 := by
    intro w
    rw [smul_smul, smul_smul, inv_mul_cancel₀ he.ne', one_smul, div_eq_inv_mul, mul_comm]
  have hpreim : (fun v : Vec 2 => e • v) ⁻¹' (Set.pi univ fun _ : Fin 2 => Ico (0 : ℝ) 1) =
      Set.pi univ fun _ : Fin 2 => Ico (0 : ℝ) (1 * M) := by
    ext w
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_Ico, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    have h : e * w i < 1 ↔ w i < e⁻¹ := by rw [← one_div, lt_div_iff₀' he]
    rw [one_mul, ← hM, h, mul_nonneg_iff_of_pos_left he]
  have hcell : ∀ n : Fin 2 → ℕ, ∫⁻ w in cell 1 n, ‖z ((e / ρ) • w) w‖ₑ ^ 2 =
      ∫⁻ y in B, ‖z ((e / ρ) • (cellVec n + y)) y‖ₑ ^ 2 := by
    intro n
    have hpres := measurePreserving_add_left (volume : Measure (Vec 2)) (cellVec n)
    have h1 := hpres.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addLeft (cellVec n)).measurableEmbedding
      (fun w : Vec 2 => ‖z ((e / ρ) • w) w‖ₑ ^ 2) (cell 1 n)
    have hpre : (fun v : Vec 2 => cellVec n + v) ⁻¹' cell 1 n = B := by
      ext y
      simp only [cell, cellVec, mem_preimage, mem_pi, mem_univ, forall_const, mem_Ico,
        Pi.add_apply, hB, one_mul]
      refine forall_congr' fun i => ?_
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [← h1]
    rw [hpre]
    refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun y _ => ?_
    have := hper ((e / ρ) • (cellVec n + y)) (fun i => (n i : ℤ)) y
    have hls : AVenhance.latticeShift (fun i => (n i : ℤ)) = cellVec n := by
      funext i; simp [AVenhance.latticeShift, cellVec]
    rw [hls, add_comm y] at this
    rw [this]
  have hc : ENNReal.ofReal (e ^ 2) * ENNReal.ofReal (4 * ((e / ρ)⁻¹) ^ 2) =
      ENNReal.ofReal (4 * ρ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc ∫⁻ x in AVenhance.unitCube, ‖z (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2
      = ∫⁻ x in Set.pi univ (fun _ : Fin 2 => Ico (0 : ℝ) 1), ‖z (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 :=
        lintegral_unitCube_eq_Ico _
    _ = ENNReal.ofReal (e ^ 2) * ∫⁻ w in Set.pi univ (fun _ : Fin 2 => Ico (0 : ℝ) (1 * M)),
          ‖z ((e / ρ) • w) w‖ₑ ^ 2 := by
        rw [setLIntegral_eq_comp_smul _ he, hpreim]
        congr 1
        exact setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
          fun w _ => hF w
    _ = ENNReal.ofReal (e ^ 2) * ∑ n ∈ P, ∫⁻ y in B, ‖z ((e / ρ) • (cellVec n + y)) y‖ₑ ^ 2 := by
        rw [lintegral_pi_Ico_eq_sum_cells _ one_pos M]
        simp only [hcell]
        rfl
    _ ≤ ENNReal.ofReal (e ^ 2) * ∑ n ∈ P, ENNReal.ofReal (4 * ((e / ρ)⁻¹) ^ 2) *
          ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
            ENNReal.ofReal ((e / ρ) ^ (2 * m)) * ∫⁻ X in cell (e / ρ) n,
              ∫⁻ y in AVenhance.unitCube, ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
        gcongr with n hn
        exact cell_bound z hz hϑ n
    _ = ENNReal.ofReal (4 * ρ ^ 2) * ∑ n ∈ P, ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
            ENNReal.ofReal ((e / ρ) ^ (2 * m)) * ∫⁻ X in cell (e / ρ) n,
              ∫⁻ y in AVenhance.unitCube, ‖orderedDerivative β (fun X' => z X' y) X‖ₑ ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc, hc]
    _ ≤ _ := by
        gcongr
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun β _ => ?_
        rw [← Finset.mul_sum]
        gcongr
        refine sum_cells_le_of_subset _ hϑ M _ ?_
        intro x hx i hi
        have hx' := hx i (mem_univ _)
        simp only [mem_Ico] at hx'
        simp only [mem_Icc]
        refine ⟨hx'.1, hx'.2.le.trans (le_of_eq ?_)⟩
        rw [div_mul_eq_mul_div, heM, one_div]

end Sampling

alias diag_sampling_sq_le := Sampling.diag_sampling_sq_le

end AVRegularity
end
