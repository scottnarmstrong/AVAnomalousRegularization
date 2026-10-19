-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.LetterTransposeNorm
public import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.CycleJoint.Assembly.BlockEdgeSlowSample
public import AVRegularity.CycleJoint.PlaneWeakCurveCongruenceOn
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The seam's weighted jet norm controls the weighted factorial norms**.

For plane fields whose jets are a.e. a given jet family `J`, the mass-weighted sum of the weighted
factorial norms (moment `n`, scale `ϖ`, centre `0`, radius `r`, orders `≤ K`) is at most the square
of the seam's weighted jet norm of `J` (moment weight `⟨ϖ z⟩^n`, the same radius). The factorial
norm is the `ℓ²` sum over the orders of the squared scaled jets, the jet norm their `ℓ¹` sum. -/

/-- `Σ a_j² ≤ (Σ a_j)²` in `ℝ≥0∞`. -/
theorem ennreal_sum_sq_le_sq_sum {α : Type*} (s : Finset α) (a : α → ℝ≥0∞) :
    ∑ j ∈ s, a j ^ 2 ≤ (∑ j ∈ s, a j) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => a i * a j) (fun _ _ => zero_le) hi

/-- The weighted lower integral of the squared jets as the squared weighted `L²` norm. -/
theorem weighted_lintegral_eq_eLpNorm_sq {E : Type*} [NormedAddCommGroup E] (n : ℕ) (ϖ : ℝ)
    {a : ℕ} (G H : DerivativeWord2 a → Vec 2 → E)
    (hGH : ∀ w, G w =ᵐ[volume] H w) (hH : ∀ w, AEStronglyMeasurable (H w) volume) :
    ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 + (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n *
        ∑ w, ‖G w z‖ ^ 2) =
      eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) *
        Real.sqrt (∑ w, ‖H w z‖ ^ 2)) 2 volume ^ 2 := by
  have hmeas : AEStronglyMeasurable (fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) *
      Real.sqrt (∑ w, ‖H w z‖ ^ 2)) volume := by
    have hw : Continuous fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) :=
      Continuous.rpow_const (by fun_prop) fun z => Or.inl (by positivity)
    have hs : AEStronglyMeasurable (fun z => ∑ w, ‖H w z‖ ^ 2) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun w _ => ((hH w).norm.pow 2)
    exact hw.aestronglyMeasurable.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hs)
  rw [CycleWords.Seam.eLpNorm_two_sq_real _ hmeas]
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr hGH] with z hz
  congr 1
  have hS : 0 ≤ ∑ w, ‖H w z‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [Pi.zero_apply, sub_zero, hz]
  set Y := ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) with hY
  have hb : (0 : ℝ) ≤ 1 + Y := by rw [hY]; positivity
  have hw : ((1 + Y) ^ ((n : ℝ) / 2)) ^ (2 : ℕ) = (1 + Y) ^ n := by
    rw [← Real.rpow_natCast ((1 + Y) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul hb,
      ← Real.rpow_natCast (1 + Y) n]
    congr 1
    push_cast
    ring
  rw [mul_pow, Real.sq_sqrt hS, hw]

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The weighted jet norm controls the weighted factorial norms.** -/
theorem weightedFactorialNormSq_family_le_weightedJetNorm_sq (π : ι → ℝ) (n K : ℕ) (ϖ r : ℝ)
    (hr : 0 ≤ r) {K' : ι → ℕ} (U : ∀ v, PlaneHk Set.univ (K' v) (h v))
    (J : ∀ v (a : ℕ), DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ v a, a ≤ K → ∀ w, planeJetOrder (U v) a w =ᵐ[volume] J v a w)
    (hmeas : ∀ v a w, AEStronglyMeasurable (J v a w) volume) :
    ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 r K (U v) ≤
      weightedJetNorm π (n : ℝ) K ϖ r J ^ 2 := by
  set X : ℕ → ℝ≥0∞ := fun a => ∑ v, ENNReal.ofReal ((π v)⁻¹) *
    eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2 with hX
  have hL : ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 r K (U v) =
      ∑ a ∈ Finset.range (K + 1), ENNReal.ofReal (r ^ (2 * a) / (a.factorial : ℝ) ^ 2) * X a := by
    calc ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 r K (U v)
        = ∑ v, ∑ a ∈ Finset.range (K + 1), ENNReal.ofReal ((π v)⁻¹) *
            (ENNReal.ofReal (r ^ (2 * a) / (a.factorial : ℝ) ^ 2) *
              ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
                (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w, ‖planeJetOrder (U v) a w z‖ ^ 2)) :=
          Finset.sum_congr rfl fun v _ => by unfold weightedFactorialNormSq; rw [Finset.mul_sum]
      _ = ∑ a ∈ Finset.range (K + 1), ∑ v, ENNReal.ofReal ((π v)⁻¹) *
            (ENNReal.ofReal (r ^ (2 * a) / (a.factorial : ℝ) ^ 2) *
              ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
                (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w, ‖planeJetOrder (U v) a w z‖ ^ 2)) :=
          Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [hX, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [weighted_lintegral_eq_eLpNorm_sq n ϖ _ _
          (hJ v a (Nat.le_of_lt_succ (Finset.mem_range.1 ha))) (hmeas v a)]
        ring
  have hR : weightedJetNorm π (n : ℝ) K ϖ r J =
      ∑ a ∈ Finset.range (K + 1), ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        X a ^ (1 / 2 : ℝ) := rfl
  rw [hL, hR]
  refine le_trans ?_ (ennreal_sum_sq_le_sq_sum _ _)
  refine Finset.sum_le_sum fun a _ => ?_
  rw [mul_pow, ← ENNReal.rpow_natCast (X a ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul]
  norm_num
  rw [← ENNReal.ofReal_pow (div_nonneg (pow_nonneg hr a) (Nat.cast_nonneg _)), div_pow, ← pow_mul,
    mul_comm a 2]

section Realize

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] in
/-- A smooth field with finite weighted jet norm has square-integrable derivatives. -/
theorem memLp_orderedDerivative_of_weightedJetNorm_ne_top (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (p : ℝ) (hp : 0 ≤ p) (M : ℕ) (s r : ℝ) (hr : 0 < r) (g : ∀ x, Vec 2 → h x)
    (hg : ∀ x (k : ℕ), ContDiff ℝ k (g x))
    (hfin : weightedJetNorm π p M s r (fun x _ wd z => orderedDerivative wd (g x) z) ≠ ⊤)
    (x : ι) (a : JetIndex2 M) : MemLp (orderedDerivative a.2 (g x)) 2 volume := by
  have hcont : Continuous (orderedDerivative a.2 (g x)) :=
    CycleWords.Assembly.orderedDerivative_continuous a.2 (hg x a.1)
  rw [memLp_iff]
  set E := eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
    Real.sqrt (∑ w : DerivativeWord2 a.1.val, ‖orderedDerivative w (g x) z‖ ^ 2)) 2 volume with hE
  have hEfin : E ≠ ⊤ := by
    intro htop
    apply hfin
    have hc : ENNReal.ofReal (r ^ a.1.val / (a.1.val.factorial : ℝ)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hπx : ENNReal.ofReal ((π x)⁻¹) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.2 (hπ x)
    have hv : (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z =>
        (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a.1.val, ‖orderedDerivative w (g v) z‖ ^ 2)) 2 volume ^ 2)
        = ⊤ := by
      refine top_le_iff.1 (le_trans ?_ (Finset.single_le_sum (f := fun v =>
        ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a.1.val, ‖orderedDerivative w (g v) z‖ ^ 2)) 2 volume ^ 2)
        (fun _ _ => zero_le) (Finset.mem_univ x)))
      change ⊤ ≤ ENNReal.ofReal ((π x)⁻¹) * E ^ 2
      rw [htop, ENNReal.top_pow two_ne_zero, ENNReal.mul_top hπx]
    unfold weightedJetNorm
    refine top_le_iff.1 (le_trans ?_ (Finset.single_le_sum (f := fun a' =>
      ENNReal.ofReal (r ^ a' / (a'.factorial : ℝ)) * (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a', ‖orderedDerivative w (g v) z‖ ^ 2)) 2 volume ^ 2) ^
          (1 / 2 : ℝ)) (fun _ _ => zero_le) (Finset.mem_range.2 a.1.2)))
    rw [hv, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top hc]
  refine lt_of_le_of_lt (eLpNorm_mono_real hcont.aestronglyMeasurable fun z => ?_) hEfin.lt_top
  have hb : 1 ≤ 1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
    have := mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (z 0)) (sq_nonneg (z 1)))
    linarith
  have hw : 1 ≤ (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) :=
    Real.one_le_rpow hb (by linarith)
  have hs : ‖orderedDerivative a.2 (g x) z‖ ≤
      Real.sqrt (∑ w : DerivativeWord2 a.1.val, ‖orderedDerivative w (g x) z‖ ^ 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun w : DerivativeWord2 a.1.val =>
      ‖orderedDerivative w (g x) z‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a.2)
  calc ‖orderedDerivative a.2 (g x) z‖
      ≤ 1 * Real.sqrt (∑ w : DerivativeWord2 a.1.val, ‖orderedDerivative w (g x) z‖ ^ 2) := by
        rw [one_mul]; exact hs
    _ ≤ _ := mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg _)

omit [Fintype ι] in
/-- **The realization of a smooth linear cell model as plane fields of order `Mb`.** -/
def realizeCellModel {X : Type*} [AddCommGroup X] [Module ℝ X] (Mb : ℕ)
    (Mc : X →ₗ[ℝ] (∀ x, Vec 2 → h x)) (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume) :
    X →ₗ[ℝ] (∀ x, PlaneHk Set.univ Mb (h x)) where
  toFun ξ x := CycleWords.smoothPlaneHk Mb (Mc ξ x) (contDiff_infty.2 fun k => hsm ξ x k)
    (hmem ξ x)
  map_add' ξ ξ' := by
    funext x
    apply CycleWords.planeHk_eq_of_planeValue_ae
    have h1 := CycleWords.smoothPlaneHk_jet_ae Mb (Mc (ξ + ξ') x)
      (contDiff_infty.2 fun k => hsm (ξ + ξ') x k) (hmem (ξ + ξ') x) 0 (Nat.zero_le _)
      (fun i => i.elim0)
    have h2 := CycleWords.smoothPlaneHk_jet_ae Mb (Mc ξ x)
      (contDiff_infty.2 fun k => hsm ξ x k) (hmem ξ x) 0 (Nat.zero_le _) (fun i => i.elim0)
    have h3 := CycleWords.smoothPlaneHk_jet_ae Mb (Mc ξ' x)
      (contDiff_infty.2 fun k => hsm ξ' x k) (hmem ξ' x) 0 (Nat.zero_le _) (fun i => i.elim0)
    have h4 := planeJetOrder_add_all_ae 0 (fun i => i.elim0)
      (CycleWords.smoothPlaneHk Mb (Mc ξ x) (contDiff_infty.2 fun k => hsm ξ x k) (hmem ξ x))
      (CycleWords.smoothPlaneHk Mb (Mc ξ' x) (contDiff_infty.2 fun k => hsm ξ' x k) (hmem ξ' x))
    unfold planeValue
    filter_upwards [h1, h2, h3, h4] with z e1 e2 e3 e4
    simp only [Pi.add_apply] at e4 ⊢
    rw [e1, e4, e2, e3, map_add]
    simp [orderedDerivative]
  map_smul' c ξ := by
    funext x
    apply CycleWords.planeHk_eq_of_planeValue_ae
    have h1 := CycleWords.smoothPlaneHk_jet_ae Mb (Mc (c • ξ) x)
      (contDiff_infty.2 fun k => hsm (c • ξ) x k) (hmem (c • ξ) x) 0 (Nat.zero_le _)
      (fun i => i.elim0)
    have h2 := CycleWords.smoothPlaneHk_jet_ae Mb (Mc ξ x)
      (contDiff_infty.2 fun k => hsm ξ x k) (hmem ξ x) 0 (Nat.zero_le _) (fun i => i.elim0)
    have h4 := planeJetOrder_smul_ae 0 (fun i => i.elim0) c
      (CycleWords.smoothPlaneHk Mb (Mc ξ x) (contDiff_infty.2 fun k => hsm ξ x k) (hmem ξ x))
    unfold planeValue
    filter_upwards [h1, h2, h4] with z e1 e2 e4
    simp only [Pi.smul_apply, RingHom.id_apply] at e4 ⊢
    rw [e1, e4, e2, map_smul]
    simp [orderedDerivative]

omit [Fintype ι] in
theorem realizeCellModel_jet_ae {X : Type*} [AddCommGroup X] [Module ℝ X] (Mb : ℕ)
    (Mc : X →ₗ[ℝ] (∀ x, Vec 2 → h x)) (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (ξ : X) (x : ι) (j : ℕ) (hj : j ≤ Mb) (w : DerivativeWord2 j) :
    planeJetOrder (realizeCellModel Mb Mc hsm hmem ξ x) j w =ᵐ[volume]
      orderedDerivative w (Mc ξ x) :=
  CycleWords.smoothPlaneHk_jet_ae Mb (Mc ξ x) (contDiff_infty.2 fun k => hsm ξ x k) (hmem ξ x) j
    hj w

end Realize

end AVRegularity.CycleJointProofs.Assembly
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Molecular slow jets and the Piola derivative reserve are independent of the
auxiliary derivative order used for the transported Taylor remainder. -/

/-- Evaluating the zeroth fast derivative costs no operator norm. -/
theorem blockEdge_mixed_zero_fast_le (n : ℕ) (f : Vec 2 → Vec 2 → ℝ)
    (hf : ContDiff ℝ (n : ℕ) (Function.uncurry f)) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Y => f Y z) X‖ ≤
      ‖iteratedFDeriv ℝ n (fun Y => iteratedFDeriv ℝ 0 (f Y) z) X‖ := by
  let g := fun Y => f Y z
  let a := fun Y => iteratedFDeriv ℝ 0 (f Y) z
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Vec 2) ℝ Fin.elim0
  have hg : ContDiff ℝ (n : ℕ) g := hf.comp (contDiff_id.prodMk contDiff_const)
  have he : a = (continuousMultilinearCurryFin0 ℝ (Vec 2) ℝ).symm ∘ g := by
    funext Y
    change iteratedFDeriv ℝ 0 (f Y) z = (continuousMultilinearCurryFin0 ℝ (Vec 2) ℝ).symm (f Y z)
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  have ha : ContDiff ℝ (n : ℕ) a := by
    rw [he]
    exact (continuousMultilinearCurryFin0 ℝ (Vec 2) ℝ).symm.contDiff.comp hg
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simpa only [L, ContinuousMultilinearMap.apply_apply, Fin.prod_univ_zero, mul_one, one_mul] using
      A.le_opNorm Fin.elim0
  have hfun : L ∘ a = g := by
    funext Y
    change iteratedFDeriv ℝ 0 (f Y) z Fin.elim0 = f Y z
    exact iteratedFDeriv_zero_apply Fin.elim0
  have hh := L.norm_iteratedFDeriv_comp_left (x := X) ha.contDiffAt (by exact_mod_cast le_refl n)
  rw [hfun] at hh
  exact hh.trans (mul_le_of_le_one_left (norm_nonneg _) hL)

/-- The original molecular reserve gives pure slow jets with the physical ratio rho/E. -/
theorem blockEdge_family_slow_jet_budget {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p)
    (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c) (k : Fin 2)
    (a : ℕ) (ha : a ≤ K v) (X : Vec 2) :
    (ρ / E) ^ a * ‖iteratedFDeriv ℝ (j + a) (fun Y => F.flux p c v u γ d I t Y 0 k) X‖ ≤
      (Kmax.factorial : ℝ) ^ 2 * E ^ j *
        molecularRealPrice ν ρ (K v) (d - 2)
          (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
              derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
  have hfg : ContDiff ℝ (j + a : ℕ)
      (Function.uncurry (fun Y z => F.flux p c v u γ d I t Y z k)) := by
    have hh := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c t hdom v u γ d I
    have hh0 : ContDiff ℝ (j + a : ℕ) (Function.uncurry (F.flux p c v u γ d I t)) :=
      hh.of_le (by exact_mod_cast (show j + a ≤ K v + J by omega))
    exact (ContinuousLinearMap.proj k).contDiff.comp hh0
  have hn := blockEdge_mixed_zero_fast_le (j + a)
    (fun Y z => F.flux p c v u γ d I t Y z k) hfg X 0
  have hm := familyPointwiseMolecular_scalar_mixed_budget F π hπ K Kmax hK dom
    ν e E ρ hν he hE hρ C J b henv v u γ hγ d hd I j hj p c t hdom 0 k a 0 (by omega) X 0
  simp only [add_zero] at hm
  have hscale : (ρ / e) ^ a * |e / E| ^ a = (ρ / E) ^ a := by
    rw [abs_of_pos (div_pos he hE), ← mul_pow]
    congr 1
    field_simp
  rw [hscale] at hm
  exact (mul_le_mul_of_nonneg_left hn (pow_nonneg (div_pos hρ hE).le a)).trans hm

/-- Piola reserve cancellation with a derivative order n distinct from the
Sobolev slot K. This is needed at order Ks+1, even for a slot of order zero. -/
theorem blockEdge_transport_reserve_budget (N D Dmax r K n M : ℕ)
    (hD : D ≤ Dmax) (hr : 1 ≤ r) (hn : n ≤ M) (C ρ R : ℝ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 < R) (hρR : ρ ≤ R)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hB : ∀ d I, 0 ≤ B d I) :
    transportedPolynomialJetPrice N D r n C R
        (fun d I => B d I / derivativeReserveFactor ρ K (d - 2)) *
      derivativeReserveFactor ρ K (r - 1) ≤
    transportedPolynomialUniformReservePrice N Dmax M C *
      (∑ d ∈ Finset.Icc (r + 1) D, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, B d I) := by
  unfold transportedPolynomialJetPrice transportedPolynomialUniformReservePrice
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  have horder : r - 1 + (d - 1 - r) = d - 2 := by
    have hh := (Finset.mem_Icc.mp hd).1
    omega
  have hb := derivativeReserveFactor_order_lowering_budget ρ R hρ hR hρR K (r - 1)
    (d - 1 - r) (B d I) (hB d I)
  rw [horder] at hb
  let Q := 3 * (N + 1 : ℕ) * (2 : ℝ) ^ N * C
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let L := ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * Q ^ (d - 1)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hpow : Q ^ (d - 1) ≤ ∑ j ∈ Finset.range (Dmax + 1), Q ^ j :=
    Finset.single_le_sum (fun j _ => pow_nonneg hQ j)
      (Finset.mem_range.mpr (by have hh := (Finset.mem_Icc.mp hd).2; omega))
  calc
    _ = L * ((B d I / derivativeReserveFactor ρ K (d - 2)) * R⁻¹ ^ (d - 1 - r) *
        derivativeReserveFactor ρ K (r - 1)) := by dsimp only [L, Q]; ring
    _ ≤ L * B d I := mul_le_mul_of_nonneg_left hb hL
    _ ≤ (((M + 1 : ℕ) * (2 : ℝ) ^ M) ^ 2 * C *
        ∑ j ∈ Finset.range (Dmax + 1), Q ^ j) * B d I := by
      apply mul_le_mul_of_nonneg_right _ (hB d I)
      dsimp only [L]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (leibnizJetPrice_mono hn) hC)
        hpow (pow_nonneg hQ _) (by positivity)
    _ = _ := by
      dsimp only [Q]
      rw [Finset.mul_sum, Finset.sum_mul]

/-! Shared molecular inputs and slow jet prices for the block source remainder. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The original positive scales, mass weights, slots, and pointwise envelope.
All fields are premises of the fixed block edge statement. -/
structure BlockMolecularInputs (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (Cm : ℕ → ℝ) (J : ℕ) (B : ι → ι → ℝ) : Prop where
  mass_pos : ∀ v, 0 < π v
  slot_le : ∀ v, K v ≤ Kmax
  nu_pos : 0 < ν
  cell_pos : 0 < e
  slow_pos : 0 < E
  radius_pos : 0 < ρ
  molecular : IsPointwiseMolecularEnvelope F π K dom ν e E ρ Cm J B

/-- The actual original constituent price for one reserved slow derivative. -/
def blockSlowJetPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Kmax : ℕ)
    (dom : F.Domain) (ν e E ρ : ℝ) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (j : ℕ) : ℝ :=
  (Kmax.factorial : ℝ) ^ 2 * E ^ j *
    molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
          derivativeReserveFactor (ρ / e) (K v) (d - 2)

variable {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
  {dom : F.Domain} {ν e E ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

/-- Every original slow price is nonnegative. -/
theorem blockSlowJetPrice_nonneg (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (j : ℕ) :
    0 ≤ blockSlowJetPrice F K Kmax dom ν e E ρ v u γ d I j := by
  have hm := molecularRealPrice_nonneg ν ρ data.nu_pos.le data.radius_pos.le (K v) (d - 2)
    (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  unfold blockSlowJetPrice derivativeReserveFactor
  have he := data.cell_pos
  have hE := data.slow_pos
  have hρ := data.radius_pos
  positivity

/-- The pure slow field has all the qualitative regularity carried by the envelope. -/
theorem blockEdge_slow_contDiff (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (n : ℕ) (hn : n ≤ K v + J) (k : Fin 2) :
    ContDiff ℝ (n : ℕ) (fun X => F.flux p c v u γ d I t X 0 k) := by
  have hh := molecular_joint_contDiff F dom E data.slow_pos.ne' (fun v => K v + J)
    data.molecular.1 p c t hdom v u γ d I
  have hh0 : ContDiff ℝ (n : ℕ) (Function.uncurry (F.flux p c v u γ d I t)) :=
    hh.of_le (by exact_mod_cast hn)
  exact ((ContinuousLinearMap.proj k).contDiff.comp hh0).comp
    (contDiff_id.prodMk contDiff_const)

/-- The jet just below the Taylor cutoff is uniformly bounded in slow variables. -/
theorem blockEdge_slow_low_jets (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (j : ℕ) (hj : j ≤ J) (k : Fin 2) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun Y => F.flux p c v u γ d I t Y 0 k) X‖ ≤
      blockSlowJetPrice F K Kmax dom ν e E ρ v u γ d I j := by
  have hh := blockEdge_family_slow_jet_budget F π data.mass_pos K Kmax data.slot_le dom
    ν e E ρ data.nu_pos data.cell_pos data.slow_pos data.radius_pos Cm J B data.molecular
    v u γ hγ d hd I j hj p c t hdom k 0 (Nat.zero_le _) X
  simpa only [pow_zero, one_mul, Nat.add_zero, blockSlowJetPrice] using hh

/-- Enlarging the physical radius to rho/zeta costs only the excess derivative order. -/
theorem blockEdge_slow_high_reserve (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (L n : ℕ) (hL : L ≤ J) (hn : n ≤ K v) (η ζ : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hscale : ζ * η = ρ / E) (k : Fin 2) :
    ∀ j ≤ n, ∀ X,
      η ^ j * ‖iteratedFDeriv ℝ j (fun Y => F.flux p c v u γ d I t Y 0 k) X‖ ≤
        ζ⁻¹ ^ (n - L) * ∑ a ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E ρ v u γ d I a := by
  apply blockEdge_slow_reserve L n _ η ζ hη hη1 hζ hζ1
    (blockSlowJetPrice F K Kmax dom ν e E ρ v u γ d I)
    (fun a _ => blockSlowJetPrice_nonneg data v u γ d I a)
    (fun a ha X => blockEdge_slow_low_jets data p c v u γ hγ d hd I t hdom a (ha.trans hL) k X)
  intro a ha X
  have hh := blockEdge_family_slow_jet_budget F π data.mass_pos K Kmax data.slot_le dom
    ν e E ρ data.nu_pos data.cell_pos data.slow_pos data.radius_pos Cm J B data.molecular
    v u γ hγ d hd I L hL p c t hdom k a (by omega) X
  rw [hscale]
  exact hh
end

end AVRegularity.CycleJointProofs.Assembly
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs.Assembly

/-! The quantitative radius used to differentiate a transported coefficient is
independent of the radius used for its original Sobolev derivative reserve. -/

/-- Transported slow coefficients retain their original derivative reserve at
both physical radii E and rho/zeta. -/
theorem blockEdge_radius_transport_reserve {α q : ℝ} {Λ m : ℕ}
    {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1))
    (s σ : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |s - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (N Dγ Dmax n r K M : ℕ) (hN : N ≤ Jchart) (hn : n + Dγ ≤ N)
    (hD : Dγ ≤ Dmax) (hr : 1 ≤ r) (hnM : n ≤ M)
    (e ρ R : ℝ) (he : 0 < e) (hρ : 0 < ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (hR : 0 < R) (hRE : R ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (Num : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hNum : ∀ d I, 0 ≤ Num d I)
    (loss price : ℝ) (hloss : 0 ≤ loss) (hprice : 0 ≤ price)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ x,
      (R / e) ^ j * ‖iteratedFDeriv ℝ j (fun y => B d I y i) x‖ ≤
        (loss * price * Num d I) / derivativeReserveFactor (ρ / e) K (d - 2))
    (I : DerivativeWord2 r) (i : Fin 2) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    (R / e) ^ n * ‖iteratedFDeriv ℝ n (fun y =>
      transportedCoeff (fun z => naturalPreparationJacobian hφ s σ (yc + e • z)) Dγ
        (fun d I => B d I y) r I y i) x‖ * derivativeReserveFactor (ρ / e) K (r - 1) ≤
      transportedPolynomialUniformReservePrice N Dmax M Cpiola *
        (loss * price) * (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I) := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let Cpiola := compConst Cflow N * Cflow
  let MB := fun d I => (loss * price * Num d I) / derivativeReserveFactor (ρ / e) K (d - 2)
  have hrad : 0 < ρ / e := div_pos hρ he
  have hC : 0 ≤ Cpiola := by
    dsimp only [Cpiola]
    exact mul_nonneg (compConst_nonneg (one_le_jetConst _ _) N)
      (zero_le_one.trans (one_le_jetConst _ _))
  have hRes : 0 < derivativeReserveFactor (ρ / e) K (r - 1) := by
    unfold derivativeReserveFactor
    positivity
  have hp := preparation_cell_transported_polynomial_jet_bound hc ha hE s σ hs hσ
    (by simpa only [abs_sub_comm] using hage) N Dγ n r hN hn e (R / e) he (div_pos hR he).le
    ((div_le_div_iff_of_pos_right he).mpr hRE) yc B hB MB 1 0
    (fun d hd I i j hj x => by simpa only [pow_zero, mul_one] using hBj d hd I i j hj x) I i x
  simp only [pow_zero, mul_one] at hp
  change (R / e) ^ n * ‖iteratedFDeriv ℝ n _ x‖ ≤
    transportedPolynomialJetPrice N Dγ r n Cpiola (ocEpsilon q Λ (m - 1) / e) MB at hp
  have hcan := blockEdge_transport_reserve_budget N Dγ Dmax r K n M hD hr hnM
    Cpiola (ρ / e) (ocEpsilon q Λ (m - 1) / e) hC hrad (div_pos hE he)
    ((div_le_div_iff_of_pos_right he).mpr hρE)
    (fun d I => loss * price * Num d I) (fun d I => mul_nonneg (mul_nonneg hloss hprice) (hNum d I))
  have hsum : (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      loss * price * Num d I) =
      (loss * price) * (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I) := by
    simp only [Finset.mul_sum]
  rw [hsum] at hcan
  change transportedPolynomialJetPrice N Dγ r n Cpiola (ocEpsilon q Λ (m - 1) / e) MB *
      derivativeReserveFactor (ρ / e) K (r - 1) ≤
    transportedPolynomialUniformReservePrice N Dmax M Cpiola *
      ((loss * price) * (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I)) at hcan
  change (R / e) ^ n * ‖iteratedFDeriv ℝ n _ x‖ * derivativeReserveFactor (ρ / e) K (r - 1) ≤
    transportedPolynomialUniformReservePrice N Dmax M Cpiola *
      (loss * price) * (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I)
  exact (mul_le_mul_of_nonneg_right hp hRes.le).trans (by simpa only [mul_assoc] using hcan)

end AVRegularity.CycleJointProofs.Assembly
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs.Assembly

/-! Pointwise block remainders of transported slow fields, with the quantitative
chart reserve equal to the maximum of the Sobolev and Taylor orders. -/

/-- The fixed preparation-flow certificate on the actual anchor/reference path. -/
structure BlockSourceChartInputs (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (tS tZ Cpad Cage : ℝ) (Jchart : ℕ)
    (Cchart : ℕ → ℝ) (s σ : ℝ) : Prop where
  flow : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart
  amplitude_nonneg : 0 ≤ ocA α q Λ (m - 1)
  anchor_padded : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)
  reference_padded : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)
  age : |s - σ| ≤ 2 * Cage * ocTauPP α q Λ m

/-- One scalar chart-sampling constant for all orders through M. -/
def blockEdgeSamplingPrice (M Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  (M.factorial : ℝ) *
    (1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|) ^ M *
      ((M + 1 : ℕ) : ℝ)

theorem blockEdgeSamplingPrice_nonneg (M Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ blockEdgeSamplingPrice M Jchart Cchart := by
  unfold blockEdgeSamplingPrice
  positivity

theorem blockEdgeSamplingPrice_mono {n M : ℕ} (hn : n ≤ M)
    (Jchart : ℕ) (Cchart : ℕ → ℝ) :
    blockEdgeSamplingPrice n Jchart Cchart ≤ blockEdgeSamplingPrice M Jchart Cchart := by
  unfold blockEdgeSamplingPrice
  have hC := one_le_jetConst (preparationFlowJetConstant Cchart) (Jchart + 1)
  have hfact : (n.factorial : ℝ) ≤ M.factorial := by exact_mod_cast Nat.factorial_le hn
  apply mul_le_mul
  · exact mul_le_mul hfact (pow_le_pow_right₀ hC hn) (by positivity) (by positivity)
  · exact_mod_cast Nat.add_le_add_right hn 1
  · positivity
  · positivity

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ} {s σ : ℝ}

local notation "E₀" => ocEpsilon q Λ (m - 1)

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {F : ChartedFamily ι h D P Ctx}
  {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ} {dom : F.Domain}
  {ν e ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

/-- At physical radius E the sample uses the pure slow derivatives through L. -/
theorem blockEdge_source_sample_low
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart s σ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (L M : ℕ) (hL : L ≤ J) (hLM : L ≤ M) (hLchart : L ≤ Jchart + 1)
    (yc : Vec 2) (k : Fin 2) :
    ∀ j ≤ L, ∀ x,
      (E₀ / e) ^ j * ‖iteratedFDeriv ℝ j (fun z =>
        F.flux p c v u γ d I t (E₀⁻¹ • streamFlow φ hφ s (yc + e • z) σ) 0 k) x‖ ≤
      blockEdgeSamplingPrice M Jchart Cchart *
        ∑ a ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E₀ ρ v u γ d I a := by
  let S := ∑ a ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E₀ ρ v u γ d I a
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => blockSlowJetPrice_nonneg data v u γ d I a)
  have hseed (j : ℕ) (hj : j ≤ L) (x : Vec 2) :
      (E₀ / E₀) ^ j * ‖iteratedFDeriv ℝ j (fun Y => F.flux p c v u γ d I t Y 0 k) x‖ ≤ S := by
    rw [div_self data.slow_pos.ne', one_pow, one_mul]
    exact (blockEdge_slow_low_jets data p c v u γ hγ d hd I t hdom j (hj.trans hL) k x).trans
      (Finset.single_le_sum (fun a _ => blockSlowJetPrice_nonneg data v u γ d I a)
        (Finset.mem_range.mpr (by omega)))
  have hf := blockEdge_slow_contDiff data p c v u γ d I t hdom L (by omega) k
  have hh := blockEdge_sample_cell_jets chart.flow chart.amplitude_nonneg s σ
    chart.anchor_padded chart.reference_padded chart.age L hLchart e E₀ data.cell_pos
    data.slow_pos le_rfl yc _ hf S hS hseed
  intro j hj x
  calc
    _ ≤ (L.factorial : ℝ) *
        (1 + ∑ a ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart a|) ^ L *
          ((L + 1 : ℕ) * S) := hh j hj x
    _ = blockEdgeSamplingPrice L Jchart Cchart * S := by unfold blockEdgeSamplingPrice; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (blockEdgeSamplingPrice_mono hLM Jchart Cchart) hS

/-- At physical radius rho/zeta the sample loses only the excess derivative order. -/
theorem blockEdge_source_sample_high
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart s σ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (L n M : ℕ) (hL : L ≤ J) (hn : n ≤ K v) (hnM : n ≤ M) (hnchart : n ≤ Jchart + 1)
    (R ζ : ℝ) (hR : 0 < R) (hRE : R ≤ E₀) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hscale : ζ * (R / E₀) = ρ / E₀) (yc : Vec 2) (k : Fin 2) :
    ∀ j ≤ n, ∀ x,
      (R / e) ^ j * ‖iteratedFDeriv ℝ j (fun z =>
        F.flux p c v u γ d I t (E₀⁻¹ • streamFlow φ hφ s (yc + e • z) σ) 0 k) x‖ ≤
      blockEdgeSamplingPrice M Jchart Cchart * ζ⁻¹ ^ (n - L) *
        ∑ a ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E₀ ρ v u γ d I a := by
  let S := ∑ a ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E₀ ρ v u γ d I a
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => blockSlowJetPrice_nonneg data v u γ d I a)
  have hseed := blockEdge_slow_high_reserve data p c v u γ hγ d hd I t hdom L n hL hn
    (R / E₀) ζ (div_pos hR data.slow_pos).le ((div_le_one data.slow_pos).mpr hRE) hζ hζ1 hscale k
  have hf := blockEdge_slow_contDiff data p c v u γ d I t hdom n (by omega) k
  have hh := blockEdge_sample_cell_jets chart.flow chart.amplitude_nonneg s σ
    chart.anchor_padded chart.reference_padded chart.age n hnchart e R data.cell_pos
    hR hRE yc _ hf (ζ⁻¹ ^ (n - L) * S) (mul_nonneg (by positivity) hS) hseed
  intro j hj x
  calc
    _ ≤ (n.factorial : ℝ) *
        (1 + ∑ a ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart a|) ^ n *
          ((n + 1 : ℕ) * (ζ⁻¹ ^ (n - L) * S)) := hh j hj x
    _ = blockEdgeSamplingPrice n Jchart Cchart * (ζ⁻¹ ^ (n - L) * S) := by
      unfold blockEdgeSamplingPrice
      ring
    _ ≤ blockEdgeSamplingPrice M Jchart Cchart * (ζ⁻¹ ^ (n - L) * S) :=
      mul_le_mul_of_nonneg_right (blockEdgeSamplingPrice_mono hnM Jchart Cchart) (mul_nonneg (by positivity) hS)
    _ = _ := by ring

/-- The numerator of all the original slow prices through L. -/
def blockSlowJetNumerator (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Kmax : ℕ)
    (dom : F.Domain) (ν e E ρ : ℝ) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), (Kmax.factorial : ℝ) ^ 2 * E ^ j *
    molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))

theorem blockSlowJetPrice_sum_eq (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E₀ ρ v u γ d I j) =
      blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d I L /
        derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
  unfold blockSlowJetPrice blockSlowJetNumerator
  rw [Finset.sum_div]

theorem blockSlowJetNumerator_nonneg {E : ℝ}
    (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (L : ℕ) :
    0 ≤ blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I L := by
  unfold blockSlowJetNumerator
  apply Finset.sum_nonneg
  intro j _
  have hm := molecularRealPrice_nonneg ν ρ data.nu_pos.le data.radius_pos.le (K v) (d - 2)
    (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg data.slow_pos.le j)) hm

/-- The complete slow field in the reference cell before ordinary Taylor truncation. -/
def blockTransportedSlowCoefficient (F : ChartedFamily ι h D P Ctx)
    (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (s σ e E : ℝ) (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r) (t : ℝ) (x : Vec 2) : Vec 2 :=
  transportedCoeff (fun z => naturalPreparationJacobian hφ s σ (yc + e • z))
    (F.identity v u γ).maxOrder
    (fun d A k => F.flux p c v u γ d A t (E⁻¹ • streamFlow φ hφ s (yc + e • x) σ) 0 k)
    r I x

/-- Its qualitative regularity uses only the original coefficient reserve. -/
theorem blockTransportedSlowCoefficient_contDiff
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r) (t : ℝ)
    (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c) (n : ℕ) (hn : n ≤ K v + J) (k : Fin 2) :
    ContDiff ℝ (n : ℕ) (fun x => blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I t x k) := by
  have hJac a b : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => naturalPreparationJacobian hφ s σ (yc + e • x) a b) :=
    ((naturalPreparationJacobian_entry_smooth hφ s a b).comp
      (contDiff_const.prodMk contDiff_id)).comp (contDiff_const.add (contDiff_id.const_smul e))
  have hY : ContDiff ℝ (n : ℕ) (fun x => E₀⁻¹ • streamFlow φ hφ s (yc + e • x) σ) :=
    (((streamFlow_spatial_smooth hφ s σ).of_le (by simp)).comp
      (contDiff_const.add (contDiff_id.const_smul e))).const_smul _
  exact transportedCoeff_spatial_smooth _ hJac (F.identity v u γ).maxOrder n
    (fun d A x => F.flux p c v u γ d A t (E₀⁻¹ • streamFlow φ hφ s (yc + e • x) σ) 0)
    (fun d A k => (blockEdge_slow_contDiff data p c v u γ d A t hdom n hn k).comp hY) r I k

/-- The scalar Piola price, fixed before source data and physical scales. -/
def blockEdgeTransportPrice (N Dmax M Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  transportedPolynomialUniformReservePrice N Dmax M (compConst Cflow N * Cflow)

theorem blockEdgeTransportPrice_nonneg (N Dmax M Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ blockEdgeTransportPrice N Dmax M Jchart Cchart := by
  unfold blockEdgeTransportPrice
  apply transportedPolynomialUniformReservePrice_nonneg
  exact mul_nonneg (compConst_nonneg (one_le_jetConst _ _) N)
    (zero_le_one.trans (one_le_jetConst _ _))

/-- The original constituent price for an ordinary transported Taylor remainder. -/
def blockTransportedTaylorJetPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Kmax : ℕ)
    (dom : F.Domain) (ν e E ρ : ℝ) (Ks N M Jchart : ℕ) (Cchart : ℕ → ℝ)
    (ζ : ℝ) (v u : ι) (γ : F.Γ v u) (r : ℕ) : ℝ :=
  2 ^ (K v) * (blockEdgeTransportPrice N D M Jchart Cchart *
    blockEdgeSamplingPrice M Jchart Cchart *
      (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
        ∑ W : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d W (Ks + 1)) /
            derivativeReserveFactor (ρ / e) (K v) (r - 1)) * ζ ^ (Ks + 1)

theorem blockTransportedTaylorJetPrice_nonneg
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (Ks N M Jchart : ℕ) (Cchart : ℕ → ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (v u : ι) (γ : F.Γ v u) (r : ℕ) :
    0 ≤ blockTransportedTaylorJetPrice F K Kmax dom ν e E₀ ρ Ks N M Jchart Cchart ζ v u γ r := by
  have hrad := (div_pos data.radius_pos data.cell_pos).le
  have hnum : 0 ≤ (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
      ∑ W : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d W (Ks + 1)) :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun W _ =>
      Finset.sum_nonneg (fun _ _ => blockSlowJetNumerator_nonneg data v u γ d W (Ks + 1))))
  unfold blockTransportedTaylorJetPrice
  exact mul_nonneg (mul_nonneg (by positivity)
    (div_nonneg (mul_nonneg (mul_nonneg (blockEdgeTransportPrice_nonneg N D M Jchart Cchart)
      (blockEdgeSamplingPrice_nonneg M Jchart Cchart)) hnum)
      (by unfold derivativeReserveFactor; positivity))) (pow_nonneg hζ _)

/-- The complete coefficient retains the original slot reserve at either sampling radius. -/
theorem blockEdge_transported_radius_jets
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart s σ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (t : ℝ)
    (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (yc : Vec 2) (L N M n r : ℕ) (I : DerivativeWord2 r) (k : Fin 2)
    (hN : N ≤ Jchart) (hn : n + (F.identity v u γ).maxOrder ≤ N)
    (hr : 1 ≤ r) (hnM : n ≤ M) (hnJ : n ≤ K v + J)
    (hρE : ρ ≤ E₀) (R loss : ℝ) (hR : 0 < R) (hRE : R ≤ E₀) (hloss : 0 ≤ loss)
    (hSample : ∀ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
      ∀ A i j, j ≤ n → ∀ x,
        (R / e) ^ j * ‖iteratedFDeriv ℝ j (fun z =>
          F.flux p c v u γ d A t (E₀⁻¹ • streamFlow φ hφ s (yc + e • z) σ) 0 i) x‖ ≤
        blockEdgeSamplingPrice M Jchart Cchart * loss *
          ∑ a ∈ Finset.range (L + 1), blockSlowJetPrice F K Kmax dom ν e E₀ ρ v u γ d A a) :
    ∀ x,
      (R / e) ^ n * ‖iteratedFDeriv ℝ n
        (fun z => blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I t z k) x‖ *
          derivativeReserveFactor (ρ / e) (K v) (r - 1) ≤
      blockEdgeTransportPrice N D M Jchart Cchart * loss * blockEdgeSamplingPrice M Jchart Cchart *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ A : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
            blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d A L) := by
  intro x
  have hY : ContDiff ℝ (n : ℕ) (fun x => E₀⁻¹ • streamFlow φ hφ s (yc + e • x) σ) :=
    (((streamFlow_spatial_smooth hφ s σ).of_le (by simp)).comp
      (contDiff_const.add (contDiff_id.const_smul e))).const_smul _
  have hB d A i : ContDiff ℝ (n : ℕ) (fun z =>
      F.flux p c v u γ d A t (E₀⁻¹ • streamFlow φ hφ s (yc + e • z) σ) 0 i) :=
    (blockEdge_slow_contDiff data p c v u γ d A t hdom n hnJ i).comp hY
  have hsamp d hd A i j hj z := hSample d hd A i j hj z
  have hBj (d : ℕ) (hd : d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder)
      (A : DerivativeWord2 (d - 1)) (i : Fin 2) (j : ℕ) (hj : j ≤ n) (z : Vec 2) :
      (R / e) ^ j * ‖iteratedFDeriv ℝ j (fun y =>
        F.flux p c v u γ d A t (E₀⁻¹ • streamFlow φ hφ s (yc + e • y) σ) 0 i) z‖ ≤
      (loss * blockEdgeSamplingPrice M Jchart Cchart *
        blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d A L) /
          derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
    have hh := hsamp d hd A i j hj z
    rw [blockSlowJetPrice_sum_eq] at hh
    convert hh using 1; ring
  have hh := blockEdge_radius_transport_reserve chart.flow chart.amplitude_nonneg data.slow_pos
    s σ chart.anchor_padded chart.reference_padded chart.age N (F.identity v u γ).maxOrder D
    n r (K v) M hN hn (F.identity v u γ).le_D hr hnM e ρ R data.cell_pos data.radius_pos hρE hR hRE yc
    (fun d A z => F.flux p c v u γ d A t (E₀⁻¹ • streamFlow φ hφ s (yc + e • z) σ) 0)
    hB (fun d A => blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d A L)
    (fun d A => blockSlowJetNumerator_nonneg data v u γ d A L) loss
    (blockEdgeSamplingPrice M Jchart Cchart) hloss (blockEdgeSamplingPrice_nonneg M Jchart Cchart)
    hBj I k x
  change (R / e) ^ n * ‖iteratedFDeriv ℝ n _ x‖ * derivativeReserveFactor (ρ / e) (K v) (r - 1) ≤
    blockEdgeTransportPrice N D M Jchart Cchart *
      (loss * blockEdgeSamplingPrice M Jchart Cchart) *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ A : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
            blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d A L) at hh
  exact hh.trans_eq (by ring)

/-- Cancel a positive differentiation radius and the original derivative reserve. -/
theorem blockEdge_cancel_radius_reserve {a res S x : ℝ} (ha : 0 < a)
    (hres : 0 < res) (n : ℕ) (h : a ^ n * x * res ≤ S) :
    x ≤ (S / res) * a⁻¹ ^ n := by
  rw [inv_pow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  apply (le_div_iff₀ hres).mpr
  convert h using 1; ring

/-- Returning from the enlarged radius spends exactly the Taylor-order gain. -/
theorem blockEdge_cancel_excess_radius {a ζ res S x : ℝ} (ha : 0 < a)
    (hζ : 0 < ζ) (hres : 0 < res) (L n : ℕ) (hLn : L ≤ n)
    (h : (a / ζ) ^ n * x * res ≤ ζ⁻¹ ^ (n - L) * S) :
    a ^ n * x ≤ (S / res) * ζ ^ L := by
  have hh := blockEdge_cancel_radius_reserve (div_pos ha hζ) hres n h
  have ht := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le n)
  have hpow : ζ ^ n = ζ ^ (n - L) * ζ ^ L := by rw [← pow_add, Nat.sub_add_cancel hLn]
  have hc : a ^ n * (((ζ⁻¹ ^ (n - L) * S) / res) * (a / ζ)⁻¹ ^ n) =
      (S / res) * ζ ^ L := by
    rw [inv_div, div_pow, inv_pow]
    have ha' : a ^ n ≠ 0 := pow_ne_zero n ha.ne'
    have hz' : ζ ^ (n - L) ≠ 0 := pow_ne_zero _ hζ.ne'
    rw [hpow]
    field_simp
  exact ht.trans_eq hc

/-- The transported slow Taylor remainder spends only the maximum of the
Sobolev and Taylor reserves, with the original molecular prices. -/
theorem blockEdge_transported_remainder_jets
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart s σ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (t : ℝ) (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (yc : Vec 2) (Ks N M r : ℕ) (I : DerivativeWord2 r) (k : Fin 2)
    (hN : N ≤ Jchart) (hMN : M + D ≤ N) (hr : 1 ≤ r)
    (hKM : K v ≤ M) (hLM : Ks + 1 ≤ M) (hLJ : Ks + 1 ≤ J)
    (hρE : ρ ≤ E₀) (ζ ϖ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hϖ : 0 < ϖ)
    (hδ : e / E₀ = ζ * ϖ) (hfit : (ρ / e) * ϖ ≤ 1) :
    let A := blockEdgeTransportPrice N D M Jchart Cchart *
      blockEdgeSamplingPrice M Jchart Cchart *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ W : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
            blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d W (Ks + 1)) /
              derivativeReserveFactor (ρ / e) (K v) (r - 1)
    let f := fun z => blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I t z k
    ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x => f x - taylorSlow 0 Ks f 0 x) z‖ ≤
        2 ^ (K v) * A * ζ ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  dsimp only
  let L := Ks + 1
  let res := derivativeReserveFactor (ρ / e) (K v) (r - 1)
  let num := ∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
    ∑ W : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      blockSlowJetNumerator F K Kmax dom ν e E₀ ρ v u γ d W L
  let price := blockEdgeTransportPrice N D M Jchart Cchart * blockEdgeSamplingPrice M Jchart Cchart * num
  let f := fun z => blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I t z k
  have hrad : 0 < ρ / e := div_pos data.radius_pos data.cell_pos
  have hres : 0 < res := by dsimp only [res]; unfold derivativeReserveFactor; positivity
  have hnum : 0 ≤ num := Finset.sum_nonneg (fun d _ =>
    Finset.sum_nonneg (fun W _ => Finset.sum_nonneg (fun _ _ =>
      blockSlowJetNumerator_nonneg data v u γ d W L)))
  have hprice : 0 ≤ price := mul_nonneg (mul_nonneg
    (blockEdgeTransportPrice_nonneg N D M Jchart Cchart)
    (blockEdgeSamplingPrice_nonneg M Jchart Cchart)) hnum
  have hD := (F.identity v u γ).le_D
  have hLc : L ≤ Jchart + 1 := by dsimp only [L]; omega
  have hlow (z : Vec 2) : ‖iteratedFDeriv ℝ L f z‖ ≤ (price / res) * (ζ * ϖ) ^ L := by
    have hsamp (d : ℕ) (hd : d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder)
        (W : DerivativeWord2 (d - 1)) (i : Fin 2) (j : ℕ) (hj : j ≤ L) (x : Vec 2) :=
      blockEdge_source_sample_low data chart p c v u γ hγ d
        (Finset.mem_Icc.mpr ⟨by have hdlo := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩) W t hdom L M hLJ hLM hLc yc i j hj x
    have hh := blockEdge_transported_radius_jets data chart p c v u γ t hdom yc L N M L r I k
      hN (by dsimp only [L]; omega) hr hLM (by dsimp only [L]; omega) hρE E₀ 1 data.slow_pos le_rfl
      zero_le_one (fun d hd W i j hj x => by simpa only [mul_one] using hsamp d hd W i j hj x) z
    change (E₀ / e) ^ L * ‖iteratedFDeriv ℝ L f z‖ * res ≤
      blockEdgeTransportPrice N D M Jchart Cchart * 1 * blockEdgeSamplingPrice M Jchart Cchart * num at hh
    simp only [mul_one] at hh
    have hb := blockEdge_cancel_radius_reserve (div_pos data.slow_pos data.cell_pos) hres L hh
    simpa only [inv_div, hδ] using hb
  let R := ρ / ζ
  have hR : 0 < R := div_pos data.radius_pos hζ
  have hscale : ζ * (R / E₀) = ρ / E₀ := by dsimp only [R]; field_simp [hζ.ne']
  have hrat : R / E₀ = (ρ / e) * ϖ := by
    apply mul_left_cancel₀ hζ.ne'
    rw [hscale]
    calc
      ρ / E₀ = (ρ / e) * (e / E₀) := by field_simp [data.cell_pos.ne', data.slow_pos.ne']
      _ = ζ * ((ρ / e) * ϖ) := by rw [hδ]; ring
  have hRE : R ≤ E₀ := (div_le_one data.slow_pos).mp (hrat ▸ hfit)
  have hhigh (n : ℕ) (hnL : Ks < n) (hn : n ≤ K v) (z : Vec 2) :
      (ρ / e) ^ n * ‖iteratedFDeriv ℝ n f z‖ ≤ (price / res) * ζ ^ L := by
    have hnc : n ≤ Jchart + 1 := by omega
    have hsamp (d : ℕ) (hd : d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder)
        (W : DerivativeWord2 (d - 1)) (i : Fin 2) (j : ℕ) (hj : j ≤ n) (x : Vec 2) :=
      blockEdge_source_sample_high data chart p c v u γ hγ d
        (Finset.mem_Icc.mpr ⟨by have hdlo := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩) W t hdom L n M hLJ hn
        (hn.trans hKM) hnc R ζ hR hRE hζ hζ1 hscale yc i j hj x
    have hh := blockEdge_transported_radius_jets data chart p c v u γ t hdom yc L N M n r I k
      hN (by omega) hr (hn.trans hKM) (by omega) hρE R (ζ⁻¹ ^ (n - L)) hR hRE (by positivity)
      (fun d hd W i j hj x => hsamp d hd W i j hj x) z
    change (R / e) ^ n * ‖iteratedFDeriv ℝ n f z‖ * res ≤
      blockEdgeTransportPrice N D M Jchart Cchart * ζ⁻¹ ^ (n - L) *
        blockEdgeSamplingPrice M Jchart Cchart * num at hh
    have hh' : ((ρ / e) / ζ) ^ n * ‖iteratedFDeriv ℝ n f z‖ * res ≤ ζ⁻¹ ^ (n - L) * price := by
      convert hh using 1 <;> dsimp only [R, price] <;> ring
    exact blockEdge_cancel_excess_radius (div_pos data.radius_pos data.cell_pos) hζ hres
      L n (by dsimp only [L]; omega) hh'
  have hf := blockTransportedSlowCoefficient_contDiff (hφ := hφ) (s := s) (σ := σ) data p c v u γ yc r I t hdom
    (max (K v) L) (by dsimp only [L]; omega) k
  exact blockEdge_remainder_jet_budget Ks (K v) f hf ϖ (ρ / e) ζ (price / res) hϖ
    (div_pos data.radius_pos data.cell_pos).le hfit hζ.le (div_nonneg hprice hres.le) hlow hhigh

end AVRegularity.CycleJointProofs.Assembly
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs.Assembly

/-! Measurable zero extensions of the transported slow field and its ordinary
Taylor remainder. The extension is zero outside the cell window and at inactive
partition times, so no off-output smoothness premise is used. -/

attribute [local instance] Classical.propDecidable

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {φ : ℝ → Vec 2 → ℝ}

/-- The complete transported coefficient, extended by zero at inactive times. -/
def blockTransportedTimeCoefficient (F : ChartedFamily ι h D P Ctx)
    (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (s σ e E timeScale a b : ℝ) (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r)
    (k : Fin 2) (τ : ℝ) (x : Vec 2) : ℝ :=
  if τ ∈ Set.Icc a b ∧ F.weight p (timeScale * τ) ≠ 0 then
    blockTransportedSlowCoefficient F hφ p c v u γ s σ e E yc r I (timeScale * τ) x k
  else 0

/-- Ordinary Taylor subtraction of the extended transported field. -/
def blockTransportedTimeRemainder (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (s σ e E timeScale a b : ℝ) (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r)
    (k : Fin 2) (τ : ℝ) (x : Vec 2) : ℝ :=
  let f := blockTransportedTimeCoefficient F hφ p c v u γ s σ e E timeScale a b yc r I k τ
  f x - taylorSlow 0 Ks f 0 x

/-- The fixed anchor/reference chart introduces no moving spatial argument in time. -/
theorem blockTransportedTimeCoefficient_measurable (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (s σ e E timeScale a b : ℝ) (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r)
    (k : Fin 2) (x : Vec 2) :
    Measurable (fun τ => blockTransportedTimeCoefficient F hφ p c v u γ
      s σ e E timeScale a b yc r I k τ x) := by
  have ht : Measurable (fun τ : ℝ => timeScale * τ) := measurable_const.mul measurable_id
  have hguard : MeasurableSet {τ : ℝ | τ ∈ Set.Icc a b ∧ F.weight p (timeScale * τ) ≠ 0} :=
    measurableSet_Icc.inter ((measurableSet_eq_fun ((hw p).comp ht) measurable_const).compl)
  apply Measurable.ite hguard _ measurable_const
  unfold blockTransportedSlowCoefficient transportedCoeff
  apply Finset.measurable_sum
  intro d _
  apply Finset.measurable_sum
  intro W _
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.mul (((measurable_pi_apply i).comp (hm p c v u γ d W _ 0)).comp ht)).mul measurable_const

variable {α q : ℝ} {Λ m : ℕ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ} {s σ : ℝ}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
  {ν e ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

local notation "E₀" => ocEpsilon q Λ (m - 1)
local notation "dom₀" => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)

/-- The nonzero time slices use only the supplied output-window regularity. -/
theorem blockTransportedTimeCoefficient_contDiff
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale a b : ℝ) (htime : ∀ τ ∈ Set.Icc a b, timeScale * τ ∈ Set.Icc tS tZ)
    (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r) (k : Fin 2) (τ : ℝ)
    (n : ℕ) (hn : n ≤ K v + J) :
    ContDiff ℝ (n : ℕ) (blockTransportedTimeCoefficient F hφ p c v u γ
      s σ e E₀ timeScale a b yc r I k τ) := by
  unfold blockTransportedTimeCoefficient
  split_ifs with ht
  · have hout := inactiveTimeZeroFamily_weight_ne_zero_mem_output F p (timeScale * τ) ht.2
    exact blockTransportedSlowCoefficient_contDiff data p c v u γ yc r I _
      (fun _ => ⟨⟨hout, htime τ ht.1⟩, Set.mem_univ _⟩) n hn k
  · exact contDiff_const

/-- The same zero extension makes its Taylor subtraction measurable in time. -/
theorem blockTransportedTimeRemainder_measurable
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale a b : ℝ) (htime : ∀ τ ∈ Set.Icc a b, timeScale * τ ∈ Set.Icc tS tZ)
    (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r) (k : Fin 2)
    (Ks : ℕ) (hKs : Ks ≤ K v + J) (x : Vec 2) :
    Measurable (fun τ => blockTransportedTimeRemainder Ks F hφ p c v u γ
      s σ e E₀ timeScale a b yc r I k τ x) := by
  let f := blockTransportedTimeCoefficient F hφ p c v u γ s σ e E₀ timeScale a b yc r I k
  have hfm (z : Vec 2) : Measurable (fun τ => f τ z) :=
    blockTransportedTimeCoefficient_measurable F hw hm hφ p c v u γ s σ e E₀ timeScale a b yc r I k z
  have hfc (τ : ℝ) : ContDiff ℝ (Ks : ℕ) (f τ) :=
    blockTransportedTimeCoefficient_contDiff data p c v u γ timeScale a b htime yc r I k τ Ks hKs
  have ht := Weighted.taylorSlow_parameter_measurable 0 Ks (fun τ z _ => f τ z)
    (fun z _ => hfm z) (fun τ _ => hfc τ) 0 1 x
  simpa only [blockTransportedTimeRemainder, one_smul, Pi.sub_apply, f] using (hfm x).fun_sub ht

/-- Spatial derivatives of the time-extended remainder require no extra jets. -/
theorem blockTransportedTimeRemainder_contDiff
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale a b : ℝ) (htime : ∀ τ ∈ Set.Icc a b, timeScale * τ ∈ Set.Icc tS tZ)
    (yc : Vec 2) (r : ℕ) (I : DerivativeWord2 r) (k : Fin 2) (Ks n : ℕ)
    (hn : n ≤ K v + J) (τ : ℝ) :
    ContDiff ℝ (n : ℕ) (blockTransportedTimeRemainder Ks F hφ p c v u γ
      s σ e E₀ timeScale a b yc r I k τ) :=
  (blockTransportedTimeCoefficient_contDiff data p c v u γ timeScale a b htime yc r I k τ n hn).sub
    (blockEdge_taylor_contDiff Ks n _)

/-- The time extension retains the original transported Taylor price pointwise. -/
theorem blockTransportedTimeRemainder_jet_bound
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart s σ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (timeScale a b : ℝ) (htime : ∀ τ ∈ Set.Icc a b, timeScale * τ ∈ Set.Icc tS tZ)
    (yc : Vec 2) (Ks N M r : ℕ) (I : DerivativeWord2 r) (k : Fin 2)
    (hN : N ≤ Jchart) (hMN : M + D ≤ N) (hr : 1 ≤ r)
    (hKM : K v ≤ M) (hLM : Ks + 1 ≤ M) (hLJ : Ks + 1 ≤ J)
    (hρE : ρ ≤ E₀) (ζ ϖ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hϖ : 0 < ϖ)
    (hδ : e / E₀ = ζ * ϖ) (hfit : (ρ / e) * ϖ ≤ 1) (τ : ℝ) :
    ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (blockTransportedTimeRemainder Ks F hφ p c v u γ
        s σ e E₀ timeScale a b yc r I k τ) z‖ ≤
      blockTransportedTaylorJetPrice F K Kmax dom₀ ν e E₀ ρ Ks N M Jchart Cchart ζ v u γ r *
        polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  by_cases ht : τ ∈ Set.Icc a b ∧ F.weight p (timeScale * τ) ≠ 0
  · have hout := inactiveTimeZeroFamily_weight_ne_zero_mem_output F p (timeScale * τ) ht.2
    have hb := blockEdge_transported_remainder_jets data chart p c v u γ hγ (timeScale * τ)
      (fun _ => ⟨⟨hout, htime τ ht.1⟩, Set.mem_univ _⟩) yc Ks N M r I k hN hMN hr hKM hLM hLJ
      hρE ζ ϖ hζ hζ1 hϖ hδ hfit
    have hf : blockTransportedTimeCoefficient F hφ p c v u γ s σ e E₀ timeScale a b yc r I k τ =
        fun x => blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I (timeScale * τ) x k := by
      funext x
      simp only [blockTransportedTimeCoefficient, ite_eq_left ht]
    have he : blockTransportedTimeRemainder Ks F hφ p c v u γ
        s σ e E₀ timeScale a b yc r I k τ = fun x =>
          blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I (timeScale * τ) x k -
            taylorSlow 0 Ks
              (fun y => blockTransportedSlowCoefficient F hφ p c v u γ s σ e E₀ yc r I (timeScale * τ) y k) 0 x := by
      unfold blockTransportedTimeRemainder
      dsimp only
      rw [hf]
    rw [he]
    simpa only [blockTransportedTaylorJetPrice] using hb
  · have hf : blockTransportedTimeCoefficient F hφ p c v u γ s σ e E₀ timeScale a b yc r I k τ =
        fun _ => 0 := by
      funext x
      simp only [blockTransportedTimeCoefficient, ite_eq_right ht]
    have htz : taylorSlow 0 Ks (fun _ : Vec 2 => (0 : ℝ)) 0 = fun _ => 0 := by
      funext x
      simp only [taylorSlow, iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply, mul_zero, Finset.sum_const_zero]
    have he : blockTransportedTimeRemainder Ks F hφ p c v u γ
        s σ e E₀ timeScale a b yc r I k τ = fun _ => 0 := by
      unfold blockTransportedTimeRemainder
      dsimp only
      rw [hf, htz]
      simp only [sub_zero]
    rw [he]
    intro j _ z
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    exact mul_nonneg (blockTransportedTaylorJetPrice_nonneg data Ks N M Jchart Cchart ζ hζ.le v u γ r)
      (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _)

/-- There is no transported remainder above the source identity's maximal order. -/
theorem blockTransportedTimeRemainder_zero_at_or_above
    (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (s σ e E timeScale a b : ℝ) (yc : Vec 2) (Ks r : ℕ)
    (hlarge : (F.identity v u γ).maxOrder ≤ r) (I : DerivativeWord2 r) (k : Fin 2) (τ : ℝ) :
    blockTransportedTimeRemainder Ks F hφ p c v u γ s σ e E timeScale a b yc r I k τ = fun _ => 0 := by
  have hf : blockTransportedTimeCoefficient F hφ p c v u γ
      s σ e E timeScale a b yc r I k τ = fun _ => 0 := by
    funext x
    unfold blockTransportedTimeCoefficient
    split_ifs
    · unfold blockTransportedSlowCoefficient
      rw [transportedCoeff_zero_at_or_above _ _ _ _ hlarge]
      rfl
    · rfl
  have hz : taylorSlow 0 Ks (fun _ : Vec 2 => (0 : ℝ)) 0 = fun _ => 0 := by
    funext x
    simp only [taylorSlow, iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply, mul_zero, Finset.sum_const_zero]
  unfold blockTransportedTimeRemainder
  dsimp only
  rw [hf, hz]
  simp only [sub_zero]

end AVRegularity.CycleJointProofs.Assembly
end
