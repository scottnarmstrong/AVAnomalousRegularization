-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
public import AVRegularity.Definitions.Construction.DiagLetter
import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Uniqueness

/-! Symmetric word arrays are determined by their action on exponential test fields.

If two symmetric ordered-word coefficient arrays act identically on every smooth coarse test field
at a point `(t, X, z)`, their coefficients agree there. The proof tests against the fields
`Y ↦ exp (ξ · Y) • w` and reads off the coefficients of the resulting polynomial in `ξ`. -/

/-- A real polynomial vanishing at every point has zero coefficients. -/
theorem poly_coeff_zero (n : ℕ) (c : ℕ → ℝ)
    (h : ∀ x : ℝ, ∑ k ∈ Finset.range (n + 1), c k * x ^ k = 0) : ∀ k ≤ n, c k = 0 := by
  let p : Polynomial ℝ := ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k
  have hp : p = 0 := Polynomial.funext (fun x => by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    exact h x)
  intro k hk
  have := congrArg (fun q => q.coeff k) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single k] at this
  · simpa using this
  · intro j _ hj; simp [Ne.symm hj]
  · intro hk'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk'

/-- Vector-valued version of `poly_coeff_zero`. -/
theorem poly_coeff_zero_vec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (c : ℕ → F) (h : ∀ x : ℝ, ∑ k ∈ Finset.range (n + 1), x ^ k • c k = 0) :
    ∀ k ≤ n, c k = 0 := by
  intro k hk
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ℓ
  have := poly_coeff_zero n (fun j => ℓ (c j)) (fun x => by
    have := congrArg ℓ (h x)
    simpa [map_sum, mul_comm] using this) k hk
  exact this


/-- The exponential test field `Y ↦ exp (ξ · Y) • w`. -/
def expField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ξ : Vec 2) (w : E) :
    Vec 2 → E :=
  fun Y => Real.exp (∑ i, ξ i * Y i) • w

private def linForm (ξ : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  ∑ i : Fin 2, ξ i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i

private theorem linForm_apply (ξ Y : Vec 2) : linForm ξ Y = ∑ i, ξ i * Y i := by
  simp [linForm]

private theorem fderiv_scaled_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ξ : Vec 2) (w : E) (c : ℝ) (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun Y : Vec 2 => (c * Real.exp (∑ j, ξ j * Y j)) • w) x (basisVec i) =
      (c * ξ i * Real.exp (∑ j, ξ j * x j)) • w := by
  have hL : HasFDerivAt (fun Y : Vec 2 => ∑ j, ξ j * Y j) (linForm ξ) x := by
    have e : (fun Y : Vec 2 => ∑ j, ξ j * Y j) = ⇑(linForm ξ) := by
      funext Y; rw [linForm_apply]
    rw [e]
    exact (linForm ξ).hasFDerivAt
  have he : HasFDerivAt (fun Y : Vec 2 => c * Real.exp (∑ j, ξ j * Y j))
      (((c * Real.exp (∑ j, ξ j * x j)) : ℝ) • linForm ξ) x := by
    have h1 := (Real.hasDerivAt_exp (∑ j, ξ j * x j)).comp_hasFDerivAt x hL
    have h2 := h1.const_mul c
    convert h2 using 1
    · rfl
    · rw [smul_smul]
  have hs := he.smul_const w
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, linForm_apply]
  have : ∑ j, ξ j * basisVec i j = ξ i := by
    simp [basisVec, Pi.single_apply]
  rw [this]
  simp only [smul_eq_mul]
  congr 1
  ring

theorem orderedDerivative_expField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (α : DerivativeWord2 m) (ξ : Vec 2) (w : E) :
    orderedDerivative α (expField ξ w) =
      fun X => ((∏ j, ξ (α j)) * Real.exp (∑ i, ξ i * X i)) • w := by
  have key : ∀ (l : List (Fin 2)) (c : ℝ),
      l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i))
        (fun Y : Vec 2 => (c * Real.exp (∑ j, ξ j * Y j)) • w) =
      fun X => ((c * (l.map ξ).prod) * Real.exp (∑ i, ξ i * X i)) • w := by
    intro l
    induction l with
    | nil => intro c; simp
    | cons a l ih =>
      intro c
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      have : (fun x : Vec 2 => fderiv ℝ (fun Y : Vec 2 => (c * Real.exp (∑ j, ξ j * Y j)) • w) x
          (basisVec a)) = fun x => ((c * ξ a) * Real.exp (∑ j, ξ j * x j)) • w := by
        funext x
        rw [fderiv_scaled_exp]
      rw [this, ih]
      funext X
      congr 2
      ring
  have h1 : expField ξ w = fun Y : Vec 2 => ((1 : ℝ) * Real.exp (∑ j, ξ j * Y j)) • w := by
    funext Y; simp [expField]
  unfold orderedDerivative
  rw [h1, key]
  funext X
  simp [List.prod_ofFn]


/-- The number of letters `1` of a word in two directions. -/
def onesCount {m : ℕ} (α : DerivativeWord2 m) : ℕ :=
  (Finset.univ.filter (fun j => α j = 1)).card

theorem onesCount_le {m : ℕ} (α : DerivativeWord2 m) : onesCount α ≤ m := by
  unfold onesCount
  calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

private theorem zeros_add_ones {m : ℕ} (α : DerivativeWord2 m) :
    (Finset.univ.filter (fun j => α j = 0)).card + onesCount α = m := by
  unfold onesCount
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun j => α j = 0)
  have e : (Finset.univ.filter (fun j => ¬ α j = 0)) = Finset.univ.filter (fun j => α j = 1) := by
    apply Finset.filter_congr
    intro j _
    generalize α j = x
    fin_cases x <;> simp
  rw [e] at h
  simpa using h

theorem exists_perm_of_onesCount_eq {m : ℕ} (α β : DerivativeWord2 m)
    (h : onesCount α = onesCount β) : ∃ σ : Equiv.Perm (Fin m), α = β ∘ σ := by
  have hc : ∀ c : Fin 2, Fintype.card {a // α a = c} = Fintype.card {a // β a = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    fin_cases c
    · have h1 := zeros_add_ones α
      have h2 := zeros_add_ones β
      simp only [Fin.zero_eta]
      omega
    · exact h
  let e : ∀ c : Fin 2, {a // α a = c} ≃ {b // β b = c} := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm


section Main

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_expField [DecidableEq ι] (n : ℕ) (B : LiftCoeff ι h) (ξ : Vec 2) (u₀ : ι)
    (w₀ : h u₀) (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n B (fun _ => expField ξ (Pi.single u₀ w₀ : ∀ i, h i)) t X z v =
      Real.exp (∑ i, ξ i * X i) • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        (∏ j, ξ (α j)) • B m α t X z v u₀ w₀ := by
  unfold liftApply
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [orderedDerivative_expField]
  rw [Finset.sum_eq_single u₀]
  · simp only [Pi.smul_apply, Pi.single_eq_same, map_smul, smul_smul]
    rw [mul_comm]
  · intro u _ hu
    simp [Pi.single_eq_of_ne hu]
  · intro hu; exact absurd (Finset.mem_univ u₀) hu



theorem prod_expDirection {m : ℕ} (α : DerivativeWord2 m) (s r : ℝ) :
    ∏ j, (![s, s * r] : Fin 2 → ℝ) (α j) = s ^ m * r ^ onesCount α := by
  have e : ∀ j, (![s, s * r] : Fin 2 → ℝ) (α j) = s * (if α j = 1 then r else 1) := by
    intro j
    generalize α j = x
    fin_cases x <;> simp
  simp only [e]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite]
  simp [onesCount]

/-- Symmetric word arrays that act identically on all smooth test fields at a point agree there. -/
theorem coeff_eq_of_apply_eq (n : ℕ) (A A' : LiftCoeff ι h)
    (hs : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), A m (α ∘ σ) = A m α)
    (hs' : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), A' m (α ∘ σ) = A' m α)
    (t : ℝ) (X z : Vec 2)
    (hap : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
      liftApply n A (fun _ => a₀) t X z = liftApply n A' (fun _ => a₀) t X z) :
    ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, A m α t X z v u = A' m α t X z v u := by
  classical
  intro m hm α₀ v u₀
  let Δ : ∀ m', DerivativeWord2 m' → (h u₀ →L[ℝ] h v) :=
    fun m' α => A m' α t X z v u₀ - A' m' α t X z v u₀
  suffices H : ∀ w₀ : h u₀, Δ m α₀ w₀ = 0 by
    have hΔ : Δ m α₀ = 0 := ContinuousLinearMap.ext H
    exact sub_eq_zero.mp hΔ
  intro w₀
  have key : ∀ s r : ℝ, ∑ m' ∈ Finset.range (n + 1),
      s ^ m' • ∑ α : DerivativeWord2 m', r ^ onesCount α • Δ m' α w₀ = 0 := by
    intro s r
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (expField ![s, s * r] (Pi.single u₀ w₀ : ∀ i, h i)) := by
      unfold expField
      have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => Real.exp (∑ i, (![s, s * r] : Fin 2 → ℝ) i * Y i)) := by
        refine Real.contDiff_exp.comp ?_
        refine ContDiff.sum (fun i _ => ?_)
        exact contDiff_const.mul (contDiff_apply ℝ ℝ i)
      exact h0.smul contDiff_const
    have h1 := congrFun (hap _ hcd) v
    rw [liftApply_expField, liftApply_expField] at h1
    have h3 := smul_right_injective _ (Real.exp_pos (∑ i, (![s, s * r] : Fin 2 → ℝ) i * X i)).ne' h1
    have h4 := sub_eq_zero.mpr h3
    rw [← Finset.sum_sub_distrib] at h4
    rw [← h4]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [prod_expDirection, ← smul_sub, smul_smul]
    simp only [Δ, sub_apply, smul_sub]
  have hA : ∀ r : ℝ, ∀ m' ≤ n, ∑ α : DerivativeWord2 m', r ^ onesCount α • Δ m' α w₀ = 0 := by
    intro r
    exact poly_coeff_zero_vec n (fun m' => ∑ α : DerivativeWord2 m', r ^ onesCount α • Δ m' α w₀)
      (fun x => key x r)
  have hB : ∀ k ≤ m, ∑ α ∈ Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = k),
      Δ m α w₀ = 0 := by
    have hfib : ∀ r : ℝ, ∑ k ∈ Finset.range (m + 1), r ^ k •
        ∑ α ∈ Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = k), Δ m α w₀ = 0 := by
      intro r
      rw [← hA r m hm]
      rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (DerivativeWord2 m)))
        (t := Finset.range (m + 1)) (g := fun α => onesCount α)
        (fun α _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (onesCount_le α)))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun α hα => ?_)
      rw [(Finset.mem_filter.mp hα).2]
    exact poly_coeff_zero_vec m _ hfib
  have hC := hB (onesCount α₀) (onesCount_le α₀)
  have hconst : ∀ α ∈ Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = onesCount α₀),
      Δ m α w₀ = Δ m α₀ w₀ := by
    intro α hα
    obtain ⟨σ, hσ⟩ := exists_perm_of_onesCount_eq α α₀ (Finset.mem_filter.mp hα).2
    simp only [Δ, sub_apply]
    rw [hσ, hs m α₀ σ, hs' m α₀ σ]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const] at hC
  have hpos : (Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = onesCount α₀)).card ≠ 0 := by
    apply Finset.card_ne_zero_of_mem (a := α₀)
    simp
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hC
  exact (smul_eq_zero.mp hC).resolve_left (by exact_mod_cast hpos)

end Main

end AVRegularity.Uniqueness
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.Uniqueness

/-! Pointwise algebra of the window uniqueness argument for the cell equation.

The weak integrand of a cell solution with metric `G(t)` and drift `v` is rewritten as the
integrand of the unit-metric, drift-free cell equation with the scalar source `-v·∇u` and the flux
`(G - 1)∇u`; and the real part of the integrand tested against the conjugate trial function obeys a
Gårding inequality. -/

/-- The cell coefficients with the `z`-independent metric `G(t)` and drift `v`. -/
def trueC (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) : CellCoefficients :=
  { G := fun t _ => G t, v := v, θ := 0, κ := 0 }

/-- The unit-metric, drift-free cell coefficients. -/
def proxyC : CellCoefficients :=
  { G := fun _ _ => 1, v := fun _ _ => 0, θ := 0, κ := 0 }

theorem proxy_metric : IsCellMetric proxyC.G := by
  refine ⟨measurable_const, fun t n z => rfl, fun t z => Matrix.isSymm_one, fun t z ξ => ?_⟩
  have h : ∑ i, ∑ j, ξ i * (proxyC.G t z) i j * ξ j = ∑ i, ξ i ^ 2 := by
    simp [proxyC, Matrix.one_apply, Fin.sum_univ_two, sq]
  rw [h]
  have h0 : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  constructor <;> linarith

theorem proxy_vmeas : Measurable (fun p : ℝ × Vec 2 => proxyC.v p.1 p.2) := measurable_const

theorem proxy_vbound : ∀ t x, ∑ i, proxyC.v t x i ^ 2 ≤ (0 : ℝ) ^ 2 := by
  intro t x; simp [proxyC]

/-- The scalar source `-v·∇u` carrying the drift. -/
def driftSrc (v : ℝ → Vec 2 → Vec 2) (du : Fin 2 → Vec 2 → ℂ) (r : ℝ) : Vec 2 → ℂ :=
  fun x => -(∑ k : Fin 2, (v r x k : ℂ) * du k x)

/-- The flux `(G - 1)∇u` carrying the metric. -/
def metricFlux (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (du : Fin 2 → Vec 2 → ℂ) (r : ℝ) :
    Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun x => WithLp.toLp 2 (fun k => ∑ i : Fin 2,
    (((G r i k - (1 : Matrix (Fin 2) (Fin 2) ℝ) i k : ℝ) : ℂ)) * du i x)

theorem rhs_true_eq_proxy (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (r : ℝ)
    (u : Vec 2 → ℂ) (du : Fin 2 → Vec 2 → ℂ) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (x : Vec 2) :
    cellLiteralRHS (trueC G v) r u du ψ dψ 0 0 x =
      cellLiteralRHS proxyC r u du ψ dψ (driftSrc v du r) (metricFlux G du r) x := by
  simp only [cellLiteralRHS, trueC, proxyC, driftSrc, metricFlux, Fin.sum_univ_two,
    Matrix.one_apply, PiLp.zero_apply, Pi.ofNat_apply]
  simp
  ring

/-- Real part of the weak integrand tested by the conjugate of the trial function. -/
theorem garding_pointwise (G : Matrix (Fin 2) (Fin 2) ℝ) (lo Mv : ℝ) (hlo : 0 < lo)
    (hq : ∀ ξ : Fin 2 → ℝ, lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j)
    (v : Fin 2 → ℝ) (hv : ∀ k, |v k| ≤ Mv) (u : ℂ) (d : Fin 2 → ℂ) :
    (-(∑ j, ∑ k, (G j k : ℂ) * d j * star (d k)) - ∑ k, (v k : ℂ) * d k * star u).re
      ≤ (Mv ^ 2 / lo) * ‖u‖ ^ 2 := by
  have h1 : (∑ j, ∑ k, (G j k : ℂ) * d j * star (d k)).re =
      (∑ i, ∑ j, G i j * (d i).re * (d j).re) + (∑ i, ∑ j, G i j * (d i).im * (d j).im) := by
    simp only [Fin.sum_univ_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hqa := hq (fun i => (d i).re)
  have hqb := hq (fun i => (d i).im)
  have hn : ∀ i, ‖d i‖ ^ 2 = (d i).re ^ 2 + (d i).im ^ 2 := fun i => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ((∑ k, (v k : ℂ) * d k * star u).re) ≥ -(Mv * ‖u‖ * (‖d 0‖ + ‖d 1‖)) := by
    have h3 : |(∑ k, (v k : ℂ) * d k * star u).re| ≤ Mv * ‖u‖ * (‖d 0‖ + ‖d 1‖) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      refine (norm_sum_le _ _).trans ?_
      simp only [Fin.sum_univ_two, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
      have h0 := norm_nonneg (d 0)
      have h1 := norm_nonneg (d 1)
      have h2 := norm_nonneg u
      nlinarith [mul_le_mul_of_nonneg_right (hv 0) (mul_nonneg h0 h2),
        mul_le_mul_of_nonneg_right (hv 1) (mul_nonneg h1 h2)]
    linarith [neg_abs_le (∑ k, (v k : ℂ) * d k * star u).re]
  have key : ∀ X U : ℝ, Mv * U * X ≤ lo / 2 * X ^ 2 + Mv ^ 2 / lo / 2 * U ^ 2 := by
    intro X U
    have h := sq_nonneg (lo * X - Mv * U)
    have : Mv ^ 2 / lo / 2 * U ^ 2 = (Mv * U) ^ 2 / (2 * lo) := by field_simp
    rw [this, ← sub_nonneg]
    have : lo / 2 * X ^ 2 + (Mv * U) ^ 2 / (2 * lo) - Mv * U * X =
        (lo * X - Mv * U) ^ 2 / (2 * lo) := by
      field_simp; ring
    rw [this]; positivity
  have k0 := key ‖d 0‖ ‖u‖
  have k1 := key ‖d 1‖ ‖u‖
  have e0 := hn 0
  have e1 := hn 1
  rw [Complex.sub_re, Complex.neg_re, h1]
  simp only [Fin.sum_univ_two] at hqa hqb e0 e1 h2 ⊢
  nlinarith [k0, k1, e0, e1, hqa, hqb, h2]

end AVRegularity.Uniqueness
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Uniqueness

/-! The provenance of an identity of the next family determines its source.

For a stage with injective provenance whose births are older than the passage, the extended
components `succComp m v 𝔱` determine `(v, 𝔱)`, and the provenance list of a path determines the
path; hence a source of the next family is determined by its provenance and its two components. -/

open AVRegularity

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The component `(v, 𝔱)` of the passage determines `v` and `𝔱` when the births of `v` and `v'` are
older than the passage. -/
theorem succComp_inj {m : ℕ} (hm : 1 ≤ m) {v v' : Comp} {t t' : List WordLetter}
    (hv : ∀ e ∈ v.births, m ≤ e.scale) (hv' : ∀ e ∈ v'.births, m ≤ e.scale)
    (h : succComp m v t = succComp m v' t') : v = v' ∧ t = t' := by
  unfold succComp at h
  by_cases ht : t = []
  · by_cases ht' : t' = []
    · simp only [ht, ht', ↓reduceDIte] at h
      exact ⟨h, ht.trans ht'.symm⟩
    · simp only [ht, ht', ↓reduceDIte] at h
      exfalso
      have := hv ⟨m - 1, t', ht'⟩ (by rw [h]; simp)
      simp at this
      omega
  · by_cases ht' : t' = []
    · simp only [ht, ht', ↓reduceDIte] at h
      exfalso
      have := hv' ⟨m - 1, t, ht⟩ (by rw [← h]; simp)
      simp at this
      omega
    · simp only [ht, ht', ↓reduceDIte] at h
      obtain ⟨r, bs⟩ := v
      obtain ⟨r', bs'⟩ := v'
      simp only [Comp.mk.injEq, List.cons.injEq, BirthEvent.mk.injEq, true_and] at h
      obtain ⟨hr, ht2, hb⟩ := h
      subst hr hb
      exact ⟨rfl, ht2⟩

variable {G : GenStage D hr Dm b j₀}

theorem StagePath.eq_of_provList (hinj : ∀ v u, Function.Injective (G.prov v u)) {h : ℕ}
    (π π' : StagePath G h) (hl : π.provList = π'.provList) : π = π' := by
  unfold StagePath.provList at hl
  have hf := List.ofFn_inj.mp hl
  have key : ∀ (a a' : Σ (v u : CompIn G.comps), G.fam.Γ v u),
      (a.1.1, a.2.1.1, G.prov _ _ a.2.2) = (a'.1.1, a'.2.1.1, G.prov _ _ a'.2.2) → a = a' := by
    rintro ⟨v, u, γ⟩ ⟨v', u', γ'⟩ hj
    simp only [Prod.mk.injEq] at hj
    obtain ⟨hv, hu, hp⟩ := hj
    have hv2 : v = v' := Subtype.ext hv
    have hu2 : u = u' := Subtype.ext hu
    subst hv2 hu2
    have := hinj v u hp
    subst this
    rfl
  have hstep : π.step = π'.step := funext (fun j => key _ _ (congrFun hf j))
  cases π
  cases π'
  simp only at hstep
  subst hstep
  rfl

theorem StagePath.length_provList {h : ℕ} (π : StagePath G h) : π.provList.length = h := by
  simp [StagePath.provList]


/-- A source of the next family is determined by its provenance and its two components. -/
theorem succSource_eq_of_prov (hm : 1 ≤ G.level) (hinj : ∀ v u, Function.Injective (G.prov v u))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale) {A : Finset WordLetter} {J : ℕ}
    (s s' : SuccSource G) (hs : s.Valid A J) (hs' : s'.Valid A J)
    (hprov : s.prov G.level = s'.prov G.level)
    (hsrc : s.srcComp G.level = s'.srcComp G.level)
    (htgt : s.tgtComp G.level = s'.tgtComp G.level) : s = s' := by
  have hpathsrc : ∀ {h : ℕ} (π : StagePath G h), 1 ≤ h → ∀ e ∈ π.src.births, G.level ≤ e.scale := by
    intro h π hh e he
    have hh0 : 0 < h := hh
    have : π.src = (π.step ⟨0, hh⟩).2.1.1 := by simp only [StagePath.src, hh0, ↓reduceDIte]
    rw [this] at he
    exact hold _ (π.step ⟨0, hh⟩).2.1.2 e he
  cases s with
  | copyDir t v u γ =>
    cases s' with
    | copyDir t' v' u' γ' =>
      simp only [SuccSource.srcComp, SuccSource.oldSrc, SuccSource.word] at hsrc
      simp only [SuccSource.tgtComp, SuccSource.oldTgt, SuccSource.newWord, SuccSource.letter?,
        SuccSource.word] at htgt
      obtain ⟨hu, ht⟩ := succComp_inj hm (hold _ u.2) (hold _ u'.2) hsrc
      subst ht
      obtain ⟨hv, -⟩ := succComp_inj hm (hold _ v.2) (hold _ v'.2) htgt
      have hv2 : v = v' := Subtype.ext hv
      have hu2 : u = u' := Subtype.ext hu
      subst hv2 hu2
      simp only [SuccSource.prov, Prov.dir.injEq, true_and] at hprov
      have := hinj v u hprov
      subst this
      rfl
    | _ => simp [SuccSource.prov] at hprov
  | copyQuad t h π =>
    cases s' with
    | copyQuad t' h' π' =>
      simp only [SuccSource.prov, Prov.quad.injEq, true_and] at hprov
      have hh : h = h' := (StagePath.length_provList π).symm.trans
        ((congrArg List.length hprov).trans (StagePath.length_provList π'))
      subst hh
      have hπ := StagePath.eq_of_provList hinj π π' hprov
      subst hπ
      have h1 : 1 ≤ h := hs.2.2
      simp only [SuccSource.srcComp, SuccSource.oldSrc, SuccSource.word] at hsrc
      obtain ⟨-, ht⟩ := succComp_inj hm (hpathsrc π h1) (hpathsrc π h1) hsrc
      subst ht
      rfl
    | _ => simp [SuccSource.prov] at hprov
  | letterDiag t u =>
    cases s' with
    | letterDiag t' u' =>
      simp only [SuccSource.srcComp, SuccSource.oldSrc, SuccSource.word] at hsrc
      obtain ⟨hu, ht⟩ := succComp_inj hm (hold _ u.2) (hold _ u'.2) hsrc
      subst ht
      have hu2 : u = u' := Subtype.ext hu
      subst hu2
      rfl
    | _ => simp [SuccSource.prov] at hprov
  | letterMean t n h π =>
    cases s' with
    | letterMean t' n' h' π' =>
      simp only [SuccSource.prov, Prov.letter.injEq, WordLetter.mean.injEq, true_and] at hprov
      obtain ⟨⟨hn, hh⟩, hl⟩ := hprov
      subst hn hh
      have hπ := StagePath.eq_of_provList hinj π π' hl
      subst hπ
      have h1 : 1 ≤ h := by simpa [SuccSource.Valid] using hs.2.2
      simp only [SuccSource.srcComp, SuccSource.oldSrc, SuccSource.word] at hsrc
      obtain ⟨-, ht⟩ := succComp_inj hm (hpathsrc π h1) (hpathsrc π h1) hsrc
      subst ht
      rfl
    | _ => simp [SuccSource.prov] at hprov
  | letterCov t n h a a' π =>
    cases s' with
    | letterCov t' n' h' b b' π' =>
      simp only [SuccSource.prov, Prov.letter.injEq, WordLetter.covariance.injEq,
        true_and] at hprov
      obtain ⟨⟨hn, hh, ha, ha'⟩, hl⟩ := hprov
      subst hn hh ha ha'
      have hπ := StagePath.eq_of_provList hinj π π' hl
      subst hπ
      have h1 : 1 ≤ h := by simpa [SuccSource.Valid] using hs.2.2
      simp only [SuccSource.srcComp, SuccSource.oldSrc, SuccSource.word] at hsrc
      obtain ⟨-, ht⟩ := succComp_inj hm (hpathsrc π h1) (hpathsrc π h1) hsrc
      subst ht
      rfl
    | _ => simp [SuccSource.prov] at hprov

end AVRegularity.Uniqueness
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Uniqueness

/-! The Hilbert curve of the difference of two cell solutions on a window.

Two public cell solutions with the same sources on `[a, b]`, a measurable metric `G(t)` that is
elliptic and bounded on the window and a drift `v` that is merely bounded on the window, differ by
a weak Hilbert curve. Its time derivative is the dual derivative of the unit-metric drift-free
equation with the scalar source `-v·∇E` and the flux `(G - 1)∇E`, of the difference `E`; the drift
is never required to be measurable: its product with `∇E` is measurable at almost every time by the
integrability clause of the weak identity tested against the constant function. -/

/-- Window bounds: ellipticity, bounded entries, and a bounded drift, on `[a, b]`. -/
structure WindowData (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (a b lo A Mv : ℝ) :
    Prop where
  lo_pos : 0 < lo
  coer : ∀ t ∈ Icc a b, ∀ ξ : Fin 2 → ℝ, lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j
  ent : ∀ t ∈ Icc a b, ∀ i j, |G t i j| ≤ A
  vb : ∀ t ∈ Icc a b, ∀ z k, |v t z k| ≤ Mv

/-- The difference of two raw jets. -/
def jetDiff (D D' : ℝ → RawJet2 1 ℂ) : ℝ → RawJet2 1 ℂ := fun r a x => D r a x - D' r a x

/-- The drift source of the difference. -/
def srcFun (v : ℝ → Vec 2 → Vec 2) (D D' : ℝ → RawJet2 1 ℂ) : ℝ → Vec 2 → ℂ :=
  fun r => driftSrc v (cellGradComp (jetDiff D D' r)) r

/-- The metric flux of the difference. -/
def fluxFun (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (D D' : ℝ → RawJet2 1 ℂ) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun r => metricFlux G (cellGradComp (jetDiff D D' r)) r

/-- The Riesz derivative of the difference through the unit-metric proxy equation. -/
def gcurve (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (D D' : ℝ → RawJet2 1 ℂ)
    (r : ℝ) : TorusHk 1 ℂ :=
  cellDualDerivative proxyC proxy_metric 0 proxy_vmeas proxy_vbound r
    (cellH1Slice D r - cellH1Slice D' r) (cellSourceSlice (srcFun v D D') r)
    (fun j => cellSourceSlice (fun r x => fluxFun G D D' r x j) r)

theorem psiOne_value_ae :
    (cellHilbertTest cellH1One).jet (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => (1 : ℂ) := by
  have h := cellRawTest_value_ae (cellHilbertTest cellH1One)
  rw [cellHilbertTest_inverse, cellH1One_value] at h
  filter_upwards [h, cellConstantCLM_ae 1] with x hx hc
  rw [hc] at hx
  have := congrArg star hx
  simpa using this.symm

theorem psiOne_deriv_ae (j : Fin 2) :
    (cellHilbertTest cellH1One).jet ⟨⟨1, by decide⟩, fun _ => j⟩ =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => (0 : ℂ) := by
  have h := cellRawTest_derivative_ae (cellHilbertTest cellH1One) j
  rw [cellHilbertTest_inverse, cellH1One_derivative] at h
  filter_upwards [h, Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := volume.restrict AVenhance.unitCube)] with x hx hz
  rw [hz] at hx
  have := congrArg star hx
  simpa using this.symm

/-- The weak equation of the difference as an identity for the Riesz derivative. -/
theorem key_identity (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D D' : ℝ → RawJet2 1 ℂ) (r : ℝ)
    (hD : ∀ a, (((cellH1Slice D r - cellH1Slice D' r).val a : Vec 2 → ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] jetDiff D D' r a)
    (hS : MemLp (srcFun v D D' r) 2 (volume.restrict AVenhance.unitCube))
    (hF : ∀ j, MemLp (fun x => fluxFun G D D' r x j) 2 (volume.restrict AVenhance.unitCube))
    (ψ : TorusHkFunction 1 ℂ) :
    Integrable (fun x => cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
      (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x) (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
      (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x) =
      cellDualComplexPair (gcurve G v D D' r) (cellRawTest ψ) := by
  have e : (fun x => cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
      (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x) =
      fun x => cellLiteralRHS proxyC r (jetDiff D D' r (valueIndex2 1))
        (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
        (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (srcFun v D D' r) (fluxFun G D D' r) x := by
    funext x
    exact rhs_true_eq_proxy G v r _ _ _ _ x
  rw [e]
  exact cellRawSpatial_equation proxyC proxy_metric 0 proxy_vmeas proxy_vbound r
    (cellH1Slice D r - cellH1Slice D' r) (jetDiff D D' r) hD ψ
    (cellSourceSlice (srcFun v D D') r)
    (fun j => cellSourceSlice (fun r x => fluxFun G D D' r x j) r)
    (srcFun v D D' r) (fluxFun G D D' r) (cellSourceSlice_ae _ r hS)
    (fun j => cellSourceSlice_ae _ r (hF j))


section Solutions

variable {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {a b lo A Mv : ℝ}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {D D' : ℝ → RawJet2 1 ℂ}

/-- The identity for the difference of two solutions with a common source. -/
theorem diff_identity (h : IsCellSolution (Icc a b) (trueC G v) src F D)
    (h' : IsCellSolution (Icc a b) (trueC G v) src F D') {s : ℝ} (hs : s ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc a b) (hst : s ≤ t) (ψ : TorusHkFunction 1 ℂ) :
    Integrable (fun x => (cellValue D t x - cellValue D' t x) * ψ.jet (valueIndex2 1) x)
      (volume.restrict AVenhance.unitCube) ∧
    Integrable (fun x => (cellValue D s x - cellValue D' s x) * ψ.jet (valueIndex2 1) x)
      (volume.restrict AVenhance.unitCube) ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (fun x => cellLiteralRHS (trueC G v) r
      (jetDiff D D' r (valueIndex2 1)) (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x) (volume.restrict AVenhance.unitCube)) ∧
    Integrable (fun r => ∫ x in AVenhance.unitCube, cellLiteralRHS (trueC G v) r
      (jetDiff D D' r (valueIndex2 1)) (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x) (volume.restrict (Ioc s t)) ∧
    (∫ x in AVenhance.unitCube, (cellValue D t x - cellValue D' t x) * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, (cellValue D s x - cellValue D' s x) * ψ.jet (valueIndex2 1) x) =
      ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, cellLiteralRHS (trueC G v) r
        (jetDiff D D' r (valueIndex2 1)) (cellGradComp (jetDiff D D' r))
        (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x := by
  exact cellWeakIdentity_sub_same_source (trueC G v) s t _ _ _ _ _ _ _ _ _ _ src F
    (h.2.2.2.2.2.2 s hs t ht hst ψ) (h'.2.2.2.2.2.2 s hs t ht hst ψ)

/-- A time at which the sections of the difference are well behaved. -/
structure Good (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D D' : ℝ → RawJet2 1 ℂ) (a b r : ℝ) : Prop where
  mem : r ∈ Icc a b
  sl : ∀ j, ((cellH1Slice D r).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D r j
  sl' : ∀ j, ((cellH1Slice D' r).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D' r j
  src : MemLp (srcFun v D D' r) 2 (volume.restrict AVenhance.unitCube)
  flux : ∀ j, MemLp (fun x => fluxFun G D D' r x j) 2 (volume.restrict AVenhance.unitCube)

theorem Good.hE {r : ℝ} (hr : Good G v D D' a b r) (j : JetIndex2 1) :
    (((cellH1Slice D r - cellH1Slice D' r).val j : Vec 2 → ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] jetDiff D D' r j :=
  (Lp.coeFn_sub _ _).trans ((hr.sl j).sub (hr.sl' j))

theorem norm_src_le (v : ℝ → Vec 2 → Vec 2) (du : Fin 2 → Vec 2 → ℂ) (r : ℝ) (Mv : ℝ)
    (hv : ∀ z k, |v r z k| ≤ Mv) (x : Vec 2) :
    ‖driftSrc v du r x‖ ≤ Mv * (‖du 0 x‖ + ‖du 1 x‖) := by
  unfold driftSrc
  rw [norm_neg]
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_two, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 := norm_nonneg (du 0 x)
  have h1 := norm_nonneg (du 1 x)
  nlinarith [mul_le_mul_of_nonneg_right (hv x 0) h0, mul_le_mul_of_nonneg_right (hv x 1) h1]

theorem norm_flux_le (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (du : Fin 2 → Vec 2 → ℂ) (r A : ℝ)
    (hA : ∀ i j, |G r i j| ≤ A) (x : Vec 2) (j : Fin 2) :
    ‖metricFlux G du r x j‖ ≤ (A + 1) * (‖du 0 x‖ + ‖du 1 x‖) := by
  have hc : ∀ i, |G r i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ A + 1 := by
    intro i
    have h1 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    calc _ ≤ |G r i j| + |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := abs_sub _ _
      _ ≤ A + 1 := add_le_add (hA i j) h1
  have e : metricFlux G du r x j =
      ∑ i : Fin 2, (((G r i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)) * du i x := rfl
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_two, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 := norm_nonneg (du 0 x)
  have h1 := norm_nonneg (du 1 x)
  nlinarith [mul_le_mul_of_nonneg_right (hc 0) h0, mul_le_mul_of_nonneg_right (hc 1) h1]

theorem ae_good (hab : a ≤ b) (hW : WindowData G v a b lo A Mv)
    (h : IsCellSolution (Icc a b) (trueC G v) src F D)
    (h' : IsCellSolution (Icc a b) (trueC G v) src F D') :
    ∀ᵐ r ∂volume.restrict (Icc a b), Good G v D D' a b r := by
  have hψ1 := (diff_identity h h' (s := a) ⟨le_rfl, hab⟩ (t := b) ⟨hab, le_rfl⟩ hab
    (cellHilbertTest cellH1One)).2.2.1
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hψ1
  filter_upwards [cellSolution_slice_ae h, cellSolution_slice_ae h', ae_restrict_mem measurableSet_Icc,
    hψ1] with r hr hr' hrI hint
  have hE : ∀ j, (((cellH1Slice D r - cellH1Slice D' r).val j : Vec 2 → ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] jetDiff D D' r j :=
    fun j => (Lp.coeFn_sub _ _).trans ((hr j).sub (hr' j))
  have hL2 : ∀ j, MemLp (jetDiff D D' r j) 2 (volume.restrict AVenhance.unitCube) :=
    fun j => (Lp.memLp ((cellH1Slice D r - cellH1Slice D' r).val j)).ae_eq (hE j)
  have hdu : ∀ k, MemLp (cellGradComp (jetDiff D D' r) k) 2 (volume.restrict AVenhance.unitCube) :=
    fun k => hL2 ⟨⟨1, by decide⟩, fun _ => k⟩
  refine ⟨hrI, hr, hr', ?_, ?_⟩
  · have hmeas : AEStronglyMeasurable (srcFun v D D' r) (volume.restrict AVenhance.unitCube) := by
      refine hint.aestronglyMeasurable.congr ?_
      filter_upwards [psiOne_value_ae, psiOne_deriv_ae 0, psiOne_deriv_ae 1] with x hv h0 h1
      simp only [cellLiteralRHS, trueC, srcFun, driftSrc, Fin.sum_univ_two, hv, h0, h1]
      simp
    have hg : MemLp (fun x => Mv * (‖cellGradComp (jetDiff D D' r) 0 x‖ +
        ‖cellGradComp (jetDiff D D' r) 1 x‖)) 2 (volume.restrict AVenhance.unitCube) :=
      ((hdu 0).norm.add (hdu 1).norm).const_mul Mv
    refine hg.of_le hmeas (Filter.Eventually.of_forall (fun x => ?_))
    have hMv : 0 ≤ Mv := (abs_nonneg _).trans (hW.vb r hrI 0 0)
    have := norm_src_le v (cellGradComp (jetDiff D D' r)) r Mv (hW.vb r hrI) x
    refine this.trans (le_of_eq ?_)
    rw [Real.norm_of_nonneg (by positivity)]
  · intro j
    have hmeas : AEStronglyMeasurable (fun x => fluxFun G D D' r x j)
        (volume.restrict AVenhance.unitCube) := by
      unfold fluxFun metricFlux
      simp only [Fin.sum_univ_two]
      exact ((aestronglyMeasurable_const.mul (hdu 0).aestronglyMeasurable).add
        (aestronglyMeasurable_const.mul (hdu 1).aestronglyMeasurable))
    have hg : MemLp (fun x => (A + 1) * (‖cellGradComp (jetDiff D D' r) 0 x‖ +
        ‖cellGradComp (jetDiff D D' r) 1 x‖)) 2 (volume.restrict AVenhance.unitCube) :=
      ((hdu 0).norm.add (hdu 1).norm).const_mul (A + 1)
    refine hg.of_le hmeas (Filter.Eventually.of_forall (fun x => ?_))
    have hA : 0 ≤ A := (abs_nonneg _).trans (hW.ent r hrI 0 0)
    have := norm_flux_le G (cellGradComp (jetDiff D D' r)) r A (hW.ent r hrI) x j
    refine this.trans (le_of_eq ?_)
    rw [Real.norm_of_nonneg (by positivity)]

end Solutions

end AVRegularity.Uniqueness
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Uniqueness

/-! Uniqueness of cell solutions on a window with a merely bounded drift and a bounded elliptic
metric: the Gårding estimate and the weak Hilbert curve of the difference. -/

/-- The `L²` class of a function bounded by two `L²` classes has a bounded norm. -/
theorem norm_class_le (f : Vec 2 → ℂ) (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (q : Fin 2 → ComplexCellL2) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ‖f x‖ ≤ c * (‖q 0 x‖ + ‖q 1 x‖)) :
    ‖hf.toLp f‖ ≤ 2 * c * (‖q 0‖ + ‖q 1‖) := by
  have h0 := integrable_normSq_of_memLp (Lp.memLp (q 0))
  have h1 := integrable_normSq_of_memLp (Lp.memLp (q 1))
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict AVenhance.unitCube) :=
    integrable_normSq_of_memLp hf
  have hsq : ‖hf.toLp f‖ ^ 2 = ∫ x in AVenhance.unitCube, ‖f x‖ ^ 2 := by
    rw [← cellL2_norm_sq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hle : (∫ x in AVenhance.unitCube, ‖f x‖ ^ 2) ≤
      ∫ x in AVenhance.unitCube, 2 * c ^ 2 * (‖q 0 x‖ ^ 2 + ‖q 1 x‖ ^ 2) := by
    refine integral_mono_ae hint ((h0.add h1).const_mul _) ?_
    filter_upwards [h] with x hx
    have hn := norm_nonneg (f x)
    have a0 := norm_nonneg (q 0 x)
    have a1 := norm_nonneg (q 1 x)
    have : ‖f x‖ ^ 2 ≤ (c * (‖q 0 x‖ + ‖q 1 x‖)) ^ 2 := by
      exact pow_le_pow_left₀ hn hx 2
    nlinarith [sq_nonneg (‖q 0 x‖ - ‖q 1 x‖), sq_nonneg c]
  have hrhs : (∫ x in AVenhance.unitCube, 2 * c ^ 2 * (‖q 0 x‖ ^ 2 + ‖q 1 x‖ ^ 2)) =
      2 * c ^ 2 * (‖q 0‖ ^ 2 + ‖q 1‖ ^ 2) := by
    rw [integral_const_mul, integral_add h0 h1, cellL2_norm_sq_integral, cellL2_norm_sq_integral]
  have hb : 0 ≤ 2 * c * (‖q 0‖ + ‖q 1‖) := by positivity
  have a0 := norm_nonneg (q 0)
  have a1 := norm_nonneg (q 1)
  have h2 : 2 * c ^ 2 * (‖q 0‖ ^ 2 + ‖q 1‖ ^ 2) ≤
      (2 * c * (‖q 0‖ + ‖q 1‖)) * (2 * c * (‖q 0‖ + ‖q 1‖)) := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg ‖q 0‖), mul_nonneg (sq_nonneg c) (sq_nonneg ‖q 1‖),
      mul_nonneg (sq_nonneg c) (mul_nonneg a0 a1)]
  by_contra hcon
  have hcon' : 2 * c * (‖q 0‖ + ‖q 1‖) < ‖hf.toLp f‖ := not_le.mp hcon
  have := mul_self_lt_mul_self hb hcon'
  nlinarith [hsq, hle, hrhs]


section Curve

variable {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {a b lo A Mv : ℝ}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {D D' : ℝ → RawJet2 1 ℂ}

/-- A linear bound of the Riesz derivative at a good time. -/
theorem exists_gcurve_bound (A Mv : ℝ) (hA : 0 ≤ A) (hMv : 0 ≤ Mv) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
      (D D' : ℝ → RawJet2 1 ℂ) (a b lo r : ℝ), WindowData G v a b lo A Mv →
      Good G v D D' a b r →
      ‖gcurve G v D D' r‖ ≤ K * ‖cellH1Slice D r - cellH1Slice D' r‖ := by
  obtain ⟨M0, hM0, hMb⟩ := cellGeneratorForm_uniform_norm_bound proxyC proxy_metric 0 0
    proxy_vmeas proxy_vbound (fun t => by simp [proxyC])
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let Sh : Fin 2 → ℝ := fun j => ‖cellShiftedDerivativeCLM (fun i => star (proxyC.θ i)) j‖
  let Dc : Fin 2 → ℝ := fun k => ‖cellDerivativeCLM k‖
  refine ⟨M0 + J * (2 * Mv * (Dc 0 + Dc 1)) + (Sh 0 + Sh 1) * (2 * (A + 1) * (Dc 0 + Dc 1)),
    by positivity, ?_⟩
  intro G v D D' a b lo r hW hr
  set s := cellH1Slice D r - cellH1Slice D' r with hs
  have hq : ∀ k, ‖cellDerivativeCLM k s‖ ≤ Dc k * ‖s‖ := fun k =>
    (cellDerivativeCLM k).le_opNorm s
  have hqa : ∀ k : Fin 2, ((cellDerivativeCLM k s : ComplexCellL2) : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] cellGradComp (jetDiff D D' r) k :=
    fun k => hr.hE ⟨⟨1, by decide⟩, fun _ => k⟩
  have hS : ‖cellSourceSlice (srcFun v D D') r‖ ≤ 2 * Mv * ((Dc 0 + Dc 1) * ‖s‖) := by
    unfold cellSourceSlice
    rw [dite_eq_left hr.src]
    refine (norm_class_le _ hr.src (fun k => cellDerivativeCLM k s) Mv hMv ?_).trans ?_
    · filter_upwards [hqa 0, hqa 1] with x h0 h1
      have := norm_src_le v (cellGradComp (jetDiff D D' r)) r Mv (hW.vb r hr.mem) x
      simpa only [srcFun, h0, h1] using this
    · have := add_le_add (hq 0) (hq 1)
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * Mv)]
  have hF : ∀ j, ‖cellSourceSlice (fun r x => fluxFun G D D' r x j) r‖ ≤
      2 * (A + 1) * ((Dc 0 + Dc 1) * ‖s‖) := by
    intro j
    unfold cellSourceSlice
    rw [dite_eq_left (hr.flux j)]
    refine (norm_class_le _ (hr.flux j) (fun k => cellDerivativeCLM k s) (A + 1) (by positivity) ?_).trans ?_
    · filter_upwards [hqa 0, hqa 1] with x h0 h1
      have := norm_flux_le G (cellGradComp (jetDiff D D' r)) r A (hW.ent r hr.mem) x j
      simpa only [fluxFun, h0, h1] using this
    · have := add_le_add (hq 0) (hq 1)
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * (A + 1))]
  have hn := cellDualDerivative_norm_le proxyC proxy_metric 0 proxy_vmeas proxy_vbound r s
    (cellSourceSlice (srcFun v D D') r)
    (fun j => cellSourceSlice (fun r x => fluxFun G D D' r x j) r)
  have hform := hMb r s
  unfold gcurve
  refine hn.trans ?_
  simp only [Fin.sum_univ_two]
  have hs0 := norm_nonneg s
  have hsh0 : 0 ≤ Sh 0 := by simp only [Sh]; positivity
  have hsh1 : 0 ≤ Sh 1 := by simp only [Sh]; positivity
  have hJ : 0 ≤ J := by simp only [J]; positivity
  have e0 := mul_le_mul_of_nonneg_left (hF 0) hsh0
  have e1 := mul_le_mul_of_nonneg_left (hF 1) hsh1
  have eS := mul_le_mul_of_nonneg_left hS hJ
  change ‖cellGeneratorForm proxyC proxy_metric 0 proxy_vmeas proxy_vbound r s‖ +
    J * ‖cellSourceSlice (srcFun v D D') r‖ +
    (Sh 0 * ‖cellSourceSlice (fun r x => fluxFun G D D' r x 0) r‖ +
      Sh 1 * ‖cellSourceSlice (fun r x => fluxFun G D D' r x 1) r‖) ≤ _
  nlinarith [hform, e0, e1, eS]

/-- The Riesz derivative is square integrable on the window. -/
theorem memLp_gcurve (hab : a ≤ b) (hW : WindowData G v a b lo A Mv)
    (h : IsCellSolution (Icc a b) (trueC G v) src F D)
    (h' : IsCellSolution (Icc a b) (trueC G v) src F D') :
    MemLp (gcurve G v D D') 2 (volume.restrict (Icc a b)) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hW.ent a ⟨le_rfl, hab⟩ 0 0)
  have hMv : 0 ≤ Mv := (abs_nonneg _).trans (hW.vb a ⟨le_rfl, hab⟩ 0 0)
  obtain ⟨K, hK, hKb⟩ := exists_gcurve_bound A Mv hA hMv
  have hstate : MemLp (fun t => cellH1Slice D t - cellH1Slice D' t) 2
      (volume.restrict (Icc a b)) :=
    (cellSolution_slice_memLp hab h).sub (cellSolution_slice_memLp hab h')
  have hmeas : AEStronglyMeasurable (gcurve G v D D') (volume.restrict (Icc a b)) := by
    apply cellH1_aestronglyMeasurable_of_pairings
    intro z
    have hψ := (diff_identity h h' (s := a) ⟨le_rfl, hab⟩ (t := b) ⟨hab, le_rfl⟩ hab
      (cellHilbertTest z)).2.2.2.1
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hψ
    have hm : AEStronglyMeasurable (fun r => (∫ x in AVenhance.unitCube, cellLiteralRHS (trueC G v) r
        (jetDiff D D' r (valueIndex2 1)) (cellGradComp (jetDiff D D' r))
        ((cellHilbertTest z).jet (valueIndex2 1))
        (fun j => (cellHilbertTest z).jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x).re)
        (volume.restrict (Icc a b)) :=
      Complex.continuous_re.comp_aestronglyMeasurable hψ.aestronglyMeasurable
    refine hm.congr ?_
    filter_upwards [ae_good hab hW h h'] with r hr
    have := (key_identity G v D D' r hr.hE hr.src hr.flux (cellHilbertTest z)).2
    rw [cellHilbertTest_inverse] at this
    rw [this, cellDualComplexPair_re, real_inner_comm]
  refine MemLp.of_le (hstate.norm.const_smul K) hmeas ?_
  filter_upwards [ae_good hab hW h h'] with r hr
  have := hKb G v D D' a b lo r hW hr
  refine this.trans (le_of_eq ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK, abs_norm]

/-- Gårding inequality for the Riesz derivative at a good time. -/
theorem good_growth (hW : WindowData G v a b lo A Mv) {r : ℝ} (hr : Good G v D D' a b r) :
    2 * inner ℝ (gcurve G v D D' r) (cellH1Slice D r - cellH1Slice D' r) ≤
      (2 * Mv ^ 2 / lo) * ‖torusHkValueCLM (cellH1Slice D r - cellH1Slice D' r)‖ ^ 2 := by
  set z := cellH1Slice D r - cellH1Slice D' r with hz
  have hk := key_identity G v D D' r hr.hE hr.src hr.flux (cellHilbertTest z)
  rw [cellHilbertTest_inverse] at hk
  have hre : inner ℝ (gcurve G v D D' r) z =
      (∫ x in AVenhance.unitCube, cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
        (cellGradComp (jetDiff D D' r)) ((cellHilbertTest z).jet (valueIndex2 1))
        (fun j => (cellHilbertTest z).jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x).re := by
    rw [hk.2, cellDualComplexPair_re]
  have hjet : ∀ j : JetIndex2 1, (cellHilbertTest z).jet j =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => star (jetDiff D D' r j x) := by
    intro j
    have h1 := cellRawTest_jet_ae (cellHilbertTest z) j
    rw [cellHilbertTest_inverse] at h1
    filter_upwards [h1, hr.hE j] with x hx hx'
    have e : (cellHilbertTest z).jet j x = star (jetDiff D D' r j x) := by
      rw [← hx', hx, star_star]
    exact e
  have hL2 : MemLp (jetDiff D D' r (valueIndex2 1)) 2 (volume.restrict AVenhance.unitCube) :=
    (Lp.memLp ((cellH1Slice D r - cellH1Slice D' r).val (valueIndex2 1))).ae_eq
      (hr.hE (valueIndex2 1))
  have hlo : 0 < lo := hW.lo_pos
  have hpt : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      (cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
        (cellGradComp (jetDiff D D' r)) ((cellHilbertTest z).jet (valueIndex2 1))
        (fun j => (cellHilbertTest z).jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x).re ≤
      (Mv ^ 2 / lo) * ‖jetDiff D D' r (valueIndex2 1) x‖ ^ 2 := by
    filter_upwards [hjet (valueIndex2 1), hjet ⟨⟨1, by decide⟩, fun _ => 0⟩,
      hjet ⟨⟨1, by decide⟩, fun _ => 1⟩] with x hv0 hd0 hd1
    have hgp := garding_pointwise (G r) lo Mv hlo (hW.coer r hr.mem) (v r x)
      (hW.vb r hr.mem x) (jetDiff D D' r (valueIndex2 1) x)
      (fun j => cellGradComp (jetDiff D D' r) j x)
    refine le_trans (le_of_eq ?_) hgp
    simp only [cellLiteralRHS, trueC, Fin.sum_univ_two, hv0, hd0, hd1] at hgp ⊢
    simp
    rfl
  have hint0 := hk.1.re
  have hint1 : Integrable (fun x => (Mv ^ 2 / lo) * ‖jetDiff D D' r (valueIndex2 1) x‖ ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    (integrable_normSq_of_memLp hL2).const_mul _
  have hle := integral_mono_ae hint0 hint1 hpt
  have hval : (∫ x in AVenhance.unitCube, ‖jetDiff D D' r (valueIndex2 1) x‖ ^ 2) =
      ‖torusHkValueCLM z‖ ^ 2 := by
    rw [← cellL2_norm_sq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hr.hE (valueIndex2 1)] with x hx
    rw [← hx]
    rfl
  have hmap := Complex.reCLM.integral_comp_comm hk.1
  change (∫ x in AVenhance.unitCube, (cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
      (cellGradComp (jetDiff D D' r)) ((cellHilbertTest z).jet (valueIndex2 1))
      (fun j => (cellHilbertTest z).jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x).re) =
    (∫ x in AVenhance.unitCube, cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
      (cellGradComp (jetDiff D D' r)) ((cellHilbertTest z).jet (valueIndex2 1))
      (fun j => (cellHilbertTest z).jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x).re at hmap
  have hc : (∫ x in AVenhance.unitCube, (Mv ^ 2 / lo) * ‖jetDiff D D' r (valueIndex2 1) x‖ ^ 2) =
      (Mv ^ 2 / lo) * ‖torusHkValueCLM z‖ ^ 2 := by
    rw [integral_const_mul, hval]
  rw [hre, ← hmap]
  calc 2 * ∫ x in AVenhance.unitCube, (cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
        (cellGradComp (jetDiff D D' r)) ((cellHilbertTest z).jet (valueIndex2 1))
        (fun j => (cellHilbertTest z).jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0 x).re
      ≤ 2 * ((Mv ^ 2 / lo) * ‖torusHkValueCLM z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hle.trans_eq hc) (by norm_num)
    _ = (2 * Mv ^ 2 / lo) * ‖torusHkValueCLM z‖ ^ 2 := by ring

/-- The fixed-test increments of the difference are integrals of the Riesz derivative. -/
theorem curve_increment (hab : a ≤ b) (hW : WindowData G v a b lo A Mv)
    (h : IsCellSolution (Icc a b) (trueC G v) src F D)
    (h' : IsCellSolution (Icc a b) (trueC G v) src F D')
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) (z : TorusHk 1 ℂ) :
    inner ℝ (cellRawTrace D t - cellRawTrace D' t) (torusHkValueCLM z) -
      inner ℝ (cellRawTrace D s - cellRawTrace D' s) (torusHkValueCLM z) =
        ∫ r in s..t, inner ℝ (gcurve G v D D' r) z := by
  let ψ := cellHilbertTest z
  let R := fun r => cellLiteralRHS (trueC G v) r (jetDiff D D' r (valueIndex2 1))
    (cellGradComp (jetDiff D D' r)) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0
  obtain ⟨-, -, -, hRint, hid⟩ := diff_identity h h' hs ht hst ψ
  have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
  have hgood := (ae_good hab hW h h').filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have he : (fun r => ∫ x in AVenhance.unitCube, R r x) =ᵐ[volume.restrict (Ioc s t)]
      fun r => cellDualComplexPair (gcurve G v D D' r) z := by
    filter_upwards [hgood] with r hr
    have := (key_identity G v D D' r hr.hE hr.src hr.flux ψ).2
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at this
    exact this
  have htrace (r : ℝ) (hr : r ∈ Icc a b) :
      ((cellRawTrace D r - cellRawTrace D' r : ComplexCellL2) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x => cellValue D r x - cellValue D' r x :=
    (Lp.coeFn_sub _ _).trans ((cellRawTrace_ae D r (h.2.2.1 r hr).1).sub
      (cellRawTrace_ae D' r (h'.2.2.1 r hr).1))
  have hp (r : ℝ) (hr : r ∈ Icc a b) := cellRawTest_pairing_integral ψ
    (cellRawTrace D r - cellRawTrace D' r) (fun x => cellValue D r x - cellValue D' r x)
    (htrace r hr)
  have hinc : cellComplexPair (cellRawTrace D t - cellRawTrace D' t) (torusHkValueCLM z) -
      cellComplexPair (cellRawTrace D s - cellRawTrace D' s) (torusHkValueCLM z) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x := by
    have hpt := hp t ht
    have hps := hp s hs
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at hpt hps
    rw [hpt, hps]
    exact hid
  have hre := congrArg Complex.re hinc
  simp only [Complex.sub_re, cellComplexPair_re] at hre
  have hmap := Complex.reCLM.integral_comp_comm hRint
  change (∫ r in Ioc s t, (∫ x in AVenhance.unitCube, R r x).re) =
    (∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x).re at hmap
  rw [← hmap] at hre
  rw [intervalIntegral.integral_of_le hst]
  have hreal : (fun r => (∫ x in AVenhance.unitCube, R r x).re) =ᵐ[
      volume.restrict (Ioc s t)] fun r => inner ℝ (gcurve G v D D' r) z :=
    he.mono (fun r hr => (congrArg Complex.re hr).trans (cellDualComplexPair_re _ _))
  exact hre.trans (integral_congr_ae hreal)

/-- Two cell solutions on a window with the same source and the same initial value agree. -/
theorem cellSolution_pair_trace_eq (hab : a ≤ b) (hW : WindowData G v a b lo A Mv)
    (h : IsCellSolution (Icc a b) (trueC G v) src F D)
    (h' : IsCellSolution (Icc a b) (trueC G v) src F D')
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' a) :
    ∀ t ∈ Icc a b, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t := by
  have hMv : 0 ≤ Mv := (abs_nonneg _).trans (hW.vb a ⟨le_rfl, hab⟩ 0 0)
  have hcurve : CellWeakHilbertCurve a b (fun t => cellRawTrace D t - cellRawTrace D' t)
      (fun t => cellH1Slice D t - cellH1Slice D' t) (gcurve G v D D') := by
    refine ⟨(IsCellSolution.trace_continuous h).sub (IsCellSolution.trace_continuous h'),
      (cellSolution_slice_memLp hab h).sub (cellSolution_slice_memLp hab h'),
      memLp_gcurve hab hW h h', ?_, fun s hs t ht hst z => curve_increment hab hW h h' s hs t ht hst z⟩
    filter_upwards [cellSolution_trace_agrees h, cellSolution_trace_agrees h'] with t ht ht'
    rw [ht, ht', ← map_sub]
  have hi' : cellRawTrace D a - cellRawTrace D' a = 0 := by
    rw [sub_eq_zero]
    exact Lp.ext ((cellRawTrace_ae D a (h.2.2.1 a ⟨le_rfl, hab⟩).1).trans
      (hi.trans (cellRawTrace_ae D' a (h'.2.2.1 a ⟨le_rfl, hab⟩).1).symm))
  have hz := hcurve.eq_zero_of_growth hab hi' (2 * Mv ^ 2 / lo)
    (div_nonneg (by positivity) hW.lo_pos.le) (by
      filter_upwards [ae_good hab hW h h', cellSolution_trace_agrees h,
        cellSolution_trace_agrees h'] with r hr ht ht'
      have hg := good_growth hW hr
      have : cellRawTrace D r - cellRawTrace D' r =
          torusHkValueCLM (cellH1Slice D r - cellH1Slice D' r) := by
        rw [ht, ht', ← map_sub]
      rw [this]
      exact hg)
  intro t ht
  have := sub_eq_zero.mp (hz t ht)
  exact (cellRawTrace_ae D t (h.2.2.1 t ht).1).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) this)).trans
      (cellRawTrace_ae D' t (h'.2.2.1 t ht).1))

end Curve

end AVRegularity.Uniqueness
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.Uniqueness

/-! Uniqueness of the classical finite-past mean-zero cell inverse on a window: two classical
fields that are cell field inverses of sources that agree on the window agree. -/

/-- Continuous periodic functions that agree almost everywhere on the unit cube agree. -/
theorem eq_of_ae_eq_periodic {E : Type*} [NormedAddCommGroup E] {f f' : Vec 2 → E} (hf : Continuous f) (hf' : Continuous f')
    (hp : AVenhance.IsZ2Periodic f) (hp' : AVenhance.IsZ2Periodic f')
    (hae : f =ᵐ[volume.restrict AVenhance.unitCube] f') : f = f' := by
  have hopen : IsOpen AVenhance.unitCube :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have h1 : EqOn f f' AVenhance.unitCube :=
    Measure.eqOn_open_of_ae_eq hae hopen hf.continuousOn hf'.continuousOn
  have h2 : EqOn f f' (closure AVenhance.unitCube) := h1.closure hf hf'
  funext x
  let y : Vec 2 := fun i => Int.fract (x i)
  let n : Fin 2 → ℤ := fun i => ⌊x i⌋
  have hx : x = y + AVenhance.latticeShift n := by
    funext i
    simp only [Pi.add_apply, y, AVenhance.latticeShift, n]
    linarith [Int.fract_add_floor (x i)]
  have hy : y ∈ closure AVenhance.unitCube := by
    unfold AVenhance.unitCube
    rw [closure_pi_set]
    intro i _
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [hx, hp n y, hp' n y]
  exact h2 hy

theorem ae_eq_of_forall_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {μ : Measure (Vec 2)} {f f' : Vec 2 → E}
    (h : ∀ ℓ : E →L[ℝ] ℝ, (fun x => ℓ (f x)) =ᵐ[μ] fun x => ℓ (f' x)) : f =ᵐ[μ] f' := by
  let bs := Module.finBasis ℝ E
  have hall : ∀ᵐ x ∂μ, ∀ i, bs.coord i (f x) = bs.coord i (f' x) := by
    rw [ae_all_iff]
    intro i
    exact h (LinearMap.toContinuousLinearMap (bs.coord i))
  filter_upwards [hall] with x hx
  exact bs.ext_elem (fun i => by simpa using hx i)

theorem periodic_of_forall_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E}
    (h : ∀ ℓ : E →L[ℝ] ℝ, AVenhance.IsZ2Periodic (fun x => ℓ (f x))) :
    AVenhance.IsZ2Periodic f := by
  intro n x
  exact sub_eq_zero.mp (SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
    (fun ℓ => by simp [map_sub, h ℓ n x]))

/-- Two classical cell field inverses with sources agreeing on the window agree on the window. -/
theorem cellField_unique_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ lo A Mv : ℝ} (ht : t₀ ≤ t₁) (hW : WindowData G v t₀ t₁ lo A Mv)
    {g g' c c' : ℝ → Vec 2 → E} (hg : ∀ t ∈ Icc t₀ t₁, ∀ z, g t z = g' t z)
    (hc : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c)
    (hc' : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g' c') :
    ∀ t ∈ Icc t₀ t₁, ∀ z, c t z = c' t z := by
  intro t htI
  have hae : ∀ ℓ : E →L[ℝ] ℝ, (fun x => ℓ (c t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ℓ (c' t x) := by
    intro ℓ
    have h1 : IsCellSolution (Icc t₀ t₁) (trueC G v) (fun t x => ((ℓ (g t x) : ℝ) : ℂ))
        (fun _ _ => 0) (cellJetOfField ℓ c) := (hc.2 ℓ).1
    have h2 : IsCellSolution (Icc t₀ t₁) (trueC G v) (fun t x => ((ℓ (g t x) : ℝ) : ℂ))
        (fun _ _ => 0) (cellJetOfField ℓ c') := by
      refine cellSolution_source_congr_sections (Icc t₀ t₁) (trueC G v)
        (fun t x => ((ℓ (g' t x) : ℝ) : ℂ)) _ (fun _ _ => 0) (fun _ _ => 0) _ ?_ ?_ (hc'.2 ℓ).1
      · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall (fun r hr => ?_))
        exact Filter.EventuallyEq.of_eq (funext (fun x => by rw [hg r hr x]))
      · exact Filter.Eventually.of_forall (fun r => Filter.EventuallyEq.rfl)
    have hi : cellValue (cellJetOfField ℓ c) t₀ =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (cellJetOfField ℓ c') t₀ := by
      have a1 := (hc.2 ℓ).2.2.1
      have a2 := (hc'.2 ℓ).2.2.1
      exact a1.trans a2.symm
    have := cellSolution_pair_trace_eq ht hW h1 h2 hi t htI
    filter_upwards [this] with x hx
    have e : ∀ (cc : ℝ → Vec 2 → E), cellValue (cellJetOfField ℓ cc) t x = ((ℓ (cc t x) : ℝ) : ℂ) := by
      intro cc
      simp [cellValue, cellJetOfField, valueIndex2, valueIndex]
    rw [e, e] at hx
    exact_mod_cast hx
  have hae' : c t =ᵐ[volume.restrict AVenhance.unitCube] c' t := ae_eq_of_forall_dual hae
  have hper : ∀ (gg cc : ℝ → Vec 2 → E),
      (∀ ℓ : E →L[ℝ] ℝ, IsCellSolution (Icc t₀ t₁) (trueC G v) (fun t x => ((ℓ (gg t x) : ℝ) : ℂ))
        (fun _ _ => 0) (cellJetOfField ℓ cc)) →
      AVenhance.IsZ2Periodic (cc t) := by
    intro gg cc hcc
    apply periodic_of_forall_dual
    intro ℓ n x
    have := (hcc ℓ).2.2.1 t htI
    have hp := this.2 n x
    have e : ∀ y, cellValue (cellJetOfField ℓ cc) t y = ((ℓ (cc t y) : ℝ) : ℂ) := by
      intro y
      simp [cellValue, cellJetOfField, valueIndex2, valueIndex]
    rw [e, e] at hp
    exact_mod_cast hp
  have hpc := hper g c (fun ℓ => (hc.2 ℓ).1)
  have hpc' := hper g' c' (fun ℓ => (hc'.2 ℓ).1)
  have := eq_of_ae_eq_periodic (hc.1 t htI).continuous (hc'.1 t htI).continuous hpc hpc' hae'
  intro z
  exact congrFun this z

end AVRegularity.Uniqueness
end
