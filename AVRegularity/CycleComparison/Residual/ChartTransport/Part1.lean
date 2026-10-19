-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import Mathlib.Algebra.Order.Chebyshev
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.ChartTransport

/-! Chart transport, part (1): the pointwise real bounds for the Piola flux `(DΦ R) ∘ Ψ` and the
scalar `q ∘ Ψ`, in terms of the weighted words of `R` and `q` at `Ψ x`. -/

/-- Cauchy–Schwarz over the words of all lengths `< n`. -/
theorem sq_sum_words_le (n : ℕ) (f : (j : ℕ) → DerivativeWord2 j → ℝ) :
    (∑ j ∈ Finset.range n, ∑ w : DerivativeWord2 j, f j w) ^ 2 ≤
      (n * 2 ^ n) * ∑ j ∈ Finset.range n, ∑ w : DerivativeWord2 j, f j w ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
    (f := fun j => ∑ w : DerivativeWord2 j, f j w)
  rw [Finset.card_range] at h1
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun j hj => ?_)
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (DerivativeWord2 j)))
    (f := fun w => f j w)
  rw [card_derivativeWord2] at h2
  have hj : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hj).le
  refine h2.trans ?_
  have : (0 : ℝ) ≤ ∑ w : DerivativeWord2 j, f j w ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  push_cast
  exact mul_le_mul_of_nonneg_right hj this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem flux_const_mono {D : ℝ} (hD : 1 ≤ D) {j r : ℕ} (hj : j ≤ r) :
    2 ^ j * (compConst D j * D) * compConst D j ≤ 2 ^ r * (compConst D r * D) * compConst D r := by
  have h1 : (2 : ℝ) ^ j ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hj
  have h2 := compConst_mono hD hj
  have h3 := compConst_nonneg hD j
  have h4 := compConst_nonneg hD r
  have hD0 : 0 ≤ D := by linarith
  gcongr

/-- Pointwise bound of a word of the Piola flux in terms of the weighted words of `G`. -/
theorem flux_word_bound {Φ Ψ : Vec 2 → Vec 2} {r j : ℕ} (hj : j ≤ r)
    (hΦ : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) Φ) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    {G : Fin 2 → Vec 2 → E} (hG : ∀ l, ContDiff ℝ (r : ℕ∞) (G l)) {D Rχ s : ℝ} (hD : 1 ≤ D)
    (hs : 0 < s) (hsR : s ≤ Rχ) (hJΦ : JetBound Φ (r + 1) D Rχ) (hJΨ : JetBound Ψ r D Rχ)
    (k : Fin 2) (β : DerivativeWord2 j) (x : Vec 2) :
    s ^ j * ‖orderedDerivative β (fun z => ∑ l : Fin 2, jacMatrix Φ (Ψ z) k l • G l (Ψ z)) x‖ ≤
      (2 ^ r * (compConst D r * D) * compConst D r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
          s ^ i * ‖orderedDerivative w (G l) (Ψ x)‖ := by
  have hjr : (j : ℕ∞) ≤ r := by exact_mod_cast hj
  have hΦj : ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) Φ := hΦ.of_le (by exact_mod_cast Nat.succ_le_succ hj)
  have hΨj : ContDiff ℝ (j : ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast hj)
  have hGj : ∀ l, ContDiff ℝ (j : ℕ∞) (G l) := fun l => (hG l).of_le (by exact_mod_cast hj)
  have hPc : ContDiff ℝ (j : ℕ∞) (fun z => ∑ l : Fin 2, jacMatrix Φ (Ψ z) k l • G l (Ψ z)) := by
    refine ContDiff.sum fun l _ => ?_
    have hfd : ContDiff ℝ (j : ℕ∞) (fderiv ℝ Φ) := hΦj.fderiv_right (by simp)
    have : ContDiff ℝ (j : ℕ∞) (fun y => jacMatrix Φ y k l) :=
      (ContinuousLinearMap.contDiff
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
          (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec l)))).comp hfd
    exact (this.comp hΨj).smul ((hGj l).comp hΨj)
  have hb := flux_chart_bound (n := j) hΦj hΨj hGj hD hs hsR
    (fun p hp1 hp y => hJΦ p hp1 (by omega) y) (fun p hp1 hp y => hJΨ p hp1 (by omega) y) k x
  have hw := norm_orderedDerivative_le hPc β x
  have hK := flux_const_mono hD hj
  have hsum : ∑ l : Fin 2, ∑ i ∈ Finset.range (j + 1), s ^ i * ‖iteratedFDeriv ℝ i (G l) (Ψ x)‖ ≤
      ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
        s ^ i * ‖orderedDerivative w (G l) (Ψ x)‖ := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i hi => ?_
    have hir : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have hGi : ∀ l, ContDiff ℝ (i : ℕ∞) (G l) := fun l => (hG l).of_le (by exact_mod_cast hir)
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_sum_words (hGi l) _) (by positivity)
  have hK0 : 0 ≤ 2 ^ j * (compConst D j * D) * compConst D j := by
    have := compConst_nonneg hD j
    have : 0 ≤ D := by linarith
    positivity
  calc s ^ j * ‖orderedDerivative β (fun z => ∑ l : Fin 2, jacMatrix Φ (Ψ z) k l • G l (Ψ z)) x‖
      ≤ s ^ j * ‖iteratedFDeriv ℝ j (fun z => ∑ l : Fin 2, jacMatrix Φ (Ψ z) k l • G l (Ψ z)) x‖ :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ _ := hb
    _ ≤ (2 ^ j * (compConst D j * D) * compConst D j) * ∑ i ∈ Finset.range (j + 1),
        ∑ w : DerivativeWord2 i, ∑ l : Fin 2, s ^ i * ‖orderedDerivative w (G l) (Ψ x)‖ := by
        exact mul_le_mul_of_nonneg_left hsum hK0
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

/-- Pointwise bound of a word of `G ∘ Ψ`. -/
theorem scalar_word_bound {Ψ : Vec 2 → Vec 2} {r j : ℕ} (hj : j ≤ r)
    (hΨ : ContDiff ℝ (r : ℕ∞) Ψ) {G : Vec 2 → E} (hG : ContDiff ℝ (r : ℕ∞) G) {D Rχ s : ℝ}
    (hD : 1 ≤ D) (hs : 0 < s) (hsR : s ≤ Rχ) (hJΨ : JetBound Ψ r D Rχ)
    (β : DerivativeWord2 j) (x : Vec 2) :
    s ^ j * ‖orderedDerivative β (fun z => G (Ψ z)) x‖ ≤
      compConst D r * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          s ^ i * ‖orderedDerivative w G (Ψ x)‖ := by
  have hΨj : ContDiff ℝ (j : ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast hj)
  have hGj : ContDiff ℝ (j : ℕ∞) G := hG.of_le (by exact_mod_cast hj)
  have hc := comp_sum_bound hGj hΨj hD hs hsR (fun p hp1 hp y => hJΨ p hp1 (by omega) y) x
  have hw := norm_orderedDerivative_le (hGj.comp hΨj) β x
  have h1 : s ^ j * ‖iteratedFDeriv ℝ j (G ∘ Ψ) x‖ ≤
      ∑ q ∈ Finset.range (j + 1), s ^ q * ‖iteratedFDeriv ℝ q (G ∘ Ψ) x‖ :=
    Finset.single_le_sum (f := fun q => s ^ q * ‖iteratedFDeriv ℝ q (G ∘ Ψ) x‖)
      (fun _ _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_self j))
  have hsum : ∑ i ∈ Finset.range (j + 1), s ^ i * ‖iteratedFDeriv ℝ i G (Ψ x)‖ ≤
      ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, s ^ i * ‖orderedDerivative w G (Ψ x)‖ := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hir : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have hGi : ContDiff ℝ (i : ℕ∞) G := hG.of_le (by exact_mod_cast hir)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_sum_words hGi _) (by positivity)
  have hK := compConst_mono hD hj
  have hK' := compConst_nonneg hD r
  have hS : 0 ≤ ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
      s ^ i * ‖orderedDerivative w G (Ψ x)‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hcr : compConst D j ≤ compConst D r := compConst_mono hD hj
  calc s ^ j * ‖orderedDerivative β (fun z => G (Ψ z)) x‖
      ≤ s ^ j * ‖iteratedFDeriv ℝ j (G ∘ Ψ) x‖ := mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ compConst D j * ∑ i ∈ Finset.range (j + 1), s ^ i * ‖iteratedFDeriv ℝ i G (Ψ x)‖ :=
        h1.trans hc
    _ ≤ compConst D j * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          s ^ i * ‖orderedDerivative w G (Ψ x)‖ :=
        mul_le_mul_of_nonneg_left hsum (compConst_nonneg hD j)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcr hS

end AVRegularity.ChartTransport
end
end

section
section
@[expose] public section
open Homogenization AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.ChartTransport

/-! Chart transport, part (1): squared pointwise bounds for the components of the Piola flux and of
the scalar, in the form consumed by the residual norm. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem norm_smul_orderedDerivative_apply {i : ℕ} {s : ℝ} (hs : 0 < s) {g : Vec 2 → ∀ i, h i}
    (hg : ContDiff ℝ (i : ℕ∞) g) (w : DerivativeWord2 i) (y : Vec 2) (v : ι) :
    ‖(s ^ i • orderedDerivative w g y) v‖ = s ^ i * ‖orderedDerivative w (fun x => g x v) y‖ := by
  rw [Pi.smul_apply, norm_smul, orderedDerivative_apply w hg v y, Real.norm_of_nonneg
    (pow_nonneg hs.le i)]

/-- The constant of the flux bound. -/
def fluxConst (D : ℝ) (r : ℕ) : ℝ :=
  (2 ^ r * (compConst D r * D) * compConst D r) ^ 2 * ((r + 1) * 2 ^ (r + 1)) * 2

theorem fluxConst_nonneg {D : ℝ} (r : ℕ) : 0 ≤ fluxConst D r := by
  unfold fluxConst; positivity

/-- The constant of the scalar bound. -/
def scalarConst (D : ℝ) (r : ℕ) : ℝ := compConst D r ^ 2 * ((r + 1) * 2 ^ (r + 1))

theorem scalarConst_nonneg {D : ℝ} (r : ℕ) : 0 ≤ scalarConst D r := by
  unfold scalarConst; positivity

theorem flux_sq {Φ Ψ : Vec 2 → Vec 2} {r j : ℕ} (hj : j ≤ r)
    (hΦ : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) Φ) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    {R : Vec 2 → Fin 2 → ∀ i, h i} (hR : ∀ l, ContDiff ℝ (r : ℕ∞) (fun x => R x l)) {D Rχ rs : ℝ}
    (hD : 1 ≤ D) (hs : 0 < rs) (hsR : rs ≤ Rχ) (hJΦ : JetBound Φ (r + 1) D Rχ)
    (hJΨ : JetBound Ψ r D Rχ) (k : Fin 2) (β : DerivativeWord2 j) (x : Vec 2) (v : ι) :
    ‖(rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ ^ 2 ≤
      fluxConst D r * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
        ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) (Ψ x)) v‖ ^ 2 := by
  have hGc : ∀ l, ContDiff ℝ (r : ℕ∞) (fun x => R x l v) := fun l => contDiff_pi.1 (hR l) v
  have hPpi : ContDiff ℝ (j : ℕ∞) (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) := by
    refine contDiff_pi.2 fun v' => ?_
    simp only [Finset.sum_apply, Pi.smul_apply]
    have hΦj : ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) Φ :=
      hΦ.of_le (by exact_mod_cast Nat.succ_le_succ hj)
    have hΨj : ContDiff ℝ (j : ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast hj)
    refine ContDiff.sum fun l _ => ?_
    have hfd : ContDiff ℝ (j : ℕ∞) (fderiv ℝ Φ) := hΦj.fderiv_right (by simp)
    have : ContDiff ℝ (j : ℕ∞) (fun y => jacMatrix Φ y k l) :=
      (ContinuousLinearMap.contDiff
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
          (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec l)))).comp hfd
    exact (this.comp hΨj).smul
      (((contDiff_pi.1 ((hR l).of_le (by exact_mod_cast hj))) v').comp hΨj)
  have hPv : (fun x => (orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v) =
      orderedDerivative β (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l v) := by
    funext y
    rw [orderedDerivative_apply β hPpi v y]
    simp only [Finset.sum_apply, Pi.smul_apply]
  have hb := flux_word_bound hj hΦ hΨ hGc hD hs hsR hJΦ hJΨ k β x
  have hlhs : ‖(rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ =
      rs ^ j * ‖orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l v) x‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pow_nonneg hs.le j), ← hPv]
  have hrhs : ∀ i, i ≤ j → ∀ (w : DerivativeWord2 i) (l : Fin 2),
      ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) (Ψ x)) v‖ =
        rs ^ i * ‖orderedDerivative w (fun x' => R x' l v) (Ψ x)‖ := fun i hi w l =>
    norm_smul_orderedDerivative_apply hs ((hR l).of_le (by exact_mod_cast hi.trans hj)) w _ v
  rw [hlhs]
  set A : (i : ℕ) → DerivativeWord2 i → Fin 2 → ℝ := fun i w l =>
    rs ^ i * ‖orderedDerivative w (fun x' => R x' l v) (Ψ x)‖ with hA
  have hA0 : ∀ i w l, 0 ≤ A i w l := fun i w l => by simp only [hA]; positivity
  have hrhs' : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
        ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) (Ψ x)) v‖ ^ 2 =
      ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2, A i w l ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [hrhs i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) w l]
  rw [hrhs']
  have hb' : rs ^ j * ‖orderedDerivative β
      (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l v) x‖ ≤
      (2 ^ r * (compConst D r * D) * compConst D r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2, A i w l := by
    exact hb
  set T : ℝ := ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2, A i w l with hT
  set Kf : ℝ := 2 ^ r * (compConst D r * D) * compConst D r with hKf
  have h1 : (rs ^ j * ‖orderedDerivative β
      (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l v) x‖) ^ 2 ≤ (Kf * T) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hb' 2
  have h2 := sq_sum_words_le (j + 1) (fun i w => ∑ l : Fin 2, A i w l)
  have h3 : ∀ i (w : DerivativeWord2 i), (∑ l : Fin 2, A i w l) ^ 2 ≤ 2 * ∑ l : Fin 2, A i w l ^ 2 :=
    fun i w => by
      simp only [Fin.sum_univ_two]
      nlinarith [sq_nonneg (A i w 0 - A i w 1)]
  have h4 : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, (∑ l : Fin 2, A i w l) ^ 2 ≤
      2 * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2, A i w l ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => h3 i w
  set Q : ℝ := ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, ∑ l : Fin 2, A i w l ^ 2
    with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by positivity
  have hn : ((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1) ≤ ((r + 1 : ℕ) : ℝ) * 2 ^ (r + 1) := by
    have e1 : ((j + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
    have e2 : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (r + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hj)
    gcongr
  have hKf0 : 0 ≤ Kf ^ 2 := by positivity
  calc _ ≤ (Kf * T) ^ 2 := h1
    _ = Kf ^ 2 * T ^ 2 := by ring
    _ ≤ Kf ^ 2 * (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1) * (2 * Q)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKf0
        refine h2.trans ?_
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ Kf ^ 2 * (((r + 1 : ℕ) : ℝ) * 2 ^ (r + 1) * (2 * Q)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKf0
        exact mul_le_mul_of_nonneg_right hn (by positivity)
    _ = fluxConst D r * Q := by unfold fluxConst; push_cast; ring

theorem scalar_sq {Ψ : Vec 2 → Vec 2} {r j : ℕ} (hj : j ≤ r) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    {q : Vec 2 → ∀ i, h i} (hq : ContDiff ℝ (r : ℕ∞) q) {D Rχ rs : ℝ} (hD : 1 ≤ D)
    (hs : 0 < rs) (hsR : rs ≤ Rχ) (hJΨ : JetBound Ψ r D Rχ) (β : DerivativeWord2 j) (x : Vec 2)
    (v : ι) :
    ‖(rs ^ j • orderedDerivative β (fun x' => q (Ψ x')) x) v‖ ^ 2 ≤
      scalarConst D r * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
        ‖(rs ^ i • orderedDerivative w q (Ψ x)) v‖ ^ 2 := by
  have hGc : ContDiff ℝ (r : ℕ∞) (fun x => q x v) := contDiff_pi.1 hq v
  have hqΨ : ContDiff ℝ (j : ℕ∞) (fun x' => q (Ψ x')) :=
    (hq.of_le (by exact_mod_cast hj)).comp (hΨ.of_le (by exact_mod_cast hj))
  have hlhs : ‖(rs ^ j • orderedDerivative β (fun x' => q (Ψ x')) x) v‖ =
      rs ^ j * ‖orderedDerivative β (fun x' => q (Ψ x') v) x‖ :=
    norm_smul_orderedDerivative_apply hs hqΨ β x v
  have hb := scalar_word_bound hj hΨ hGc hD hs hsR hJΨ β x
  have hrhs : ∀ i, i ≤ j → ∀ (w : DerivativeWord2 i),
      ‖(rs ^ i • orderedDerivative w q (Ψ x)) v‖ =
        rs ^ i * ‖orderedDerivative w (fun x' => q x' v) (Ψ x)‖ := fun i hi w =>
    norm_smul_orderedDerivative_apply hs (hq.of_le (by exact_mod_cast hi.trans hj)) w _ v
  set A : (i : ℕ) → DerivativeWord2 i → ℝ := fun i w =>
    rs ^ i * ‖orderedDerivative w (fun x' => q x' v) (Ψ x)‖ with hA
  have hrhs' : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
        ‖(rs ^ i • orderedDerivative w q (Ψ x)) v‖ ^ 2 =
      ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, A i w ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun w _ => by
      rw [hrhs i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) w]
  rw [hlhs, hrhs']
  have hA0 : ∀ i w, 0 ≤ A i w := fun i w => by simp only [hA]; positivity
  set T : ℝ := ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, A i w with hT
  have h1 : (rs ^ j * ‖orderedDerivative β (fun x' => q (Ψ x') v) x‖) ^ 2 ≤
      (compConst D r * T) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
  have h2 := sq_sum_words_le (j + 1) A
  set Q : ℝ := ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i, A i w ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hn : ((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1) ≤ ((r + 1 : ℕ) : ℝ) * 2 ^ (r + 1) := by
    have e1 : ((j + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
    have e2 : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (r + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hj)
    gcongr
  have hK0 : 0 ≤ compConst D r ^ 2 := by positivity
  calc _ ≤ (compConst D r * T) ^ 2 := h1
    _ = compConst D r ^ 2 * T ^ 2 := by ring
    _ ≤ compConst D r ^ 2 * (((j + 1 : ℕ) : ℝ) * 2 ^ (j + 1) * Q) :=
        mul_le_mul_of_nonneg_left h2 hK0
    _ ≤ compConst D r ^ 2 * (((r + 1 : ℕ) : ℝ) * 2 ^ (r + 1) * Q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn hQ0) hK0
    _ = scalarConst D r * Q := by unfold scalarConst; push_cast; ring

end AVRegularity.ChartTransport
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev MeasureTheory AVenhance
open scoped ENNReal
namespace AVRegularity.ChartTransport

/-! Chart transport: the cell integrals of the factorial densities and their transport by a
volume-preserving chart. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A volume-preserving lattice-equivariant chart with its inverse. -/
structure IsChart (Φ Ψ : Vec 2 → Vec 2) : Prop where
  contΦ : ContDiff ℝ 1 Φ
  contΨ : ContDiff ℝ 1 Ψ
  left : ∀ y, Ψ (Φ y) = y
  right : ∀ x, Φ (Ψ x) = x
  equiv : ∀ (n : Fin 2 → ℤ) y, Φ (y + latticeShift n) = Φ y + latticeShift n
  det : ∀ y, (jacMatrix Φ y).det = 1

theorem IsChart.cell_comp {Φ Ψ : Vec 2 → Vec 2} (h : IsChart Φ Ψ) (g : Vec 2 → ℝ≥0∞)
    (hg : IsZ2Periodic g) : ∫⁻ x in unitCube, g (Φ x) = ∫⁻ x in unitCube, g x :=
  lintegral_cell_comp h.contΦ h.contΨ.continuous h.left h.right h.equiv h.det g hg

theorem IsChart.cell_comp_inv {Φ Ψ : Vec 2 → Vec 2} (h : IsChart Φ Ψ) (g : Vec 2 → ℝ≥0∞)
    (hg : IsZ2Periodic g) : ∫⁻ x in unitCube, g (Ψ x) = ∫⁻ x in unitCube, g x :=
  lintegral_cell_comp_inv h.contΦ h.contΨ h.left h.right h.equiv h.det g hg

/-- `∑_{j ≤ M} ∫_{cell} fdens_j`. -/
noncomputable def fsum (ρ : ℝ) (e M : ℕ) (u : Vec 2 → E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (M + 1), ∫⁻ x in unitCube, ENNReal.ofReal (fdens ρ e j u x)

theorem classicalFactorialSq_eq_fsum (ρ : ℝ) (m : ℕ) {u : Vec 2 → E} (hu : ContDiff ℝ (m : ℕ∞) u) :
    classicalFactorialSq ρ m u = fsum ρ 0 m u := classicalFactorialSq_eq ρ m hu

theorem classicalGradFactorialSq_eq_fsum (ρ : ℝ) (m : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) u) :
    classicalGradFactorialSq ρ m u = fsum ρ 1 m u := classicalGradFactorialSq_eq ρ m hu

theorem measurable_ofReal_fdens (ρ : ℝ) (e j : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((j + e : ℕ) : ℕ∞) u) :
    Measurable (fun x => ENNReal.ofReal (fdens ρ e j u x)) := by
  simp only [ofReal_fdens]
  exact (Finset.measurable_sum _ fun w _ => measurable_enorm_sq_orderedDerivative hu w).const_mul _

theorem isZ2Periodic_fdens (ρ : ℝ) (e j : ℕ) {u : Vec 2 → E} (hu : IsZ2Periodic u) :
    IsZ2Periodic (fun x => fdens ρ e j u x) := by
  intro n x
  unfold fdens
  refine congrArg _ (Finset.sum_congr rfl fun w _ => ?_)
  rw [isZ2Periodic_orderedDerivative w hu n x]

theorem fsum_eq_lintegral (ρ : ℝ) (e M : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((M + e : ℕ) : ℕ∞) u) :
    fsum ρ e M u = ∫⁻ x in unitCube, ENNReal.ofReal (∑ j ∈ Finset.range (M + 1), fdens ρ e j u x) := by
  unfold fsum
  rw [← lintegral_finsetSum]
  · refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => fdens_nonneg _ _ _ _ _)]
  · intro j hj
    exact measurable_ofReal_fdens ρ e j (hu.of_le (by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      exact_mod_cast Nat.add_le_add_right this e))

/-- Transport of the factorial densities through a chart. -/
theorem fsum_le_of_pointwise {κ : Type*} [Fintype κ] {Φ Ψ : Vec 2 → Vec 2} (hC : IsChart Φ Ψ)
    (ρ : ℝ) (e M : ℕ) {u : Vec 2 → F} (hu : ContDiff ℝ ((M + e : ℕ) : ℕ∞) u)
    {g : κ → Vec 2 → E} (hg : ∀ l, ContDiff ℝ ((M + e : ℕ) : ℕ∞) (g l))
    (hgp : ∀ l, IsZ2Periodic (g l)) {C : ℝ}
    (hpt : ∀ y, ∑ j ∈ Finset.range (M + 1), fdens ρ e j u y ≤
      C * ∑ l, ∑ i ∈ Finset.range (M + 1), fdens ρ e i (g l) (Φ y)) :
    fsum ρ e M u ≤ ENNReal.ofReal C * ∑ l, fsum ρ e M (g l) := by
  rw [fsum_eq_lintegral ρ e M hu]
  set G : κ → Vec 2 → ℝ≥0∞ := fun l x => ∑ i ∈ Finset.range (M + 1),
    ENNReal.ofReal (fdens ρ e i (g l) x) with hG
  have hGm : ∀ l, Measurable (G l) := fun l =>
    Finset.measurable_sum _ fun i hi => measurable_ofReal_fdens ρ e i ((hg l).of_le (by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      exact_mod_cast Nat.add_le_add_right this e))
  have hGp : ∀ l, IsZ2Periodic (G l) := fun l n x => by
    simp only [hG, isZ2Periodic_fdens ρ e _ (hgp l) n x]
  calc ∫⁻ x in unitCube, ENNReal.ofReal (∑ j ∈ Finset.range (M + 1), fdens ρ e j u x)
      ≤ ∫⁻ x in unitCube, ENNReal.ofReal C * ∑ l, G l (Φ x) := by
        refine lintegral_mono fun x => ?_
        refine (ENNReal.ofReal_le_ofReal (hpt x)).trans ?_
        have hS : 0 ≤ ∑ l, ∑ i ∈ Finset.range (M + 1), fdens ρ e i (g l) (Φ x) :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => fdens_nonneg _ _ _ _ _
        rw [ENNReal.ofReal_mul' hS, ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
            Finset.sum_nonneg fun _ _ => fdens_nonneg _ _ _ _ _)]
        refine le_of_eq (congrArg _ (Finset.sum_congr rfl fun l _ => ?_))
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => fdens_nonneg _ _ _ _ _)]
    _ = ENNReal.ofReal C * ∑ l, ∫⁻ x in unitCube, G l x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum (f := fun l x => G l (Φ x)) _
          (fun l _ => (hGm l).comp hC.contΦ.continuous.measurable)]
        congr 1
        exact Finset.sum_congr rfl fun l _ => hC.cell_comp (G l) (hGp l)
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold fsum
        rw [lintegral_finsetSum]
        exact fun i hi => measurable_ofReal_fdens ρ e i ((hg l).of_le (by
          have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          exact_mod_cast Nat.add_le_add_right this e))
end

/-! Chart transport: factorial-norm bounds for `g ∘ Φ` and for the inverse-Piola combinations. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constant of `fdens_sum_le`. -/
def densConst (M e c : ℕ) (K : ℝ) : ℝ := (M + 1) * ((M + 1) * c * (2 ^ (M + e)) ^ 2 * K ^ 2)

theorem densConst_nonneg (M e c : ℕ) (K : ℝ) : 0 ≤ densConst M e c K := by
  unfold densConst; positivity

theorem jet_comp_H {g : Vec 2 → E} {Θ : Vec 2 → Vec 2} {M e N : ℕ} (he : e ≤ 1) (hMe : M + e ≤ N)
    (hg : ContDiff ℝ ((M + e : ℕ) : ℕ∞) g) (hΘ : ContDiff ℝ ((M + e : ℕ) : ℕ∞) Θ)
    {D Rχ ρ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ) (hρR : ρ ≤ Rχ) (hJ : JetBound Θ N D Rχ) (x : Vec 2) :
    ∀ j, j ≤ M → ρ ^ j * ‖iteratedFDeriv ℝ (j + e) (g ∘ Θ) x‖ ≤
      (N.factorial * D ^ N) * ∑ i ∈ Finset.range (j + 1),
        ρ ^ i * ‖iteratedFDeriv ℝ (i + e) g (Θ x)‖ := by
  intro j hj
  have hD0 : 0 ≤ D := by linarith
  have hfac : ((j + e).factorial : ℝ) * D ^ (j + e) ≤ N.factorial * D ^ N := by
    have h1 : ((j + e).factorial : ℝ) ≤ N.factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h2 : D ^ (j + e) ≤ D ^ N := pow_le_pow_right₀ hD (by omega)
    gcongr
  have hjn : j + e ≤ M + e := Nat.add_le_add_right hj e
  have hjn' : ((j + e : ℕ) : ℕ∞) ≤ ((M + e : ℕ) : ℕ∞) := by exact_mod_cast hjn
  have hg' : ContDiff ℝ ((j + e : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast hjn)
  have hΘ' : ContDiff ℝ ((j + e : ℕ) : ℕ∞) Θ := hΘ.of_le (by exact_mod_cast hjn)
  have hJ' : ∀ p, 1 ≤ p → p ≤ j + e → ‖iteratedFDeriv ℝ p Θ x‖ ≤ D * Rχ⁻¹ ^ (p - 1) :=
    fun p hp1 hp => hJ p hp1 (by omega) x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl
  · have h := scaled_comp_bound (n := j + 0) hg' hΘ' hD hρ hρR x hJ'
    simp only [add_zero] at h hfac ⊢
    exact h.trans (mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg fun _ _ => by positivity))
  · have h := scaled_comp_bound_pos (n := j + 1) (by omega) hg' hΘ' hD hρ hρR x hJ'
    have hmul : ρ * (ρ ^ j * ‖iteratedFDeriv ℝ (j + 1) (g ∘ Θ) x‖) ≤
        ρ * (((N.factorial : ℝ) * D ^ N) * ∑ i ∈ Finset.range (j + 1),
          ρ ^ i * ‖iteratedFDeriv ℝ (i + 1) g (Θ x)‖) := by
      calc ρ * (ρ ^ j * ‖iteratedFDeriv ℝ (j + 1) (g ∘ Θ) x‖)
          = ρ ^ (j + 1) * ‖iteratedFDeriv ℝ (j + 1) (g ∘ Θ) x‖ := by ring
        _ ≤ ((j + 1).factorial * D ^ (j + 1)) * ∑ i ∈ Finset.range (j + 1),
            ρ ^ (i + 1) * ‖iteratedFDeriv ℝ (i + 1) g (Θ x)‖ := h
        _ ≤ (N.factorial * D ^ N) * ∑ i ∈ Finset.range (j + 1),
            ρ ^ (i + 1) * ‖iteratedFDeriv ℝ (i + 1) g (Θ x)‖ :=
            mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg fun _ _ => by positivity)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    exact le_of_mul_le_mul_left hmul hρ

/-- Factorial norms under composition with the chart. -/
theorem fsum_comp_le {Φ Ψ : Vec 2 → Vec 2} (hC : IsChart Φ Ψ) {M e N : ℕ} (he : e ≤ 1)
    (hMe : M + e ≤ N) {g : Vec 2 → E} (hg : ContDiff ℝ ((M + e : ℕ) : ℕ∞) g)
    (hgp : IsZ2Periodic g) (hΦ : ContDiff ℝ ((M + e : ℕ) : ℕ∞) Φ) {D Rχ ρ : ℝ} (hD : 1 ≤ D)
    (hρ : 0 < ρ) (hρR : ρ ≤ Rχ) (hJ : JetBound Φ N D Rχ) :
    fsum ρ e M (g ∘ Φ) ≤ ENNReal.ofReal (densConst M e 1 (N.factorial * D ^ N)) *
      fsum ρ e M g := by
  have h := fsum_le_of_pointwise hC ρ e M (u := g ∘ Φ) (hg.comp hΦ) (g := fun _ : Unit => g)
    (fun _ => hg) (fun _ => hgp) (C := densConst M e 1 (N.factorial * D ^ N)) (fun y => by
      have := fdens_sum_le (κ := Unit) (M := M) (e := e) (ρ := ρ) (K := N.factorial * D ^ N)
        hρ.le (hg.comp hΦ) (g := fun _ => g) (fun _ => hg) y (Φ y)
        (fun j hj => by simpa using jet_comp_H he hMe hg hΦ hD hρ hρR hJ y j hj)
      simpa [densConst] using this)
  simpa using h
end

/-! Chart transport, part (2): the pull-back strong energy of `a ∘ Φ`. -/

/-- The window hypotheses of the chart, as `IsChart` and a jet bound with the common constant. -/
theorem chart_data {Φ Ψ : ℝ → Vec 2 → Vec 2} {m r : ℕ} {Cχ : ℕ → ℝ} {Rχ t₀ t₁ : ℝ}
    (hR : 0 < Rχ)
    (hl : ∀ t y, Ψ t (Φ t y) = y) (hr : ∀ t x, Φ t (Ψ t x) = x)
    (heq : ∀ t (n : Fin 2 → ℤ) y, Φ t (y + latticeShift n) = Φ t y + latticeShift n)
    (hdet : ∀ t y, (jacMatrix (Φ t) y).det = 1)
    (hΦ : ∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Φ t))
    (hΨ : ∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Ψ t))
    (hjet : ∀ t ∈ Set.Icc t₀ t₁, ∀ p, 1 ≤ p → p ≤ m + r + 2 → ∀ y,
      ‖iteratedFDeriv ℝ p (Φ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
      ‖iteratedFDeriv ℝ p (Ψ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) :
    IsChart (Φ t) (Ψ t) ∧
      JetBound (Φ t) (m + r + 2) (1 + ∑ p ∈ Finset.range (m + r + 2 + 1), |Cχ p|) Rχ ∧
      JetBound (Ψ t) (m + r + 2) (1 + ∑ p ∈ Finset.range (m + r + 2 + 1), |Cχ p|) Rχ := by
  refine ⟨⟨(hΦ t).of_le (by exact_mod_cast Nat.le_add_left 1 _), (hΨ t).of_le
    (by exact_mod_cast Nat.le_add_left 1 _), hl t, hr t, heq t, hdet t⟩, ?_, ?_⟩
  · exact jetBound_of_Cχ hR fun p hp1 hpN y => (hjet t ht p hp1 hpN y).1
  · exact jetBound_of_Cχ hR fun p hp1 hpN y => (hjet t ht p hp1 hpN y).2

theorem part2 (m r : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (B ρ rs Rχ t₀ t₁ : ℝ) (Φ Ψ : ℝ → Vec 2 → Vec 2),
        0 < rs → rs ≤ ρ → ρ ≤ Rχ →
        (∀ t y, Ψ t (Φ t y) = y) → (∀ t x, Φ t (Ψ t x) = x) →
        (∀ t (n : Fin 2 → ℤ) y,
          Φ t (y + AVenhance.latticeShift n) = Φ t y + AVenhance.latticeShift n) →
        (∀ t y, (jacMatrix (Φ t) y).det = 1) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Φ t)) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Ψ t)) →
        (∀ t ∈ Set.Icc t₀ t₁, ∀ p, 1 ≤ p → p ≤ m + r + 2 → ∀ y,
          ‖iteratedFDeriv ℝ p (Φ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (Ψ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        ∀ a : ℝ → Vec 2 → ∀ i, h i,
          (∀ t, ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (a t)) → (∀ t, AVenhance.IsZ2Periodic (a t)) →
          classicalStrongEnergy ρ B π (Set.Icc t₀ t₁) (m + r) (fun t y => a t (Φ t y))
            ≤ ENNReal.ofReal C * classicalStrongEnergy ρ B π (Set.Icc t₀ t₁) (m + r) a := by
  set N := m + r + 2 with hN
  set D := 1 + ∑ p ∈ Finset.range (N + 1), |Cχ p| with hD
  set K : ℝ := N.factorial * D ^ N with hK
  set Cc : ℝ := max (densConst (m + r) 0 1 K) (densConst (m + r) 1 1 K) with hCc
  have hCc0 : 0 ≤ Cc := le_trans (densConst_nonneg _ _ _ _) (le_max_left _ _)
  refine ⟨Cc ^ (1 / 2 : ℝ), Real.rpow_nonneg hCc0 _, ?_⟩
  intro ι _ h _ _ _ _ π B ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet a ha hap
  have hρ : 0 < ρ := lt_of_lt_of_le hrs hrsρ
  have hR : 0 < Rχ := lt_of_lt_of_le hρ hρR
  have hFS : ∀ t ∈ Set.Icc t₀ t₁, ∀ v : ι,
      classicalFactorialSq ρ (m + r) (fun x => a t (Φ t x) v) ≤
        ENNReal.ofReal Cc * classicalFactorialSq ρ (m + r) (fun x => a t x v) := by
    intro t ht v
    obtain ⟨hC, hJΦ, -⟩ := chart_data hR hl hr heq hdet hΦ hΨ hjet t ht
    have hg : ContDiff ℝ ((m + r + 0 : ℕ) : ℕ∞) (fun x => a t x v) :=
      (contDiff_pi.1 ((ha t).of_le (by exact_mod_cast Nat.le_succ _))) v
    have hgΦ : ContDiff ℝ ((m + r + 0 : ℕ) : ℕ∞) (fun x => a t (Φ t x) v) :=
      hg.comp ((hΦ t).of_le (by exact_mod_cast Nat.le_add_right _ _))
    rw [classicalFactorialSq_eq_fsum ρ (m + r) (by simpa using hgΦ),
      classicalFactorialSq_eq_fsum ρ (m + r) (by simpa using hg)]
    refine (fsum_comp_le hC (e := 0) (N := N) (by norm_num) (by omega) hg
      (fun n x => by
        simpa using congrFun (hap t n x) v) ((hΦ t).of_le (by exact_mod_cast Nat.le_add_right _ _))
      (one_le_jetConst Cχ N) hρ hρR hJΦ).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le
  have hGS : ∀ t ∈ Set.Icc t₀ t₁, ∀ v : ι,
      classicalGradFactorialSq ρ (m + r) (fun x => a t (Φ t x) v) ≤
        ENNReal.ofReal Cc * classicalGradFactorialSq ρ (m + r) (fun x => a t x v) := by
    intro t ht v
    obtain ⟨hC, hJΦ, -⟩ := chart_data hR hl hr heq hdet hΦ hΨ hjet t ht
    have hg : ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (fun x => a t x v) :=
      (contDiff_pi.1 (ha t)) v
    have hΦ1 : ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (Φ t) :=
      (hΦ t).of_le (by exact_mod_cast Nat.le_succ _)
    rw [classicalGradFactorialSq_eq_fsum ρ (m + r) (u := fun x => a t (Φ t x) v) (hg.comp hΦ1),
      classicalGradFactorialSq_eq_fsum ρ (m + r) hg]
    refine (fsum_comp_le hC (e := 1) (N := N) (by norm_num) (by omega) hg
      (fun n x => by
        simpa using congrFun (hap t n x) v) hΦ1
      (one_le_jetConst Cχ N) hρ hρR hJΦ).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) zero_le
  have hmeas : MeasurableSet (Set.Icc t₀ t₁) := measurableSet_Icc
  unfold classicalStrongEnergy
  have hinner : ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ Set.Icc t₀ t₁, classicalFactorialSq ρ (m + r) (fun x => a t (Φ t x) v)) +
        ENNReal.ofReal B * ∫⁻ t in Set.Icc t₀ t₁,
          classicalGradFactorialSq ρ (m + r) (fun x => a t (Φ t x) v)) ≤
      ENNReal.ofReal Cc * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ((⨆ t ∈ Set.Icc t₀ t₁, classicalFactorialSq ρ (m + r) (fun x => a t x v)) +
          ENNReal.ofReal B * ∫⁻ t in Set.Icc t₀ t₁,
            classicalGradFactorialSq ρ (m + r) (fun x => a t x v)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 : (⨆ t ∈ Set.Icc t₀ t₁, classicalFactorialSq ρ (m + r) (fun x => a t (Φ t x) v)) ≤
        ENNReal.ofReal Cc * ⨆ t ∈ Set.Icc t₀ t₁, classicalFactorialSq ρ (m + r) (fun x => a t x v) := by
      refine iSup₂_le fun t ht => (hFS t ht v).trans ?_
      exact mul_le_mul_of_nonneg_left
        (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) =>
          classicalFactorialSq ρ (m + r) (fun x => a t x v)) t ht) zero_le
    have h2 : ∫⁻ t in Set.Icc t₀ t₁, classicalGradFactorialSq ρ (m + r) (fun x => a t (Φ t x) v) ≤
        ENNReal.ofReal Cc * ∫⁻ t in Set.Icc t₀ t₁,
          classicalGradFactorialSq ρ (m + r) (fun x => a t x v) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' hmeas fun t ht => hGS t ht v
    calc ENNReal.ofReal (π v)⁻¹ * _ ≤ ENNReal.ofReal (π v)⁻¹ *
          (ENNReal.ofReal Cc * (⨆ t ∈ Set.Icc t₀ t₁, classicalFactorialSq ρ (m + r) (fun x => a t x v)) +
            ENNReal.ofReal B * (ENNReal.ofReal Cc * ∫⁻ t in Set.Icc t₀ t₁,
              classicalGradFactorialSq ρ (m + r) (fun x => a t x v))) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ (ENNReal.ofReal Cc * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ((⨆ t ∈ Set.Icc t₀ t₁, classicalFactorialSq ρ (m + r) (fun x => a t x v)) +
          ENNReal.ofReal B * ∫⁻ t in Set.Icc t₀ t₁,
            classicalGradFactorialSq ρ (m + r) (fun x => a t x v))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hinner (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hCc0 (by norm_num)]

end AVRegularity.ChartTransport
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev MeasureTheory AVenhance
open scoped ENNReal ContDiff
namespace AVRegularity.ChartTransport

/-! Chart transport, part (1): the time-slice estimates `fluxInt`, `scalInt`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The flux slice norm squared, `∑_v π_v⁻¹ ∫ ∑_k ‖F_{k,v}‖²`. -/
noncomputable def fluxInt (π : ι → ℝ) (F : Vec 2 → Fin 2 → ∀ i, h i) : ℝ≥0∞ :=
  ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in unitCube, ∑ k : Fin 2, ‖F x k v‖ₑ ^ 2

/-- The scalar slice norm squared. -/
noncomputable def scalInt (π : ι → ℝ) (q : Vec 2 → ∀ i, h i) : ℝ≥0∞ :=
  ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in unitCube, ‖q x v‖ₑ ^ 2

theorem enorm_sq_eq_ofReal {E : Type*} [NormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem lintegral_le_transport {α : Type*} (S : Finset α) {Φ Ψ : Vec 2 → Vec 2}
    (hC : IsChart Φ Ψ) (Fam : α → Vec 2 → ℝ≥0∞) (hm : ∀ a ∈ S, Measurable (Fam a))
    (hp : ∀ a ∈ S, IsZ2Periodic (Fam a)) {U : Vec 2 → ℝ≥0∞} {c : ℝ}
    (hU : ∀ x, U x ≤ ENNReal.ofReal c * ∑ a ∈ S, Fam a (Ψ x)) :
    ∫⁻ x in unitCube, U x ≤ ENNReal.ofReal c * ∑ a ∈ S, ∫⁻ x in unitCube, Fam a x := by
  calc ∫⁻ x in unitCube, U x ≤ ∫⁻ x in unitCube, ENNReal.ofReal c * ∑ a ∈ S, Fam a (Ψ x) :=
        lintegral_mono hU
    _ = ENNReal.ofReal c * ∑ a ∈ S, ∫⁻ x in unitCube, Fam a (Ψ x) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum (f := fun a x => Fam a (Ψ x)) _
            (fun a ha => (hm a ha).comp hC.contΨ.continuous.measurable)]
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun a ha => hC.cell_comp_inv (Fam a) (hp a ha)

theorem measurable_slice_flux {r : ℕ} {R : Vec 2 → Fin 2 → ∀ i, h i}
    (hR : ∀ l, ContDiff ℝ (r : ℕ∞) (fun x => R x l)) {i : ℕ} (hi : i ≤ r) (w : DerivativeWord2 i)
    (rs : ℝ) (v : ι) :
    Measurable (fun y => ∑ l : Fin 2,
      ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) y) v‖ₑ ^ 2) := by
  refine Finset.measurable_sum _ fun l _ => ?_
  have hc := continuous_orderedDerivative w ((hR l).of_le (by exact_mod_cast hi))
  have : Continuous (fun y => (rs ^ i • orderedDerivative w (fun x' => R x' l) y) v) :=
    (continuous_apply v).comp (hc.const_smul (rs ^ i))
  exact this.enorm.measurable.pow_const 2

theorem periodic_slice_flux {R : Vec 2 → Fin 2 → ∀ i, h i}
    (hRp : ∀ l, IsZ2Periodic (fun x => R x l)) (i : ℕ) (w : DerivativeWord2 i) (rs : ℝ) (v : ι) :
    IsZ2Periodic (fun y => ∑ l : Fin 2,
      ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) y) v‖ₑ ^ 2) := by
  intro n y
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [isZ2Periodic_orderedDerivative w (hRp l) n y]

theorem flux_slice {Φ Ψ : Vec 2 → Vec 2} (hC : IsChart Φ Ψ) {r j : ℕ} (hj : j ≤ r)
    (hΦ : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) Φ) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    {R : Vec 2 → Fin 2 → ∀ i, h i} (hR : ∀ l, ContDiff ℝ (r : ℕ∞) (fun x => R x l))
    (hRp : ∀ l, IsZ2Periodic (fun x => R x l)) {D Rχ rs : ℝ} (hD : 1 ≤ D) (hs : 0 < rs)
    (hsR : rs ≤ Rχ) (hJΦ : JetBound Φ (r + 1) D Rχ) (hJΨ : JetBound Ψ r D Rχ) (π : ι → ℝ)
    (β : DerivativeWord2 j) :
    fluxInt π (fun x k => rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) ≤
      ENNReal.ofReal (2 * fluxConst D r) * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
        fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => R x' l) x) := by
  unfold fluxInt
  have hv : ∀ v : ι, ∫⁻ x in unitCube, ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * fluxConst D r) * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
        ∫⁻ x in unitCube, ∑ l : Fin 2, ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) x) v‖ₑ ^ 2 := by
    intro v
    have hmi : ∀ i ∈ Finset.range (j + 1), i ≤ r := fun i hi =>
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have key := lintegral_le_transport (Finset.range (j + 1)) hC
      (fun i y => ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
        ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) y) v‖ₑ ^ 2)
      (fun i hi => Finset.measurable_sum _ fun w _ => measurable_slice_flux hR (hmi i hi) w rs v)
      (fun i hi n y => Finset.sum_congr rfl fun w _ => periodic_slice_flux hRp i w rs v n y)
      (U := fun x => ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ₑ ^ 2)
      (c := 2 * fluxConst D r) (fun x => by
        have hpt : ∀ k : Fin 2, ‖(rs ^ j • orderedDerivative β
            (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ₑ ^ 2 ≤
            ENNReal.ofReal (fluxConst D r) * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
              ∑ l : Fin 2, ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) (Ψ x)) v‖ₑ ^ 2 := by
          intro k
          rw [enorm_sq_eq_ofReal]
          have h1 := flux_sq hj hΦ hΨ hR hD hs hsR hJΦ hJΨ k β x v
          refine (ENNReal.ofReal_le_ofReal h1).trans ?_
          rw [ENNReal.ofReal_mul (fluxConst_nonneg r)]
          refine le_of_eq (congrArg _ ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          exact Finset.sum_congr rfl fun l _ => (enorm_sq_eq_ofReal _).symm
        calc ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
            (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ₑ ^ 2
            ≤ ∑ _k : Fin 2, ENNReal.ofReal (fluxConst D r) * ∑ i ∈ Finset.range (j + 1),
              ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
                ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) (Ψ x)) v‖ₑ ^ 2 :=
              Finset.sum_le_sum fun k _ => hpt k
          _ = ENNReal.ofReal (2 * fluxConst D r) * ∑ i ∈ Finset.range (j + 1),
              ∑ w : DerivativeWord2 i, ∑ l : Fin 2,
                ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) (Ψ x)) v‖ₑ ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                ENNReal.ofReal_mul (by norm_num)]
              simp only [nsmul_eq_mul]
              norm_num
              ring)
    refine key.trans (le_of_eq (congrArg _ (Finset.sum_congr rfl fun i hi => ?_)))
    rw [lintegral_finsetSum]
    exact fun w _ => measurable_slice_flux hR (hmi i hi) w rs v
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in unitCube, ∑ k : Fin 2, ‖(rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • R (Ψ x') l) x) v‖ₑ ^ 2
      ≤ ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (2 * fluxConst D r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          ∫⁻ x in unitCube, ∑ l : Fin 2, ‖(rs ^ i • orderedDerivative w (fun x' => R x' l) x) v‖ₑ ^ 2) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hv v) zero_le
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
        ring

theorem measurable_slice_scalar {r : ℕ} {q : Vec 2 → ∀ i, h i}
    (hq : ContDiff ℝ (r : ℕ∞) q) {i : ℕ} (hi : i ≤ r) (w : DerivativeWord2 i) (rs : ℝ) (v : ι) :
    Measurable (fun y => ‖(rs ^ i • orderedDerivative w q y) v‖ₑ ^ 2) := by
  have hc := continuous_orderedDerivative w (hq.of_le (by exact_mod_cast hi))
  have : Continuous (fun y => (rs ^ i • orderedDerivative w q y) v) :=
    (continuous_apply v).comp (hc.const_smul (rs ^ i))
  exact this.enorm.measurable.pow_const 2

theorem periodic_slice_scalar {q : Vec 2 → ∀ i, h i} (hqp : IsZ2Periodic q) (i : ℕ)
    (w : DerivativeWord2 i) (rs : ℝ) (v : ι) :
    IsZ2Periodic (fun y => ‖(rs ^ i • orderedDerivative w q y) v‖ₑ ^ 2) := by
  intro n y
  simp only [isZ2Periodic_orderedDerivative w hqp n y]

theorem scalar_slice {Φ Ψ : Vec 2 → Vec 2} (hC : IsChart Φ Ψ) {r j : ℕ} (hj : j ≤ r)
    (hΨ : ContDiff ℝ (r : ℕ∞) Ψ) {q : Vec 2 → ∀ i, h i} (hq : ContDiff ℝ (r : ℕ∞) q)
    (hqp : IsZ2Periodic q) {D Rχ rs : ℝ} (hD : 1 ≤ D) (hs : 0 < rs) (hsR : rs ≤ Rχ)
    (hJΨ : JetBound Ψ r D Rχ) (π : ι → ℝ) (β : DerivativeWord2 j) :
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' => q (Ψ x')) x) ≤
      ENNReal.ofReal (scalarConst D r) * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
        scalInt π (fun x => rs ^ i • orderedDerivative w q x) := by
  unfold scalInt
  have hv : ∀ v : ι, ∫⁻ x in unitCube, ‖(rs ^ j • orderedDerivative β (fun x' => q (Ψ x')) x) v‖ₑ ^ 2 ≤
      ENNReal.ofReal (scalarConst D r) * ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
        ∫⁻ x in unitCube, ‖(rs ^ i • orderedDerivative w q x) v‖ₑ ^ 2 := by
    intro v
    have hmi : ∀ i ∈ Finset.range (j + 1), i ≤ r := fun i hi =>
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have key := lintegral_le_transport (Finset.range (j + 1)) hC
      (fun i y => ∑ w : DerivativeWord2 i, ‖(rs ^ i • orderedDerivative w q y) v‖ₑ ^ 2)
      (fun i hi => Finset.measurable_sum _ fun w _ => measurable_slice_scalar hq (hmi i hi) w rs v)
      (fun i hi n y => Finset.sum_congr rfl fun w _ => periodic_slice_scalar hqp i w rs v n y)
      (U := fun x => ‖(rs ^ j • orderedDerivative β (fun x' => q (Ψ x')) x) v‖ₑ ^ 2)
      (c := scalarConst D r) (fun x => by
        rw [enorm_sq_eq_ofReal]
        have h1 := scalar_sq hj hΨ hq hD hs hsR hJΨ β x v
        refine (ENNReal.ofReal_le_ofReal h1).trans ?_
        rw [ENNReal.ofReal_mul (scalarConst_nonneg r)]
        refine le_of_eq (congrArg _ ?_)
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        exact Finset.sum_congr rfl fun w _ => (enorm_sq_eq_ofReal _).symm)
    refine key.trans (le_of_eq (congrArg _ (Finset.sum_congr rfl fun i hi => ?_)))
    rw [lintegral_finsetSum]
    exact fun w _ => measurable_slice_scalar hq (hmi i hi) w rs v
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in unitCube, ‖(rs ^ j • orderedDerivative β (fun x' => q (Ψ x')) x) v‖ₑ ^ 2
      ≤ ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (scalarConst D r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          ∫⁻ x in unitCube, ‖(rs ^ i • orderedDerivative w q x) v‖ₑ ^ 2) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hv v) zero_le
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
        ring
end

/-! Chart transport, part (3): the inverse-Piola pull-back flux `(DΦ)⁻¹ (Fc ∘ Φ)`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_jac_entry {Φ : Vec 2 → Vec 2} {n : ℕ} (hΦ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) Φ)
    (c : ℝ) (a b : Fin 2) : ContDiff ℝ (n : ℕ∞) (fun z => c * jacMatrix Φ z a b) := by
  have hfd : ContDiff ℝ (n : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  have : ContDiff ℝ (n : ℕ∞) (fun y => jacMatrix Φ y a b) :=
    (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) a).comp
        (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec b)))).comp hfd
  exact contDiff_const.mul this

theorem contDiff_piola_comb {Φ : Vec 2 → Vec 2} {M : ℕ}
    (hΦ : ContDiff ℝ ((M + 1 : ℕ) : ℕ∞) Φ) {G : Fin 2 → Vec 2 → E}
    (hG : ∀ l, ContDiff ℝ ((M : ℕ) : ℕ∞) (G l)) (c : Fin 2 → ℝ) (a b : Fin 2 → Fin 2) :
    ContDiff ℝ (M : ℕ∞) (fun z => ∑ l : Fin 2, (c l * jacMatrix Φ z (a l) (b l)) • G l (Φ z)) := by
  refine ContDiff.sum fun l _ => ?_
  exact (contDiff_jac_entry hΦ (c l) (a l) (b l)).smul
    ((hG l).comp (hΦ.of_le (by exact_mod_cast Nat.le_succ M)))

/-- The factorial norm of the inverse-Piola component. -/
theorem fsum_piola_le {Φ Ψ : Vec 2 → Vec 2} (hC : IsChart Φ Ψ) {M N : ℕ} (hMN : M + 1 ≤ N)
    {G : Fin 2 → Vec 2 → E} (hG : ∀ l, ContDiff ℝ ((M : ℕ) : ℕ∞) (G l))
    (hGp : ∀ l, IsZ2Periodic (G l)) (hΦ : ContDiff ℝ ((M + 1 : ℕ) : ℕ∞) Φ) {c : Fin 2 → ℝ}
    (hc : ∀ l, |c l| ≤ 1) (a b : Fin 2 → Fin 2) {D Rχ ρ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ)
    (hρR : ρ ≤ Rχ) (hJ : JetBound Φ N D Rχ) (u : Vec 2 → E)
    (hu : u = fun z => ∑ l : Fin 2, (c l * jacMatrix Φ z (a l) (b l)) • G l (Φ z)) :
    fsum ρ 0 M u ≤ ENNReal.ofReal (densConst M 0 2 (2 ^ N * D * compConst D N)) *
      ∑ l, fsum ρ 0 M (G l) := by
  have hu' : ContDiff ℝ ((M + 0 : ℕ) : ℕ∞) u := by
    rw [hu]; exact contDiff_piola_comb hΦ hG c a b
  refine fsum_le_of_pointwise hC ρ 0 M hu' (g := G) (fun l => by simpa using hG l) hGp
    (C := densConst M 0 2 (2 ^ N * D * compConst D N)) (fun y => ?_)
  have := fdens_sum_le (κ := Fin 2) (M := M) (e := 0) (ρ := ρ) (K := 2 ^ N * D * compConst D N)
    hρ.le hu' (g := G) (fun l => by simpa using hG l) y (Φ y) (fun j hj => by
      have hjΦ : ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) Φ := hΦ.of_le (by
        exact_mod_cast Nat.add_le_add_right hj 1)
      have h := piola_chart_bound (n := j) hjΦ (G := G)
        (fun l => (hG l).of_le (by exact_mod_cast hj)) hc a b hD hρ hρR
        (fun p hp1 hp z => hJ p hp1 (by omega) z) y
      rw [hu]
      refine h.trans ?_
      have h1 : (2 : ℝ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : compConst D j ≤ compConst D N := compConst_mono hD (by omega)
      have hS : 0 ≤ ∑ l : Fin 2, ∑ i ∈ Finset.range (j + 1),
          ρ ^ i * ‖iteratedFDeriv ℝ (i + 0) (G l) (Φ y)‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
      have hD0 : 0 ≤ D := by linarith
      refine mul_le_mul_of_nonneg_right ?_ (by simpa using hS)
      have := compConst_nonneg hD j
      gcongr)
  simpa [densConst] using this

theorem part3 (m r : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (ρ rs Rχ t₀ t₁ : ℝ) (Φ Ψ : ℝ → Vec 2 → Vec 2),
        0 < rs → rs ≤ ρ → ρ ≤ Rχ →
        (∀ t y, Ψ t (Φ t y) = y) → (∀ t x, Φ t (Ψ t x) = x) →
        (∀ t (n : Fin 2 → ℤ) y,
          Φ t (y + AVenhance.latticeShift n) = Φ t y + AVenhance.latticeShift n) →
        (∀ t y, (jacMatrix (Φ t) y).det = 1) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Φ t)) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Ψ t)) →
        (∀ t ∈ Set.Icc t₀ t₁, ∀ p, 1 ≤ p → p ≤ m + r + 2 → ∀ y,
          ‖iteratedFDeriv ℝ p (Φ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (Ψ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        ∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ t k, ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
          (∀ t k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
          classicalFluxL2H ρ π (Set.Icc t₀ t₁) (m + r)
              (fun t y k => ∑ l : Fin 2, (jacMatrix (Φ t) y)⁻¹ k l • Fc t (Φ t y) l)
            ≤ ENNReal.ofReal C * classicalFluxL2H ρ π (Set.Icc t₀ t₁) (m + r) Fc := by
  set N := m + r + 2 with hN
  set D := 1 + ∑ p ∈ Finset.range (N + 1), |Cχ p| with hD
  set Cc : ℝ := 2 * densConst (m + r) 0 2 (2 ^ N * D * compConst D N) with hCc
  have hCc0 : 0 ≤ Cc := by
    have := densConst_nonneg (m + r) 0 2 (2 ^ N * D * compConst D N)
    positivity
  refine ⟨Cc ^ (1 / 2 : ℝ), Real.rpow_nonneg hCc0 _, ?_⟩
  intro ι _ h _ _ _ _ π ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet Fc hF hFp
  have hρ : 0 < ρ := lt_of_lt_of_le hrs hrsρ
  have hR : 0 < Rχ := lt_of_lt_of_le hρ hρR
  have hmeas : MeasurableSet (Set.Icc t₀ t₁) := measurableSet_Icc
  have hpt : ∀ t ∈ Set.Icc t₀ t₁, ∀ v : ι,
      ∑ k : Fin 2, classicalFactorialSq ρ (m + r)
          (fun x => (∑ l : Fin 2, (jacMatrix (Φ t) x)⁻¹ k l • Fc t (Φ t x) l) v) ≤
        ENNReal.ofReal Cc * ∑ k : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x k v) := by
    intro t ht v
    obtain ⟨hC, hJΦ, -⟩ := chart_data hR hl hr heq hdet hΦ hΨ hjet t ht
    have hG : ∀ l : Fin 2, ContDiff ℝ ((m + r : ℕ) : ℕ∞) (fun x => Fc t x l v) := fun l =>
      (contDiff_pi.1 ((hF t l).of_le (by exact_mod_cast Nat.le_succ _))) v
    have hGp : ∀ l : Fin 2, IsZ2Periodic (fun x => Fc t x l v) := fun l n x => by
      simpa using congrFun (hFp t l n x) v
    have hΦ1 : ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (Φ t) :=
      (hΦ t).of_le (by exact_mod_cast Nat.le_succ _)
    have hk : ∀ k : Fin 2, classicalFactorialSq ρ (m + r)
          (fun x => (∑ l : Fin 2, (jacMatrix (Φ t) x)⁻¹ k l • Fc t (Φ t x) l) v) ≤
        ENNReal.ofReal (densConst (m + r) 0 2 (2 ^ N * D * compConst D N)) *
          ∑ l : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x l v) := by
      intro k
      choose c a b hc hcab using fun l => inv_entry k l
      have hu : (fun x => (∑ l : Fin 2, (jacMatrix (Φ t) x)⁻¹ k l • Fc t (Φ t x) l) v) =
          fun z => ∑ l : Fin 2, (c l * jacMatrix (Φ t) z (a l) (b l)) • (fun x => Fc t x l v) (Φ t z) := by
        funext z
        simp only [Finset.sum_apply, Pi.smul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcab l _ (hdet t z)]
      have hcont : ContDiff ℝ ((m + r + 0 : ℕ) : ℕ∞) (fun z => ∑ l : Fin 2,
          (c l * jacMatrix (Φ t) z (a l) (b l)) • (fun x => Fc t x l v) (Φ t z)) := by
        simpa using contDiff_piola_comb hΦ1 hG c a b
      rw [hu, classicalFactorialSq_eq_fsum ρ (m + r) (by simpa using hcont)]
      simp only [fun l => classicalFactorialSq_eq_fsum ρ (m + r) (hG l)]
      exact fsum_piola_le (N := N) hC (by omega) hG hGp hΦ1 hc a b (one_le_jetConst Cχ N) hρ hρR
        hJΦ _ rfl
    calc ∑ k : Fin 2, classicalFactorialSq ρ (m + r)
          (fun x => (∑ l : Fin 2, (jacMatrix (Φ t) x)⁻¹ k l • Fc t (Φ t x) l) v)
        ≤ ∑ k : Fin 2, ENNReal.ofReal (densConst (m + r) 0 2 (2 ^ N * D * compConst D N)) *
          ∑ l : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x l v) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = ENNReal.ofReal Cc * ∑ k : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x k v) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hCc,
            ENNReal.ofReal_mul (by norm_num)]
          simp only [nsmul_eq_mul]
          norm_num
          ring
  unfold classicalFluxL2H
  have hint : (∫⁻ t in Set.Icc t₀ t₁, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∑ k : Fin 2, classicalFactorialSq ρ (m + r)
          (fun x => (∑ l : Fin 2, (jacMatrix (Φ t) x)⁻¹ k l • Fc t (Φ t x) l) v)) ≤
      ENNReal.ofReal Cc * ∫⁻ t in Set.Icc t₀ t₁, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∑ k : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x k v) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hmeas fun t ht => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc ENNReal.ofReal (π v)⁻¹ * _ ≤ ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal Cc *
          ∑ k : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x k v)) :=
          mul_le_mul_of_nonneg_left (hpt t ht v) zero_le
      _ = _ := by ring
  calc _ ≤ (ENNReal.ofReal Cc * ∫⁻ t in Set.Icc t₀ t₁, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∑ k : Fin 2, classicalFactorialSq ρ (m + r) (fun x => Fc t x k v)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hCc0 (by norm_num)]
end

end AVRegularity.ChartTransport
end
end

section
/-! Chart transport, part (1): the Piola-pushed pair `((DΦ R) ∘ Ψ, q ∘ Ψ)`. -/

@[expose] public section

open Homogenization AVRegularity.Sobolev MeasureTheory AVenhance
open scoped ENNReal ContDiff

namespace AVRegularity.ChartTransport

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem measurable_fluxInt {r : ℕ} {R : ℝ → Vec 2 → Fin 2 → ∀ i, h i} (π : ι → ℝ) (rs : ℝ)
    (hmeas : ∀ j', j' ≤ r → ∀ (β' : DerivativeWord2 j') (k : Fin 2) (v : ι),
      Measurable (fun p : ℝ × Vec 2 =>
        ‖orderedDerivative β' (fun x => R p.1 x k) p.2 v‖ₑ))
    {i : ℕ} (hi : i ≤ r) (w : DerivativeWord2 i) :
    Measurable (fun t => fluxInt π (fun x l => rs ^ i • orderedDerivative w
      (fun x' => R t x' l) x)) := by
  unfold fluxInt
  refine Finset.measurable_sum _ fun v _ => Measurable.const_mul ?_ _
  have : Measurable (fun p : ℝ × Vec 2 => ∑ l : Fin 2,
      ‖(rs ^ i • orderedDerivative w (fun x' => R p.1 x' l) p.2) v‖ₑ ^ 2) := by
    refine Finset.measurable_sum _ fun l _ => ?_
    have h1 := (hmeas i hi w l v).const_mul ‖rs ^ i‖ₑ
    have h2 : (fun p : ℝ × Vec 2 => ‖(rs ^ i • orderedDerivative w (fun x' => R p.1 x' l) p.2) v‖ₑ)
        = fun p => ‖rs ^ i‖ₑ * ‖orderedDerivative w (fun x => R p.1 x l) p.2 v‖ₑ := by
      funext p
      rw [Pi.smul_apply, enorm_smul]
    rw [← h2] at h1
    exact h1.pow_const 2
  exact Measurable.lintegral_prod_right' (ν := volume.restrict unitCube)
    (f := fun p : ℝ × Vec 2 => ∑ l : Fin 2,
      ‖(rs ^ i • orderedDerivative w (fun x' => R p.1 x' l) p.2) v‖ₑ ^ 2) this

theorem measurable_scalInt {r : ℕ} {q : ℝ → Vec 2 → ∀ i, h i} (π : ι → ℝ) (rs : ℝ)
    (hmeas : ∀ j', j' ≤ r → ∀ (β' : DerivativeWord2 j') (v : ι),
      Measurable (fun p : ℝ × Vec 2 => ‖orderedDerivative β' (q p.1) p.2 v‖ₑ))
    {i : ℕ} (hi : i ≤ r) (w : DerivativeWord2 i) :
    Measurable (fun t => scalInt π (fun x => rs ^ i • orderedDerivative w (q t) x)) := by
  unfold scalInt
  refine Finset.measurable_sum _ fun v _ => Measurable.const_mul ?_ _
  have : Measurable (fun p : ℝ × Vec 2 =>
      ‖(rs ^ i • orderedDerivative w (q p.1) p.2) v‖ₑ ^ 2) := by
    have h1 := (hmeas i hi w v).const_mul ‖rs ^ i‖ₑ
    have h2 : (fun p : ℝ × Vec 2 => ‖(rs ^ i • orderedDerivative w (q p.1) p.2) v‖ₑ)
        = fun p => ‖rs ^ i‖ₑ * ‖orderedDerivative w (q p.1) p.2 v‖ₑ := by
      funext p
      rw [Pi.smul_apply, enorm_smul]
    rw [← h2] at h1
    exact h1.pow_const 2
  exact Measurable.lintegral_prod_right' (ν := volume.restrict unitCube)
    (f := fun p : ℝ × Vec 2 => ‖(rs ^ i • orderedDerivative w (q p.1) p.2) v‖ₑ ^ 2) this

end AVRegularity.ChartTransport

namespace AVRegularity.ChartTransport

theorem part1 (m r : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (ν _B ρ rs Rχ t₀ t₁ : ℝ) (Φ Ψ : ℝ → Vec 2 → Vec 2),
        0 < rs → rs ≤ ρ → ρ ≤ Rχ →
        (∀ t y, Ψ t (Φ t y) = y) → (∀ t x, Φ t (Ψ t x) = x) →
        (∀ t (n : Fin 2 → ℤ) y,
          Φ t (y + AVenhance.latticeShift n) = Φ t y + AVenhance.latticeShift n) →
        (∀ t y, (jacMatrix (Φ t) y).det = 1) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Φ t)) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Ψ t)) →
        (∀ t ∈ Set.Icc t₀ t₁, ∀ p, 1 ≤ p → p ≤ m + r + 2 → ∀ y,
          ‖iteratedFDeriv ℝ p (Φ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (Ψ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        (∀ (R : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (q : ℝ → Vec 2 → ∀ i, h i),
          (∀ t k, ContDiff ℝ (r : ℕ∞) (fun x => R t x k)) → (∀ t, ContDiff ℝ (r : ℕ∞) (q t)) →
          (∀ t k, AVenhance.IsZ2Periodic (fun x => R t x k)) →
          (∀ t, AVenhance.IsZ2Periodic (q t)) →
          (∀ j', j' ≤ r → ∀ (β' : DerivativeWord2 j') (k : Fin 2) (v : ι),
            Measurable (fun p : ℝ × Vec 2 =>
              ‖orderedDerivative β' (fun x => R p.1 x k) p.2 v‖ₑ)) →
          (∀ j', j' ≤ r → ∀ (β' : DerivativeWord2 j') (v : ι),
            Measurable (fun p : ℝ × Vec 2 => ‖orderedDerivative β' (q p.1) p.2 v‖ₑ)) →
          ∀ j, j ≤ r → ∀ β : DerivativeWord2 j,
            residualNorm ν π (Set.Icc t₀ t₁)
                (fun t x k => rs ^ j • orderedDerivative β
                  (fun x' => ∑ l : Fin 2, jacMatrix (Φ t) (Ψ t x') k l • R t (Ψ t x') l) x)
                (fun t x => rs ^ j • orderedDerivative β (fun x' => q t (Ψ t x')) x)
              ≤ ENNReal.ofReal C *
                ∑ j' ∈ Finset.range (j + 1), ∑ β' : DerivativeWord2 j',
                  residualNorm ν π (Set.Icc t₀ t₁)
                    (fun t x k => rs ^ j' • orderedDerivative β' (fun x' => R t x' k) x)
                    (fun t x => rs ^ j' • orderedDerivative β' (q t) x)) := by
  set N := m + r + 2 with hN
  set D := 1 + ∑ p ∈ Finset.range (N + 1), |Cχ p| with hD
  set c₁ : ℝ := 2 * fluxConst D r with hc₁
  set c₂ : ℝ := scalarConst D r with hc₂
  have hc₁0 : 0 ≤ c₁ := by have := fluxConst_nonneg (D := D) r; positivity
  have hc₂0 : 0 ≤ c₂ := scalarConst_nonneg r
  refine ⟨max (c₁ ^ (1 / 2 : ℝ)) (c₂ ^ (1 / 2 : ℝ)),
    le_max_of_le_left (Real.rpow_nonneg hc₁0 _), ?_⟩
  intro ι _ h _ _ _ _ π ν _B ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet R q hR hq hRp
    hqp hmR hmq j hj β
  have hρ : 0 < ρ := lt_of_lt_of_le hrs hrsρ
  have hR0 : 0 < Rχ := lt_of_lt_of_le hρ hρR
  have hsR : rs ≤ Rχ := hrsρ.trans hρR
  set S : Finset (Σ i : ℕ, DerivativeWord2 i) :=
    (Finset.range (j + 1)).sigma (fun i => (Finset.univ : Finset (DerivativeWord2 i))) with hS
  have hmi : ∀ s ∈ S, s.1 ≤ r := fun s hs =>
    ((Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_sigma.1 hs).1))).trans hj
  have hmeas : MeasurableSet (Set.Icc t₀ t₁) := measurableSet_Icc
  have key := time_assembly S hmeas
    (fun t => fluxInt π (fun x k => rs ^ j • orderedDerivative β
      (fun x' => ∑ l : Fin 2, jacMatrix (Φ t) (Ψ t x') k l • R t (Ψ t x') l) x))
    (fun t => scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' => q t (Ψ t x')) x))
    (fun s t => fluxInt π (fun x l => rs ^ s.1 • orderedDerivative s.2 (fun x' => R t x' l) x))
    (fun s t => scalInt π (fun x => rs ^ s.1 • orderedDerivative s.2 (q t) x))
    (c₁ := c₁) (c₂ := c₂) hc₁0 hc₂0
    (fun t ht => by
      obtain ⟨hC, hJΦ, hJΨ⟩ := chart_data hR0 hl hr heq hdet hΦ hΨ hjet t ht
      have h1 := flux_slice hC hj ((hΦ t).of_le (by exact_mod_cast (show r + 1 ≤ N by omega)))
        ((hΨ t).of_le (by exact_mod_cast (show r ≤ N by omega))) (R := R t) (hR t) (hRp t)
        (one_le_jetConst Cχ N) hrs hsR (fun p hp1 hp y => hJΦ p hp1 (by omega) y)
        (fun p hp1 hp y => hJΨ p hp1 (by omega) y) π β
      rw [hS, Finset.sum_sigma]
      exact h1)
    (fun t ht => by
      obtain ⟨hC, hJΦ, hJΨ⟩ := chart_data hR0 hl hr heq hdet hΦ hΨ hjet t ht
      have h1 := scalar_slice hC hj ((hΨ t).of_le (by exact_mod_cast (show r ≤ N by omega)))
        (hq t) (hqp t) (one_le_jetConst Cχ N) hrs hsR
        (fun p hp1 hp y => hJΨ p hp1 (by omega) y) π β
      rw [hS, Finset.sum_sigma]
      exact h1)
    (fun s hs => measurable_fluxInt π rs hmR (hmi s hs) s.2)
    (fun s hs => measurable_scalInt π rs hmq (hmi s hs) s.2)
    (ENNReal.ofReal (Real.sqrt ν)⁻¹)
  rw [hS, Finset.sum_sigma] at key
  exact key

end AVRegularity.ChartTransport
end
end
end
