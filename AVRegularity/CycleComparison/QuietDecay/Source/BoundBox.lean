-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Source.TermBound
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! Box-smooth variant (slow and fast orders `p + 1`, `q + 1` separately): regularity, continuity and mixed-jet bounds of one term `srcTerm η k a L W J` of the source
coefficient in terms of the mixed jets of the `ε`-coefficients `W`. -/

section TermBound
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]

section Pieces
variable {W : ℕ → Vec 2 → Vec 2 → E₁} {p q : ℕ} (hW : ∀ i, IsBoxSmooth (p + 1) (q + 1) (W i))
include hW

theorem isBoxSmooth_fast_piece_box (L : E₁ →L[ℝ] E₂) (k : Fin 2) (J : ℕ) :
    IsBoxSmooth (p + 1) q (fun X z => L (fastPartial k (W J) X z)) :=
  (IsBoxSmooth.fastPartial (hW J) k).map_clm L

theorem isBoxSmooth_slow_piece_box (L : E₁ →L[ℝ] E₂) (k : Fin 2) (J : ℕ) :
    IsBoxSmooth p (q + 1) (fun X z => L (slowPartial k (W J) X z)) :=
  (IsBoxSmooth.slowPartial (hW J) k).map_clm L

theorem isBoxSmooth_plain_piece_box (L : E₁ →L[ℝ] E₂) (J : ℕ) :
    IsBoxSmooth (p + 1) (q + 1) (fun X z => L (W J X z)) :=
  (hW J).map_clm L

variable {k : Fin 2} {a : Vec 2 → ℝ} {m : ℕ} (L : E₁ →L[ℝ] E₂) (X z : Vec 2) (J₀ : ℕ)
  {β : ℕ → ℕ → ℝ}
  (hJ : ∀ i p' q', p' ≤ p + 1 → q' ≤ q + 1 →
    srcJp (W i) X p' q' z ≤ 2 ^ m * β (p' + i) (q' + m - i))
  {Bs : ℝ} (hBs : ∀ a' b', a' ≤ p + J₀ → b' ≤ q + m + 1 → β a' b' ≤ Bs)
include hJ hBs

theorem srcJp_piece_fast_box (ha : ContDiff ℝ (p : ℕ∞) a) {i : ℕ} (hi : i ≤ J₀) :
    srcJp (fun X z => a X • L (fastPartial k (W i) X z)) X p q z ≤
      2 ^ p * (‖L‖ * (2 ^ m * Bs)) * ∑ i' ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ i' a X‖ := by
  have hb := isBoxSmooth_fast_piece_box hW L k i
  have hf : RegBox p q (fun X z => L (fastPartial k (W i) X z)) :=
    IsBoxSmooth.regBox (hb.mono (by omega) (by omega))
  refine srcJp_mulX_le hf ha le_rfl le_rfl X z fun i' hi' => ?_
  have hF : RegBox (p + 1) q (fastPartial k (W i)) :=
    IsBoxSmooth.regBox (IsBoxSmooth.fastPartial (hW i) k)
  have h1 := srcJp_clm (hF.mono (by omega) (by omega) : RegBox (p - i') q _) L (le_refl _)
    le_rfl X z
  have h2 := srcJp_fastPartial (IsBoxSmooth.regBox (hW i)) k (p := p - i') (q := q)
    (by omega) (by omega) X z
  have h3 := hJ i (p - i') (q + 1) (by omega) (by omega)
  have h4 := hBs (p - i' + i) (q + 1 + m - i) (by omega) (by omega)
  calc _ ≤ ‖L‖ * srcJp (fastPartial k (W i)) X (p - i') q z := h1
    _ ≤ ‖L‖ * (2 ^ m * β (p - i' + i) (q + 1 + m - i)) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg _)
    _ ≤ ‖L‖ * (2 ^ m * Bs) := by gcongr

theorem srcJp_piece_plain_box (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) a) {i : ℕ} (hi : i ≤ J₀) :
    srcJp (fun X z => fderiv ℝ a X (basisVec k) • L (W i X z)) X p q z ≤
      2 ^ p * (‖L‖ * (2 ^ m * Bs)) *
        ∑ i' ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ i' (fun Y => fderiv ℝ a Y (basisVec k)) X‖ := by
  have hb := isBoxSmooth_plain_piece_box hW L i
  have hf : RegBox p q (fun X z => L (W i X z)) :=
    IsBoxSmooth.regBox (hb.mono (by omega) (by omega))
  refine srcJp_mulX_le hf (contDiff_slowDir ha k) le_rfl le_rfl X z fun i' hi' => ?_
  have hF : RegBox (p + 1) (q + 1) (W i) := IsBoxSmooth.regBox (hW i)
  have h1 := srcJp_clm (hF.mono (by omega) (by omega) : RegBox (p - i') q _) L (le_refl _)
    le_rfl X z
  have h3 := hJ i (p - i') q (by omega) (by omega)
  have h4 := hBs (p - i' + i) (q + m - i) (by omega) (by omega)
  calc _ ≤ ‖L‖ * srcJp (W i) X (p - i') q z := h1
    _ ≤ ‖L‖ * (2 ^ m * β (p - i' + i) (q + m - i)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ ‖L‖ * (2 ^ m * Bs) := by gcongr

theorem srcJp_piece_slow_box (ha : ContDiff ℝ (p : ℕ∞) a) {i : ℕ} (hi : i + 1 ≤ J₀) :
    srcJp (fun X z => a X • L (slowPartial k (W i) X z)) X p q z ≤
      2 ^ p * (‖L‖ * (2 ^ m * Bs)) * ∑ i' ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ i' a X‖ := by
  have hb := isBoxSmooth_slow_piece_box hW L k i
  have hf : RegBox p q (fun X z => L (slowPartial k (W i) X z)) :=
    IsBoxSmooth.regBox (hb.mono (by omega) (by omega))
  refine srcJp_mulX_le hf ha le_rfl le_rfl X z fun i' hi' => ?_
  have hF : RegBox p (q + 1) (slowPartial k (W i)) :=
    IsBoxSmooth.regBox (IsBoxSmooth.slowPartial (hW i) k)
  have h1 := srcJp_clm (hF.mono (by omega) (by omega) : RegBox (p - i') q _) L (le_refl _)
    le_rfl X z
  have h2 := srcJp_slowPartial (hW i) k (p := p - i') (q := q) (by omega) (by omega) X z
  have h3 := hJ i (p - i' + 1) q (by omega) (by omega)
  have h4 := hBs (p - i' + 1 + i) (q + m - i) (by omega) (by omega)
  calc _ ≤ ‖L‖ * srcJp (slowPartial k (W i)) X (p - i') q z := h1
    _ ≤ ‖L‖ * (2 ^ m * β (p - i' + 1 + i) (q + m - i)) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg _)
    _ ≤ ‖L‖ * (2 ^ m * Bs) := by gcongr

end Pieces

section Combined
variable {k : Fin 2} {a : Vec 2 → ℝ} {p q : ℕ} {W : ℕ → Vec 2 → Vec 2 → E₁}

theorem regBox_srcTerm_box (η : ℝ) (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) a) (L : E₁ →L[ℝ] E₂)
    (hW : ∀ i, IsBoxSmooth (p + 1) (q + 1) (W i)) (J : ℕ) :
    RegBox p q (srcTerm η k a L W J) := by
  have hap : ContDiff ℝ (p : ℕ∞) a := ha.of_le (by exact_mod_cast Nat.le_succ p)
  have rf : ∀ i, RegBox p q (fun X z => L (fastPartial k (W i) X z)) := fun i =>
    IsBoxSmooth.regBox ((isBoxSmooth_fast_piece_box hW L k i).mono (by omega) (by omega))
  have rp : ∀ i, RegBox p q (fun X z => L (W i X z)) := fun i =>
    IsBoxSmooth.regBox ((isBoxSmooth_plain_piece_box hW L i).mono (by omega) (by omega))
  have rs : ∀ i, RegBox p q (fun X z => L (slowPartial k (W i) X z)) := fun i =>
    IsBoxSmooth.regBox ((isBoxSmooth_slow_piece_box hW L k i).mono (by omega) (by omega))
  cases J with
  | zero => exact (rf 0).mulX hap
  | succ J =>
    exact ((rf (J + 1)).mulX hap).add
      ((((rp J).mulX (contDiff_slowDir ha k)).add ((rs J).mulX hap)).const_smul _)

theorem jcont_srcTerm_box (η : ℝ) (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) a) (L : E₁ →L[ℝ] E₂)
    (hW : ∀ i, IsBoxSmooth (p + 1) (q + 1) (W i)) (J : ℕ) (X : Vec 2) :
    JCont (srcTerm η k a L W J) X p q := by
  have hap : ContDiff ℝ (p : ℕ∞) a := ha.of_le (by exact_mod_cast Nat.le_succ p)
  have bf : ∀ i, IsBoxSmooth p q (fun X z => L (fastPartial k (W i) X z)) := fun i =>
    (isBoxSmooth_fast_piece_box hW L k i).mono (by omega) (by omega)
  have bp : ∀ i, IsBoxSmooth p q (fun X z => L (W i X z)) := fun i =>
    (isBoxSmooth_plain_piece_box hW L i).mono (by omega) (by omega)
  have bs : ∀ i, IsBoxSmooth p q (fun X z => L (slowPartial k (W i) X z)) := fun i =>
    (isBoxSmooth_slow_piece_box hW L k i).mono (by omega) (by omega)
  have rf := fun i => IsBoxSmooth.regBox (bf i)
  have rp := fun i => IsBoxSmooth.regBox (bp i)
  have rs := fun i => IsBoxSmooth.regBox (bs i)
  cases J with
  | zero => exact JCont.mulX (bf 0) hap le_rfl le_rfl X
  | succ J =>
    have c1 := JCont.mulX (bf (J + 1)) hap le_rfl le_rfl X
    have c2 := JCont.mulX (bp J) (contDiff_slowDir ha k) le_rfl le_rfl X
    have c3 := JCont.mulX (bs J) hap le_rfl le_rfl X
    have r2 := (rp J).mulX (contDiff_slowDir ha k)
    have r3 := (rs J).mulX hap
    exact JCont.add ((rf (J + 1)).mulX hap) ((r2.add r3).const_smul _) le_rfl le_rfl c1
      (JCont.const_smul (r2.add r3) _ le_rfl le_rfl (JCont.add r2 r3 le_rfl le_rfl c2 c3))

theorem srcJp_srcTerm_le_box (η : ℝ) (hη : Real.sqrt η ≤ 1) (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) a)
    (L : E₁ →L[ℝ] E₂) {m : ℕ} (hW : ∀ i, IsBoxSmooth (p + 1) (q + 1) (W i))
    (β : ℕ → ℕ → ℝ) (hβ : ∀ a b, 0 ≤ β a b) (X z : Vec 2)
    (hJ : ∀ i p' q', p' ≤ p + 1 → q' ≤ q + 1 →
      srcJp (W i) X p' q' z ≤ 2 ^ m * β (p' + i) (q' + m - i)) (J : ℕ) :
    srcJp (srcTerm η k a L W J) X p q z ≤
      3 * 2 ^ p * 2 ^ m * ‖L‖ * (∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i a X‖) *
        ∑ a' ∈ Finset.range (p + J + 1), ∑ b' ∈ Finset.range (q + m + 2), β a' b' := by
  have hap : ContDiff ℝ (p : ℕ∞) a := ha.of_le (by exact_mod_cast Nat.le_succ p)
  set Bs := ∑ a' ∈ Finset.range (p + J + 1), ∑ b' ∈ Finset.range (q + m + 2), β a' b' with hBs
  set A := ∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i a X‖ with hA
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hβ _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hBle : ∀ a' b', a' ≤ p + J → b' ≤ q + m + 1 → β a' b' ≤ Bs := by
    intro a' b' h1 h2
    have e1 : β a' b' ≤ ∑ b'' ∈ Finset.range (q + m + 2), β a' b'' :=
      Finset.single_le_sum (f := fun b'' => β a' b'') (fun b _ => hβ _ _)
        (Finset.mem_range.mpr (by omega))
    exact e1.trans (Finset.single_le_sum (f := fun a'' => ∑ b'' ∈ Finset.range (q + m + 2),
      β a'' b'') (fun a _ => Finset.sum_nonneg fun _ _ => hβ _ _)
        (Finset.mem_range.mpr (by omega)))
  have hA1 : ∑ i' ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ i' a X‖ ≤ A :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun _ _ _ => norm_nonneg _
  have hA2 : ∑ i' ∈ Finset.range (p + 1),
      ‖iteratedFDeriv ℝ i' (fun Y => fderiv ℝ a Y (basisVec k)) X‖ ≤ A := by
    have e1 : ∑ i' ∈ Finset.range (p + 1),
        ‖iteratedFDeriv ℝ i' (fun Y => fderiv ℝ a Y (basisVec k)) X‖ ≤
        ∑ i' ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ (i' + 1) a X‖ :=
      Finset.sum_le_sum fun i' hi' => norm_iteratedFDeriv_slowDir_le
        (ha.of_le (by exact_mod_cast (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi' :
          i' + 1 ≤ p + 1))) k X
    have e2 : A = ∑ i' ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ (i' + 1) a X‖ +
        ‖iteratedFDeriv ℝ 0 a X‖ := by
      rw [hA, Finset.sum_range_succ' (fun i => ‖iteratedFDeriv ℝ i a X‖) (p + 1)]
    rw [e2]
    exact e1.trans (le_add_of_nonneg_right (norm_nonneg _))
  set T0 : ℝ := 2 ^ p * (‖L‖ * (2 ^ m * Bs)) with hT0
  have hT00 : 0 ≤ T0 := by positivity
  have hfin : ∀ x : ℝ, x ≤ A → T0 * x ≤ T0 * A := fun x hx => mul_le_mul_of_nonneg_left hx hT00
  have hgoal : 3 * 2 ^ p * 2 ^ m * ‖L‖ * A * Bs = 3 * (T0 * A) := by rw [hT0]; ring
  rw [hgoal]
  cases J with
  | zero =>
    have h1 := srcJp_piece_fast_box hW L X z 0 hJ (β := β) (Bs := Bs) (by simpa using hBle) hap
      (le_refl 0) (k := k)
    show srcJp (fun X z => a X • L (fastPartial k (W 0) X z)) X p q z ≤ _
    have := hfin _ hA1
    nlinarith [mul_nonneg hT00 hA0]
  | succ J =>
    have rr := fun i => IsBoxSmooth.regBox (hW i)
    have r1 : RegBox p q (fun X z => a X • L (fastPartial k (W (J + 1)) X z)) :=
      ((IsBoxSmooth.regBox ((isBoxSmooth_fast_piece_box hW L k (J + 1)).mono (by omega)
        (by omega)))).mulX hap
    have rp : RegBox p q (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z)) :=
      (IsBoxSmooth.regBox ((isBoxSmooth_plain_piece_box hW L J).mono (by omega)
        (by omega))).mulX (contDiff_slowDir ha k)
    have rs : RegBox p q (fun X z => a X • L (slowPartial k (W J) X z)) :=
      (IsBoxSmooth.regBox ((isBoxSmooth_slow_piece_box hW L k J).mono (by omega)
        (by omega))).mulX hap
    have hadd := srcJp_add r1 ((rp.add rs).const_smul (Real.sqrt η)) (p := p) (q := q) le_rfl
      le_rfl X z
    have hsm := srcJp_const_smul (rp.add rs) (Real.sqrt η) (p := p) (q := q) le_rfl le_rfl X z
    have hadd2 := srcJp_add rp rs (p := p) (q := q) le_rfl le_rfl X z
    have hB' : ∀ a' b', a' ≤ p + (J + 1) → b' ≤ q + m + 1 → β a' b' ≤ Bs := hBle
    have p1 := srcJp_piece_fast_box hW L X z (J + 1) hJ hB' hap (le_refl _) (k := k)
    have p2 := srcJp_piece_plain_box hW L X z (J + 1) hJ hB' ha (by omega : J ≤ J + 1) (k := k)
    have p3 := srcJp_piece_slow_box hW L X z (J + 1) hJ hB' hap (le_refl _) (k := k)
    have hη0 : |Real.sqrt η| ≤ 1 := by rw [abs_of_nonneg (Real.sqrt_nonneg η)]; exact hη
    have q1 := hfin _ hA1
    have q2 := hfin _ hA2
    have s2 := srcJp_nonneg (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z)) X p q z
    have s3 := srcJp_nonneg (fun X z => a X • L (slowPartial k (W J) X z)) X p q z
    show srcJp (fun X z => a X • L (fastPartial k (W (J + 1)) X z) + Real.sqrt η •
      (fderiv ℝ a X (basisVec k) • L (W J X z) + a X • L (slowPartial k (W J) X z))) X p q z ≤ _
    have e3 : srcJp (fun X z => Real.sqrt η • (fderiv ℝ a X (basisVec k) • L (W J X z) +
        a X • L (slowPartial k (W J) X z))) X p q z =
        |Real.sqrt η| * srcJp (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z) +
        a X • L (slowPartial k (W J) X z)) X p q z := hsm
    have b23 : srcJp (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z) +
        a X • L (slowPartial k (W J) X z)) X p q z ≤ T0 * A + T0 * A :=
      hadd2.trans (add_le_add (p2.trans q2) (p3.trans q1))
    have b1 := p1.trans q1
    have : |Real.sqrt η| * srcJp (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z) +
        a X • L (slowPartial k (W J) X z)) X p q z ≤ T0 * A + T0 * A := by
      have hs0 : 0 ≤ srcJp (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z) +
        a X • L (slowPartial k (W J) X z)) X p q z := srcJp_nonneg _ _ _ _ _
      calc _ ≤ 1 * srcJp (fun X z => fderiv ℝ a X (basisVec k) • L (W J X z) +
          a X • L (slowPartial k (W J) X z)) X p q z := mul_le_mul_of_nonneg_right hη0 hs0
        _ ≤ _ := by rw [one_mul]; exact b23
    refine hadd.trans ?_
    rw [e3]
    linarith

end Combined

end TermBound

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! The pointwise (in the fast variable) mixed-jet bound of the explicit source coefficient. -/

section
section BoundPt
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem norm_iteratedFDeriv_proj_le {g : Vec 2 → Vec 2} {i : ℕ} {X : Vec 2}
    (hg : ContDiff ℝ (i : ℕ∞) g) (k : Fin 2) :
    ‖iteratedFDeriv ℝ i (fun Y => g Y k) X‖ ≤ ‖iteratedFDeriv ℝ i g X‖ := by
  have hP : ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      rw [one_mul]; exact norm_le_pi_norm g k
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).norm_iteratedFDeriv_comp_left
    (hg.contDiffAt (x := X)) (n := i) (by exact_mod_cast le_rfl)
  refine this.trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ i g X‖ := by gcongr
    _ = _ := one_mul _

/-- The sum of the mixed jets of the `u`-component of `Φ`. -/
def srcBtot (Φ : Vec 2 → Vec 2 → ∀ i, h i) (u : ι) (X : Vec 2) (p q j : ℕ) (z : Vec 2) : ℝ :=
  ∑ a ∈ Finset.range (p + j + 1), ∑ b ∈ Finset.range (q + D + 1),
    srcJp (fun X z => Φ X z u) X a b z

/-- The real pointwise majorant. -/
def srcBoundReal (edge : ConstituentEdges D h) (t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i)
    (p q j : ℕ) (X : Vec 2) (v : ι) (z : Vec 2) : ℝ :=
  ∑ u : ι, ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ => ‖γ.map‖ *
    (∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (p + 2),
      ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖) * srcBtot (D := D) Φ u X p q j z).sum

end BoundPt
end

/-! **The mixed-jet bound of the source coefficients.** For a box-smooth `Φ` and fast independent
edge coefficients, the `L²(unit cube)` mixed jets of `𝒮_j Φ` at `X` are bounded by the mixed jets of
`Φ` at `X`, weighted by the slow jets of the edge coefficients at `X` and the norms of the
component maps (`srcPtJet_sourceCoeff_le_box`); and `𝒮_j Φ = 0` for `j > D`. -/

section
section Norms

theorem eLpNorm_fun_sum_le {κ : Type*} (s : Finset κ) (f : κ → Vec 2 → ℝ) (μ : Measure (Vec 2)) :
    eLpNorm (fun z => ∑ x ∈ s, f x z) 2 μ ≤ ∑ x ∈ s, eLpNorm (f x) 2 μ := by
  have : (fun z => ∑ x ∈ s, f x z) = ∑ x ∈ s, f x := by
    funext z; simp [Finset.sum_apply]
  rw [this]
  exact eLpNorm_sum_le (by norm_num)

theorem eLpNorm_fun_list_sum_le {κ : Type*} (l : List κ) (f : κ → Vec 2 → ℝ)
    (μ : Measure (Vec 2)) :
    eLpNorm (fun z => (l.map fun x => f x z).sum) 2 μ ≤ (l.map fun x => eLpNorm (f x) 2 μ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : (fun z => ((a :: l).map fun x => f x z).sum) =
        f a + fun z => (l.map fun x => f x z).sum := by
      funext z; simp
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    simp only [List.map_cons, List.sum_cons]
    gcongr

theorem eLpNorm_const_mul_le (c : ℝ) (g : Vec 2 → ℝ) (μ : Measure (Vec 2)) :
    eLpNorm (fun z => c * g z) 2 μ = ‖c‖ₑ * eLpNorm g 2 μ := by
  have := eLpNorm_const_smul (μ := μ) (p := 2) c g
  simpa [Pi.smul_def] using this

end Norms

section Bound
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The `ENNReal` majorant. -/
def srcBoundE (edge : ConstituentEdges D h) (t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i)
    (p q j : ℕ) (X : Vec 2) (v : ι) : ℝ≥0∞ :=
  ∑ u : ι, ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ => ‖γ.map‖ₑ *
    (∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (p + 2),
      ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖ₑ) *
    ∑ a ∈ Finset.range (p + j + 1), ∑ b ∈ Finset.range (q + D + 1),
      srcPtJet (fun X z => Φ X z u) X a b).sum

theorem eLpNorm_srcBoundReal_le (edge : ConstituentEdges D h) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (p q j : ℕ) (X : Vec 2) (v : ι) :
    eLpNorm (srcBoundReal edge t Φ p q j X v) 2 (volume.restrict AVenhance.unitCube) ≤
      srcBoundE edge t Φ p q j X v := by
  set μ := volume.restrict AVenhance.unitCube with hμ
  have hfun : srcBoundReal edge t Φ p q j X v = fun z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ‖γ.map‖ *
        (∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (p + 2),
          ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖) *
          srcBtot (D := D) Φ u X p q j z).sum := rfl
  rw [hfun]
  refine (eLpNorm_fun_sum_le _ _ μ).trans ?_
  refine Finset.sum_le_sum fun u _ => ?_
  refine (eLpNorm_fun_sum_le _ _ μ).trans ?_
  refine Finset.sum_le_sum fun d _ => ?_
  refine (eLpNorm_fun_list_sum_le _ _ μ).trans ?_
  refine List.sum_le_sum fun γ _ => ?_
  rw [eLpNorm_const_mul_le]
  have hS : 0 ≤ ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (p + 2),
      ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc : ‖‖γ.map‖ * ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (p + 2),
      ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖‖ₑ = ‖γ.map‖ₑ *
      ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (p + 2),
        ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖ₑ := by
    rw [Real.enorm_of_nonneg (mul_nonneg (norm_nonneg _) hS), ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm, ENNReal.ofReal_sum_of_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
    simp [ofReal_norm]
  rw [hc]
  refine mul_le_mul' le_rfl ?_
  unfold srcBtot
  refine (eLpNorm_fun_sum_le _ _ μ).trans ?_
  refine Finset.sum_le_sum fun a _ => ?_
  refine (eLpNorm_fun_sum_le _ _ μ).trans ?_
  exact le_rfl

end Bound
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization Filter Topology
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! Measurability in the time variable: measurability of the time derivative of a time dependent
scalar coefficient, the mixed partial words of a time dependent field, and the class `MixSpan` of
families that are finite real linear combinations of mixed partial words. -/

section
section Time

theorem aemeasurable_fderiv_time {μ : Measure (ℝ × Vec 2)} (a : ℝ → Vec 2 → ℝ) (X e : Vec 2)
    (ha : ∀ Y, Measurable (fun t => a t Y)) (hd : ∀ᵐ p ∂μ, DifferentiableAt ℝ (a p.1) X) :
    AEMeasurable (fun p : ℝ × Vec 2 => fderiv ℝ (a p.1) X e) μ := by
  refine aemeasurable_of_tendsto_metrizable_ae'
    (f := fun (n : ℕ) (p : ℝ × Vec 2) =>
      ((n : ℝ) + 1) * (a p.1 (X + (1 / ((n : ℝ) + 1)) • e) - a p.1 X)) (fun n => ?_) ?_
  · exact ((((ha _).comp measurable_fst).sub ((ha X).comp measurable_fst)).const_mul _).aemeasurable
  · filter_upwards [hd] with p hp
    have hl : HasDerivAt (fun s : ℝ => X + s • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add X
    have h1 : HasDerivAt (fun s : ℝ => a p.1 (X + s • e)) (fderiv ℝ (a p.1) X e) 0 := by
      have hp' : HasFDerivAt (a p.1) (fderiv ℝ (a p.1) X) (X + (0 : ℝ) • e) := by
        simpa using hp.hasFDerivAt
      exact hp'.comp_hasDerivAt (0 : ℝ) hl
    have h2 := hasDerivAt_iff_tendsto_slope_zero.mp h1
    have h3 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity⟩
    refine (h2.comp h3).congr fun n => ?_
    simp only [Function.comp_apply, zero_add, smul_eq_mul, zero_smul, add_zero]
    rw [one_div, inv_inv]

end Time

section Mixed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One mixed partial derivative: `true` is slow, `false` is fast. -/
def mixedStep (b : Bool × Fin 2) (Ψ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  if b.1 then slowPartial b.2 Ψ else fastPartial b.2 Ψ

/-- The mixed partial word (first letter applied first). -/
def mixed (w : List (Bool × Fin 2)) (Ψ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  w.foldl (fun Ψ' b => mixedStep b Ψ') Ψ

theorem mixed_nil (Ψ : Vec 2 → Vec 2 → E) : mixed [] Ψ = Ψ := rfl

theorem mixed_append_single (w : List (Bool × Fin 2)) (b : Bool × Fin 2) (Ψ : Vec 2 → Vec 2 → E) :
    mixed (w ++ [b]) Ψ = mixedStep b (mixed w Ψ) := by
  simp [mixed, List.foldl_append]

theorem isBoxSmooth_mixed (w : List (Bool × Fin 2)) {Ψ : Vec 2 → Vec 2 → E} {s : ℕ}
    (hΨ : IsBoxSmooth s s Ψ) (hw : w.length ≤ s) :
    IsBoxSmooth (s - w.length) (s - w.length) (mixed w Ψ) := by
  induction w using List.reverseRecOn with
  | nil => simpa [mixed_nil] using hΨ
  | append_singleton w b ih =>
    simp only [List.length_append, List.length_singleton] at hw ⊢
    have ih' := ih (by omega)
    obtain ⟨m, hm⟩ : ∃ m, s - w.length = m + 1 := ⟨s - w.length - 1, by omega⟩
    rw [hm] at ih'
    rw [mixed_append_single]
    have e : s - (w.length + 1) = m := by omega
    rw [e]
    unfold mixedStep
    cases b.1
    · exact isBoxSmooth_fastPartial_step ih' b.2
    · exact isBoxSmooth_slowPartial_step ih' b.2

end Mixed
end

/-! The class `MixSpan` of time dependent fields that are finite real linear combinations of mixed
partial words of a given family `Φ`, closed under the partial derivatives, and its measurability. -/

section
section Span
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fastPartial_smul_const' (c : ℝ) {F : Vec 2 → Vec 2 → E} (k : Fin 2) (X z : Vec 2)
    (hF : DifferentiableAt ℝ (F X) z) :
    fastPartial k (fun X z => c • F X z) X z = c • fastPartial k F X z := by
  simp only [fastPartial]
  rw [fderiv_fun_const_smul hF]
  rfl

theorem slowPartial_smul_const' (c : ℝ) {F : Vec 2 → Vec 2 → E} (k : Fin 2) (X z : Vec 2)
    (hF : DifferentiableAt ℝ (fun X' => F X' z) X) :
    slowPartial k (fun X z => c • F X z) X z = c • slowPartial k F X z := by
  simp only [slowPartial]
  rw [fderiv_fun_const_smul hF]
  rfl

/-- Finite real linear combinations of mixed partial words (of length `≤ n`) of `Φ`, for the
times `t ∈ I`. -/
def MixSpan (I : Set ℝ) (Φ : ℝ → Vec 2 → Vec 2 → E) (n : ℕ) (G : ℝ → Vec 2 → Vec 2 → E) : Prop :=
  ∃ l : List (ℝ × List (Bool × Fin 2)), (∀ cw ∈ l, cw.2.length ≤ n) ∧
    ∀ t ∈ I, ∀ X z, G t X z = (l.map fun cw => cw.1 • mixed cw.2 (Φ t) X z).sum

variable {I : Set ℝ} {Φ : ℝ → Vec 2 → Vec 2 → E}

theorem MixSpan.base : MixSpan I Φ 0 Φ :=
  ⟨[(1, [])], by simp, fun t _ X z => by simp [mixed_nil]⟩

theorem MixSpan.zero (n : ℕ) : MixSpan I Φ n (fun _ _ _ => 0) :=
  ⟨[], by simp, fun t _ X z => by simp⟩

theorem MixSpan.add {n : ℕ} {G G' : ℝ → Vec 2 → Vec 2 → E} (h : MixSpan I Φ n G)
    (h' : MixSpan I Φ n G') : MixSpan I Φ n (fun t X z => G t X z + G' t X z) := by
  obtain ⟨l, hl, hG⟩ := h
  obtain ⟨l', hl', hG'⟩ := h'
  refine ⟨l ++ l', fun cw hcw => ?_, fun t ht X z => ?_⟩
  · rcases List.mem_append.mp hcw with h1 | h1
    exacts [hl cw h1, hl' cw h1]
  · beta_reduce
    rw [hG t ht X z, hG' t ht X z, List.map_append, List.sum_append]

theorem MixSpan.const_smul {n : ℕ} {G : ℝ → Vec 2 → Vec 2 → E} (h : MixSpan I Φ n G) (c : ℝ) :
    MixSpan I Φ n (fun t X z => c • G t X z) := by
  obtain ⟨l, hl, hG⟩ := h
  refine ⟨l.map fun cw => (c * cw.1, cw.2), fun cw hcw => ?_, fun t ht X z => ?_⟩
  · obtain ⟨cw', h1, rfl⟩ := List.mem_map.mp hcw
    exact hl cw' h1
  · beta_reduce
    rw [hG t ht X z, List.map_map, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun cw _ => ?_
    simp [smul_smul]

theorem MixSpan.mono {n n' : ℕ} (hn : n ≤ n') {G : ℝ → Vec 2 → Vec 2 → E} (h : MixSpan I Φ n G) :
    MixSpan I Φ n' G := by
  obtain ⟨l, hl, hG⟩ := h
  exact ⟨l, fun cw hcw => (hl cw hcw).trans hn, hG⟩

variable {s : ℕ} (hΦ : ∀ t ∈ I, IsBoxSmooth s s (Φ t))
include hΦ

theorem MixSpan.fast {n : ℕ} (hn : n + 1 ≤ s) {G : ℝ → Vec 2 → Vec 2 → E} (h : MixSpan I Φ n G)
    (k : Fin 2) : MixSpan I Φ (n + 1) (fun t => fastPartial k (G t)) := by
  obtain ⟨l, hl, hG⟩ := h
  refine ⟨l.map fun cw => (cw.1, cw.2 ++ [(false, k)]), fun cw hcw => ?_, fun t ht X z => ?_⟩
  · obtain ⟨cw', h1, rfl⟩ := List.mem_map.mp hcw
    simpa using Nat.succ_le_succ (hl cw' h1)
  · beta_reduce
    have hF : G t = fun X z => (l.map fun cw => cw.1 • mixed cw.2 (Φ t) X z).sum :=
      funext fun X => funext fun z => hG t ht X z
    have hdiff : ∀ cw ∈ l, DiffF (mixed cw.2 (Φ t)) := fun cw hcw =>
      IsBoxSmooth.diffF (isBoxSmooth_mixed cw.2 (hΦ t ht) (by have := hl cw hcw; omega))
        (by have := hl cw hcw; omega) (by have := hl cw hcw; omega)
    rw [hF, fastPartial_list_sum l (fun cw hcw => (hdiff cw hcw).const_smul cw.1) k X z,
      List.map_map]
    congr 1
    refine List.map_congr_left fun cw hcw => ?_
    simp only [Function.comp_apply]
    rw [fastPartial_smul_const' cw.1 k X z ((hdiff cw hcw).1 X z), mixed_append_single]
    simp [mixedStep]

theorem MixSpan.slow {n : ℕ} (hn : n + 1 ≤ s) {G : ℝ → Vec 2 → Vec 2 → E} (h : MixSpan I Φ n G)
    (k : Fin 2) : MixSpan I Φ (n + 1) (fun t => slowPartial k (G t)) := by
  obtain ⟨l, hl, hG⟩ := h
  refine ⟨l.map fun cw => (cw.1, cw.2 ++ [(true, k)]), fun cw hcw => ?_, fun t ht X z => ?_⟩
  · obtain ⟨cw', h1, rfl⟩ := List.mem_map.mp hcw
    simpa using Nat.succ_le_succ (hl cw' h1)
  · beta_reduce
    have hF : G t = fun X z => (l.map fun cw => cw.1 • mixed cw.2 (Φ t) X z).sum :=
      funext fun X => funext fun z => hG t ht X z
    have hdiff : ∀ cw ∈ l, DiffF (mixed cw.2 (Φ t)) := fun cw hcw =>
      IsBoxSmooth.diffF (isBoxSmooth_mixed cw.2 (hΦ t ht) (by have := hl cw hcw; omega))
        (by have := hl cw hcw; omega) (by have := hl cw hcw; omega)
    rw [hF, slowPartial_list_sum l (fun cw hcw => (hdiff cw hcw).const_smul cw.1) k X z,
      List.map_map]
    congr 1
    refine List.map_congr_left fun cw hcw => ?_
    simp only [Function.comp_apply]
    rw [slowPartial_smul_const' cw.1 k X z ((hdiff cw hcw).2 z X), mixed_append_single]
    simp [mixedStep]

end Span
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! **Joint measurability in `(t, z)` of the source coefficients.** -/

section
section Aesm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Φ : ℝ → Vec 2 → Vec 2 → E} {I : Set ℝ}

theorem MixSpan.aesm {μ : Measure (ℝ × Vec 2)} (hI : ∀ᵐ p ∂μ, p.1 ∈ I) {n : ℕ}
    {G : ℝ → Vec 2 → Vec 2 → E} (hG : MixSpan I Φ n G)
    (hΦm : ∀ w : List (Bool × Fin 2), w.length ≤ n → ∀ X,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => mixed w (Φ p.1) X p.2) μ) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => G p.1 X p.2) μ := by
  obtain ⟨l, hl, hG⟩ := hG
  have hae : ∀ᵐ p ∂μ, (l.map fun cw => cw.1 • mixed cw.2 (Φ p.1) X p.2).sum = G p.1 X p.2 :=
    hI.mono fun p hp => (hG p.1 hp X p.2).symm
  refine AEStronglyMeasurable.congr ?_ hae
  clear hae hG
  induction l with
  | nil => simpa using aestronglyMeasurable_const
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hΦm a.2 (hl a List.mem_cons_self) X).const_smul a.1).add
      (ih fun cw hcw => hl cw (List.mem_cons_of_mem _ hcw))

end Aesm

section SeqSpan
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Φ : ℝ → Vec 2 → Vec 2 → E} {I : Set ℝ} {s : ℕ} (hΦ : ∀ t ∈ I, IsBoxSmooth s s (Φ t))
include hΦ

theorem mixSpan_seqWord (η : ℝ) (l : List (Fin 2)) (hl : l.length ≤ s) (i : ℕ) :
    MixSpan I Φ l.length (fun t => seqWord η l (Φ t) i) := by
  induction l using List.reverseRecOn generalizing i with
  | nil =>
    cases i with
    | zero => exact MixSpan.base
    | succ j => exact MixSpan.zero 0
  | append_singleton l k ih =>
    simp only [List.length_append, List.length_singleton] at hl ⊢
    have ih' := fun i => ih (by omega) i
    have e : (fun t => seqWord η (l ++ [k]) (Φ t) i) =
        fun t => seqStep η k (seqWord η l (Φ t)) i := by
      funext t; rw [seqWord_concat]
    rw [e]
    cases i with
    | zero => exact MixSpan.fast hΦ (by omega) (ih' 0) k
    | succ j =>
      exact (MixSpan.fast hΦ (by omega) (ih' (j + 1)) k).add
        ((MixSpan.slow hΦ (by omega) (ih' j) k).const_smul (Real.sqrt η))

end SeqSpan

section Terms
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] {Φ : ℝ → Vec 2 → Vec 2 → E₁} {I : Set ℝ} {s : ℕ}

theorem aesm_srcTerm_time {μ : Measure (ℝ × Vec 2)} (hI : ∀ᵐ p ∂μ, p.1 ∈ I) (η : ℝ) (k : Fin 2)
    {a : ℝ → Vec 2 → ℝ} (ha_meas : ∀ Y, Measurable fun t => a t Y)
    (ha_diff : ∀ t ∈ I, Differentiable ℝ (a t)) (L : E₁ →L[ℝ] E₂)
    (hΦ : ∀ t ∈ I, IsBoxSmooth s s (Φ t)) (l : List (Fin 2)) (hl : l.length + 1 ≤ s)
    (hΦm : ∀ w : List (Bool × Fin 2), w.length ≤ l.length + 1 → ∀ X,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => mixed w (Φ p.1) X p.2) μ) (J : ℕ) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      srcTerm η k (a p.1) L (seqWord η l (Φ p.1)) J X p.2) μ := by
  have hA : AEStronglyMeasurable (fun p : ℝ × Vec 2 => a p.1 X) μ :=
    ((ha_meas X).comp measurable_fst).aestronglyMeasurable
  have hlin : ∀ {G : ℝ × Vec 2 → E₁}, AEStronglyMeasurable G μ →
      AEStronglyMeasurable (fun p => L (G p)) μ := fun hG => L.continuous.comp_aestronglyMeasurable hG
  have hW : ∀ i, AEStronglyMeasurable (fun p : ℝ × Vec 2 => seqWord η l (Φ p.1) i X p.2) μ :=
    fun i => ((mixSpan_seqWord hΦ η l (by omega) i).mono (Nat.le_succ _)).aesm hI
      (fun w hw => hΦm w (by omega)) X
  have hF : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => fastPartial k (seqWord η l (Φ p.1) i) X p.2) μ := fun i =>
    (MixSpan.fast hΦ hl (mixSpan_seqWord hΦ η l (by omega) i) k).aesm hI hΦm X
  have hS : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => slowPartial k (seqWord η l (Φ p.1) i) X p.2) μ := fun i =>
    (MixSpan.slow hΦ hl (mixSpan_seqWord hΦ η l (by omega) i) k).aesm hI hΦm X
  have hD : AEStronglyMeasurable (fun p : ℝ × Vec 2 => fderiv ℝ (a p.1) X (basisVec k)) μ :=
    (aemeasurable_fderiv_time a X (basisVec k) ha_meas
      (hI.mono fun p hp => (ha_diff p.1 hp) X)).aestronglyMeasurable
  cases J with
  | zero => exact hA.smul (hlin (hF 0))
  | succ J =>
    exact (hA.smul (hlin (hF (J + 1)))).add
      (((hD.smul (hlin (hW J))).add (hA.smul (hlin (hS J)))).const_smul _)

end Terms

section Final
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem aesm_list_sum {α κ E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    (l : List κ) {f : κ → α → E} (hf : ∀ x ∈ l, AEStronglyMeasurable (f x) μ) :
    AEStronglyMeasurable (fun a => (l.map fun x => f x a).sum) μ := by
  induction l with
  | nil => simpa using aestronglyMeasurable_const
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a List.mem_cons_self).add (ih fun x hx => hf x (List.mem_cons_of_mem _ hx))

/-- **Joint measurability of the source coefficients in `(t, z)`.** Let `μ` be a measure on
`(t, z)` carried by the times `t ∈ I` at which every edge coefficient is fast independent and
`C¹` in `X`; let `Φ t` be box smooth of order `s ≥ D` for `t ∈ I`; let every `γ.coeff α t X 0` be
measurable in `t`; and let every mixed partial word (of length `≤ D`, slow letters `true`, fast
letters `false`, first letter applied first) of each component `Φ t · · u` be jointly
a.e.-strongly measurable in `(t, z)`. Then `(t, z) ↦ 𝒮_j(Φ t)(X, z)_v` is a.e.-strongly
measurable. -/
theorem aesm_sourceCoeff_time (edge : ConstituentEdges D h) (η : ℝ) {I : Set ℝ}
    {μ : Measure (ℝ × Vec 2)} (hI : ∀ᵐ p ∂μ, p.1 ∈ I)
    (hquiet : ∀ t ∈ I, ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ t ∈ I, ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    (hcoef : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α Y, Measurable fun t => γ.coeff α t Y 0)
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : ∀ t ∈ I, IsBoxSmooth s s (Φ t))
    (hDs : D ≤ s)
    (hΦm : ∀ (u : ι) (w : List (Bool × Fin 2)), w.length ≤ D → ∀ X,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
        mixed w (fun X' z' => Φ p.1 X' z' u) X p.2) μ)
    (j : ℕ) (X : Vec 2) (v : ι) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      sourceCoeff edge η j p.1 (Φ p.1) X p.2 v) μ := by
  have hae : ∀ᵐ p ∂μ, srcCoef edge η p.1 (Φ p.1) j X p.2 v =
      sourceCoeff edge η j p.1 (Φ p.1) X p.2 v := hI.mono fun p hp => by
    rw [sourceCoeff_eq_srcCoef edge η p.1 (hquiet p.1 hp) (hsm p.1 hp) (hΦ p.1 hp) hDs j]
  refine AEStronglyMeasurable.congr ?_ hae
  have hΦu : ∀ u : ι, ∀ t ∈ I, IsBoxSmooth s s (fun X z => Φ t X z u) := fun u t ht =>
    (hΦ t ht).map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  have hk : ∀ k : Fin 2, ∀ u : ι, ∀ d : Finset.Icc 2 D, ∀ γ ∈ edge v u d,
      ∀ α : DerivativeWord2 (d.1 - 1), AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
        srcTerm η k (fun Y => γ.coeff α p.1 Y 0 k) γ.map (srcW η u α (Φ p.1)) j X p.2) μ := by
    intro k u d γ hγ α
    have hd := Finset.mem_Icc.mp d.2
    exact aesm_srcTerm_time (Φ := fun t X z => Φ t X z u) hI η k
      (a := fun t Y => γ.coeff α t Y 0 k)
      (fun Y => (measurable_pi_apply k).comp (hcoef v u d γ hγ α Y))
      (fun t ht => ((contDiff_pi.mp (hsm t ht v u d γ hγ α 0)) k).differentiable one_ne_zero)
      γ.map (hΦu u) (List.ofFn α) (by simp only [List.length_ofFn]; omega)
      (fun w hw => hΦm u w (by simp only [List.length_ofFn] at hw; omega)) j X
  simp only [srcCoef, NS]
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun u _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun d _ => ?_
  refine aesm_list_sum _ fun γ hγ => ?_
  exact Finset.aestronglyMeasurable_fun_sum _ fun α _ => hk k u d γ hγ α

end Final
end

/-! **Box-smooth variants** (slow order `sX`, fast order `sZ`, with only `p + D ≤ sX` and
`q + D ≤ sZ`) of the mixed-jet bound of the source coefficients and of the explicit
representation, vanishing and time measurability (the latter three only need
`D ≤ sX` and `D ≤ sZ`, by monotonicity of `IsBoxSmooth`). -/

section
section BoundBox
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem srcJp_term_le_box (η t : ℝ) (hη : Real.sqrt η ≤ 1)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) {p q j : ℕ}
    (hX : p + D ≤ sX) (hZ : q + D ≤ sZ) {v u : ι} {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)}
    (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2)
    (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0)) (X z : Vec 2) :
    srcJp (srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) X p q z ≤
      3 * 2 ^ p * 2 ^ D * (‖γ.map‖ *
        (∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖) *
        srcBtot (D := D) Φ u X p q j z) := by
  have hd := Finset.mem_Icc.mp d.2
  have hak : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0 k) :=
    contDiff_pi.mp ha k
  have h1 : IsBoxSmooth sX sZ (fun X z => Φ X z u) :=
    hΦ.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  have hW : ∀ i, IsBoxSmooth (p + 1) (q + 1) (srcW η u α Φ i) := fun i => by
    have := isBoxSmooth_seqWord_box η (List.ofFn α) h1 (by simp only [List.length_ofFn]; omega)
      (by simp only [List.length_ofFn]; omega) i
    exact (by simpa [srcW] using this : IsBoxSmooth (sX - min i (d.1 - 1)) (sZ - ((d.1 - 1) - i))
      (srcW η u α Φ i)).mono (by omega) (by omega)
  have hJ : ∀ i p' q', p' ≤ p + 1 → q' ≤ q + 1 → srcJp (srcW η u α Φ i) X p' q' z ≤
      2 ^ (d.1 - 1) * srcJp (fun X z => Φ X z u) X (p' + i) (q' + (d.1 - 1) - i) z :=
    fun i p' q' hp hq => by
    have := srcJp_seqWord_le_box η hη (List.ofFn α) h1 p' q'
      (by simp only [List.length_ofFn]; omega) (by simp only [List.length_ofFn]; omega) i X z
    simpa [srcW] using this
  have key := srcJp_srcTerm_le_box (k := k) (p := p) (q := q) (m := d.1 - 1) η hη hak
    γ.map hW (fun a b => srcJp (fun X z => Φ X z u) X a b z)
    (fun a b => srcJp_nonneg _ _ _ _ _) X z hJ j
  refine key.trans ?_
  have hA : ∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0 k) X‖ ≤
      ∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖ :=
    Finset.sum_le_sum fun i hi => norm_iteratedFDeriv_proj_le
      (ha.of_le (by exact_mod_cast (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi :
        i ≤ p + 1))) k
  have hB : ∑ a' ∈ Finset.range (p + j + 1), ∑ b' ∈ Finset.range (q + (d.1 - 1) + 2),
      srcJp (fun X z => Φ X z u) X a' b' z ≤ srcBtot (D := D) Φ u X p q j z :=
    Finset.sum_le_sum fun a' _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) fun _ _ _ => srcJp_nonneg _ _ _ _ _
  have h2 : (2 : ℝ) ^ (d.1 - 1) ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0 k) X‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0 : 0 ≤ ∑ a' ∈ Finset.range (p + j + 1), ∑ b' ∈ Finset.range (q + (d.1 - 1) + 2),
      srcJp (fun X z => Φ X z u) X a' b' z :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => srcJp_nonneg _ _ _ _ _
  have hL := norm_nonneg γ.map
  calc _ = 3 * 2 ^ p * 2 ^ (d.1 - 1) * ‖γ.map‖ * (∑ i ∈ Finset.range (p + 2),
        ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0 k) X‖) * (∑ a' ∈ Finset.range (p + j + 1),
        ∑ b' ∈ Finset.range (q + (d.1 - 1) + 2), srcJp (fun X z => Φ X z u) X a' b' z) := rfl
    _ ≤ 3 * 2 ^ p * 2 ^ D * ‖γ.map‖ * (∑ i ∈ Finset.range (p + 2),
        ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖) * srcBtot (D := D) Φ u X p q j z := by
      gcongr
    _ = _ := by ring

theorem regBox_srcTerm_box_src (η : ℝ) {t : ℝ} {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ}
    (hΦ : IsBoxSmooth sX sZ Φ) {p q : ℕ} (hX : p + D ≤ sX) (hZ : q + D ≤ sZ) {v u : ι}
    {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)} (α : DerivativeWord2 (d.1 - 1))
    (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0)) (k : Fin 2) (j : ℕ) :
    RegBox p q (srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) := by
  have hd := Finset.mem_Icc.mp d.2
  have h1 : IsBoxSmooth sX sZ (fun X z => Φ X z u) :=
    hΦ.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  refine regBox_srcTerm_box η (contDiff_pi.mp ha k) γ.map (fun i => ?_) j
  have := isBoxSmooth_seqWord_box η (List.ofFn α) h1 (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) i
  exact (by simpa [srcW] using this : IsBoxSmooth (sX - min i (d.1 - 1)) (sZ - ((d.1 - 1) - i))
    (srcW η u α Φ i)).mono (by omega) (by omega)

theorem jcont_srcTerm_box_src (η : ℝ) {t : ℝ} {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ}
    (hΦ : IsBoxSmooth sX sZ Φ) {p q : ℕ} (hX : p + D ≤ sX) (hZ : q + D ≤ sZ) {v u : ι}
    {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)} (α : DerivativeWord2 (d.1 - 1))
    (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0)) (k : Fin 2) (j : ℕ)
    (X : Vec 2) :
    JCont (srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) X p q := by
  have hd := Finset.mem_Icc.mp d.2
  have h1 : IsBoxSmooth sX sZ (fun X z => Φ X z u) :=
    hΦ.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  refine jcont_srcTerm_box η (contDiff_pi.mp ha k) γ.map (fun i => ?_) j X
  have := isBoxSmooth_seqWord_box η (List.ofFn α) h1 (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) i
  exact (by simpa [srcW] using this : IsBoxSmooth (sX - min i (d.1 - 1)) (sZ - ((d.1 - 1) - i))
    (srcW η u α Φ i)).mono (by omega) (by omega)

theorem srcJp_srcCoef_le_box (edge : ConstituentEdges D h) (η t : ℝ) (hη : Real.sqrt η ≤ 1)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) {p q : ℕ} (j : ℕ)
    (hX : p + D ≤ sX) (hZ : q + D ≤ sZ)
    (ha : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0)) (X z : Vec 2) (v : ι) :
    srcJp (fun X z => srcCoef edge η t Φ j X z v) X p q z ≤
      6 * 2 ^ (p + D) * srcBoundReal edge t Φ p q j X v z := by
  have hreg : ∀ k : Fin 2, ∀ u d, ∀ γ ∈ edge v u d, ∀ α, RegBox p q
      (srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) := fun k u d γ hγ α =>
    regBox_srcTerm_box_src η hΦ hX hZ α (ha v u d γ hγ α) k j
  have hNS : ∀ k : Fin 2, RegBox p q (NS edge v (fun u d γ α =>
      srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j)) := fun k =>
    NS.regBox edge v (hreg k)
  have hfield : (fun X z => srcCoef edge η t Φ j X z v) = fun X z => ∑ k ∈ Finset.univ,
      NS edge v (fun u d γ α =>
        srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) X z := rfl
  rw [hfield]
  refine (srcJp_sum _ (fun k _ => hNS k) le_rfl le_rfl X z).trans ?_
  have hk : ∀ k : Fin 2, srcJp (NS edge v (fun u d γ α =>
      srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j)) X p q z ≤
      3 * 2 ^ p * 2 ^ D * srcBoundReal edge t Φ p q j X v z := by
    intro k
    refine (NS.srcJp_le edge v (hreg k) le_rfl le_rfl X z).trans ?_
    unfold srcBoundReal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← List.sum_map_mul_left]
    refine List.sum_le_sum fun γ hγ => ?_
    calc _ ≤ ∑ α : DerivativeWord2 (d.1 - 1), 3 * 2 ^ p * 2 ^ D * (‖γ.map‖ *
          (∑ i ∈ Finset.range (p + 2), ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α t Y 0) X‖) *
          srcBtot (D := D) Φ u X p q j z) :=
        Finset.sum_le_sum fun α _ =>
          srcJp_term_le_box η t hη hΦ hX hZ α k (ha v u d γ hγ α) X z
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  calc _ ≤ ∑ k : Fin 2, 3 * 2 ^ p * 2 ^ D * srcBoundReal edge t Φ p q j X v z :=
        Finset.sum_le_sum fun k _ => hk k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [pow_add]; push_cast; ring

theorem jcont_srcCoef_box (edge : ConstituentEdges D h) (η t : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) {p q : ℕ} (j : ℕ)
    (hX : p + D ≤ sX) (hZ : q + D ≤ sZ)
    (ha : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0)) (X : Vec 2) (v : ι) :
    JCont (fun X z => srcCoef edge η t Φ j X z v) X p q := by
  have hreg : ∀ k : Fin 2, ∀ u d, ∀ γ ∈ edge v u d, ∀ α, RegBox p q
      (srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) := fun k u d γ hγ α =>
    regBox_srcTerm_box_src η hΦ hX hZ α (ha v u d γ hγ α) k j
  have hNS : ∀ k : Fin 2, RegBox p q (NS edge v (fun u d γ α =>
      srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j)) := fun k =>
    NS.regBox edge v (hreg k)
  have hfield : (fun X z => srcCoef edge η t Φ j X z v) = fun X z => ∑ k ∈ Finset.univ,
      NS edge v (fun u d γ α =>
        srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) X z := rfl
  rw [hfield]
  exact JCont.sum _ (fun k _ => hNS k) le_rfl le_rfl fun k _ =>
    NS.jcont edge v (hreg k) le_rfl le_rfl fun u d γ hγ α =>
      jcont_srcTerm_box_src η hΦ hX hZ α (ha v u d γ hγ α) k j X

/-- **Representation under box smoothness**: only `D ≤ sX` and `D ≤ sZ` are needed. -/
theorem sourceCoeff_eq_srcCoef_box (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) (hX : D ≤ sX)
    (hZ : D ≤ sZ) (j : ℕ) : sourceCoeff edge η j t Φ = srcCoef edge η t Φ j :=
  sourceCoeff_eq_srcCoef edge η t hquiet hsm (hΦ.mono hX hZ |>.mono (by omega) (by omega)
    : IsBoxSmooth D D Φ) le_rfl j

/-- **Mixed-jet bound of the source coefficients, box-smooth version.** Slow letters cost slow
order and fast letters cost fast order: only `p + D ≤ sX` and `q + D ≤ sZ` are needed. -/
theorem srcPtJet_sourceCoeff_le_box (edge : ConstituentEdges D h) (η t : ℝ)
    (hη : Real.sqrt η ≤ 1)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) (p q j : ℕ)
    (hX : p + D ≤ sX) (hZ : q + D ≤ sZ)
    (hsmp : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z)) (X : Vec 2) (v : ι) :
    srcPtJet (fun X z => sourceCoeff edge η j t Φ X z v) X p q ≤
      (((6 * 2 ^ (p + D) : ℕ) : ℝ≥0∞)) * srcBoundE edge t Φ p q j X v := by
  have hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    (hsmp v u d γ hγ α z).of_le (by exact_mod_cast Nat.le_add_left 1 p)
  have ha : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0) := fun v u d γ hγ α =>
    hsmp v u d γ hγ α 0
  have e : (fun X z => sourceCoeff edge η j t Φ X z v) =
      fun X z => srcCoef edge η t Φ j X z v := by
    rw [sourceCoeff_eq_srcCoef_box edge η t hquiet hsm hΦ (by omega) (by omega) j]
  rw [e]
  set μ := volume.restrict AVenhance.unitCube with hμ
  have hfm := (jcont_srcCoef_box edge η t hΦ j hX hZ ha X v).aestronglyMeasurable μ
  have hpt : srcPtJet (fun X z => srcCoef edge η t Φ j X z v) X p q =
      eLpNorm (srcJp (fun X z => srcCoef edge η t Φ j X z v) X p q) 2 μ := rfl
  rw [hpt]
  have h1 : eLpNorm (srcJp (fun X z => srcCoef edge η t Φ j X z v) X p q) 2 μ ≤
      eLpNorm (fun z => (6 * 2 ^ (p + D) : ℝ) * srcBoundReal edge t Φ p q j X v z) 2 μ :=
    eLpNorm_mono_real (by simpa [srcJp] using hfm) fun z => by
      rw [Real.norm_of_nonneg (srcJp_nonneg _ _ _ _ _)]
      exact srcJp_srcCoef_le_box edge η t hη hΦ j hX hZ ha X z v
  refine h1.trans ?_
  rw [eLpNorm_const_mul_le]
  have hc : ‖(6 * 2 ^ (p + D) : ℝ)‖ₑ = (((6 * 2 ^ (p + D) : ℕ) : ℝ≥0∞)) := by
    rw [Real.enorm_of_nonneg (by positivity)]
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [hc]
  exact mul_le_mul' le_rfl (eLpNorm_srcBoundReal_le edge t Φ p q j X v)

/-- **Time measurability, box-smooth version**: only `D ≤ sX` and `D ≤ sZ` are needed. -/
theorem aesm_sourceCoeff_time_box (edge : ConstituentEdges D h) (η : ℝ) {I : Set ℝ}
    {μ : Measure (ℝ × Vec 2)} (hI : ∀ᵐ p ∂μ, p.1 ∈ I)
    (hquiet : ∀ t ∈ I, ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ t ∈ I, ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    (hcoef : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α Y, Measurable fun t => γ.coeff α t Y 0)
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : ∀ t ∈ I, IsBoxSmooth sX sZ (Φ t))
    (hX : D ≤ sX) (hZ : D ≤ sZ)
    (hΦm : ∀ (u : ι) (w : List (Bool × Fin 2)), w.length ≤ D → ∀ X,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
        mixed w (fun X' z' => Φ p.1 X' z' u) X p.2) μ)
    (j : ℕ) (X : Vec 2) (v : ι) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      sourceCoeff edge η j p.1 (Φ p.1) X p.2 v) μ :=
  aesm_sourceCoeff_time edge η hI hquiet hsm hcoef (s := D)
    (fun t ht => ((hΦ t ht).mono hX hZ : IsBoxSmooth D D (Φ t))) le_rfl hΦm j X v

end BoundBox
end

end AVRegularity.QuietDecay
end
