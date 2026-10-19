-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVenhance.Infra.Ergodic.Flow
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Chebyshev
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation

@[expose] public section

section
open Homogenization
namespace AVRegularity.ChartTransport

/-! Chart transport: the scale-invariant Faà di Bruno bound.  If the jets of the chart `Ψ` are
normalized at scale `Rχ` and `0 < s ≤ Rχ`, then
`s^n ‖D^n (g ∘ Ψ)(x)‖ ≤ n! D^n ∑_{i ≤ n} s^i ‖D^i g(Ψ x)‖`. -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Rescaling the chart so that its jets are bounded by `D^p`, then applying the Mathlib
Faà di Bruno bound. -/
theorem scaled_comp_bound {g : Vec 2 → G} {Ψ : Vec 2 → Vec 2} {n : ℕ}
    (hg : ContDiff ℝ (n : ℕ∞) g) (hΨ : ContDiff ℝ (n : ℕ∞) Ψ) {D Rχ s : ℝ} (hD : 1 ≤ D)
    (hs : 0 < s) (hsR : s ≤ Rχ) (x : Vec 2)
    (hjet : ∀ p, 1 ≤ p → p ≤ n → ‖iteratedFDeriv ℝ p Ψ x‖ ≤ D * Rχ⁻¹ ^ (p - 1)) :
    s ^ n * ‖iteratedFDeriv ℝ n (g ∘ Ψ) x‖ ≤
      n.factorial * D ^ n * ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖ := by
  have hR : 0 < Rχ := lt_of_lt_of_le hs hsR
  set Ψt : Vec 2 → Vec 2 := fun z => s⁻¹ • Ψ (s • z) with hΨt
  set gt : Vec 2 → G := fun y => g (s • y) with hgt
  have hΨt_c : ContDiff ℝ (n : ℕ∞) Ψt :=
    (hΨ.comp (contDiff_const_smul s)).const_smul s⁻¹
  have hgt_c : ContDiff ℝ (n : ℕ∞) gt := hg.comp (contDiff_const_smul s)
  have hcomp : gt ∘ Ψt = fun z => (g ∘ Ψ) (s • z) := by
    funext z
    simp only [Function.comp, hgt, hΨt, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hgΨ : ContDiff ℝ (n : ℕ∞) (g ∘ Ψ) := hg.comp hΨ
  have hDn := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := n) s hgΨ
  have hDg : ∀ i : ℕ, i ≤ n → iteratedFDeriv ℝ i gt = fun y => s ^ i • iteratedFDeriv ℝ i g (s • y) :=
    fun i hi => iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := i) s (hg.of_le (by exact_mod_cast hi))
  have hDΨ : ∀ p : ℕ, p ≤ n → ∀ z, iteratedFDeriv ℝ p Ψt z =
      s⁻¹ • s ^ p • iteratedFDeriv ℝ p Ψ (s • z) := by
    intro p hp z
    have h1 := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := p) s
      (hΨ.of_le (by exact_mod_cast hp))
    have h2 : iteratedFDeriv ℝ p Ψt z = s⁻¹ • iteratedFDeriv ℝ p (fun z => Ψ (s • z)) z :=
      iteratedFDeriv_const_smul_apply' (a := s⁻¹) (f := fun z => Ψ (s • z)) (x := z) (i := p)
        ((hΨ.of_le (by exact_mod_cast hp)).comp (contDiff_const_smul s)).contDiffAt
    rw [h2, h1]
  have hbound := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := gt) (f := Ψt) (N := (n : ℕ∞))
    (n := n) hgt_c hΨt_c le_rfl (s⁻¹ • x)
    (C := ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖) (D := D)
    (fun i hi => by
      rw [hDg i hi]
      have : Ψt (s⁻¹ • x) = s⁻¹ • Ψ x := by
        simp only [hΨt, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      simp only [this, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, norm_smul,
        Real.norm_eq_abs, abs_of_pos (pow_pos hs i)]
      exact Finset.single_le_sum (f := fun i => s ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖)
        (fun _ _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
    (fun p hp1 hpn => by
      rw [hDΨ p hpn]
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have hq := hjet (q + 1) hp1 hpn
      have e : s • s⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      have e2 : s⁻¹ * s ^ (q + 1) = s ^ q := by
        rw [pow_succ]; field_simp
      rw [smul_smul, e, e2, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hs q)]
      simp only [Nat.add_sub_cancel] at hq
      have h1 : s * Rχ⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]; exact (div_le_one hR).2 hsR
      have hD0 : 0 ≤ D := by linarith
      calc s ^ q * ‖iteratedFDeriv ℝ (q + 1) Ψ x‖ ≤ s ^ q * (D * Rχ⁻¹ ^ q) :=
            mul_le_mul_of_nonneg_left hq (pow_nonneg hs.le q)
        _ = D * (s * Rχ⁻¹) ^ q := by rw [mul_pow]; ring
        _ ≤ D * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) h1) hD0
        _ ≤ D ^ (q + 1) := by rw [mul_one]; exact le_self_pow₀ hD (Nat.succ_ne_zero q))
  rw [hcomp, hDn] at hbound
  have e : s • s⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hs n), e] at hbound
  calc _ ≤ _ := hbound
    _ = _ := by ring

theorem iteratedFDeriv_sub_const_pos {f : Vec 2 → G} {n i : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (hi : i ≤ n) (hi0 : i ≠ 0) (c : G) (y : Vec 2) :
    iteratedFDeriv ℝ i (fun z => f z - c) y = iteratedFDeriv ℝ i f y := by
  have h1 : ContDiffAt ℝ (i : ℕ∞) f y := (hf.of_le (by exact_mod_cast hi)).contDiffAt
  have h2 : ContDiffAt ℝ (i : ℕ∞) (fun _ : Vec 2 => c) y := contDiffAt_const
  have := iteratedFDeriv_sub_apply (𝕜 := ℝ) h1 h2
  have e : (fun z => f z - c) = f - fun _ => c := rfl
  rw [e, this, iteratedFDeriv_const_of_ne hi0]
  simp

/-- The version without the zeroth-order term, for orders `n ≥ 1`. -/
theorem scaled_comp_bound_pos {g : Vec 2 → G} {Ψ : Vec 2 → Vec 2} {n : ℕ} (hn : 1 ≤ n)
    (hg : ContDiff ℝ (n : ℕ∞) g) (hΨ : ContDiff ℝ (n : ℕ∞) Ψ) {D Rχ s : ℝ} (hD : 1 ≤ D)
    (hs : 0 < s) (hsR : s ≤ Rχ) (x : Vec 2)
    (hjet : ∀ p, 1 ≤ p → p ≤ n → ‖iteratedFDeriv ℝ p Ψ x‖ ≤ D * Rχ⁻¹ ^ (p - 1)) :
    s ^ n * ‖iteratedFDeriv ℝ n (g ∘ Ψ) x‖ ≤
      n.factorial * D ^ n *
        ∑ i ∈ Finset.range n, s ^ (i + 1) * ‖iteratedFDeriv ℝ (i + 1) g (Ψ x)‖ := by
  set c : G := g (Ψ x) with hc
  have hg' : ContDiff ℝ (n : ℕ∞) (fun y => g y - c) := hg.sub contDiff_const
  have h := scaled_comp_bound hg' hΨ hD hs hsR x hjet
  have e1 : iteratedFDeriv ℝ n ((fun y => g y - c) ∘ Ψ) x = iteratedFDeriv ℝ n (g ∘ Ψ) x := by
    have := iteratedFDeriv_sub_const_pos (hg.comp hΨ) le_rfl (by omega) c x
    exact this
  rw [e1, Finset.sum_range_succ'] at h
  have e2 : ∀ i ∈ Finset.range n, ‖iteratedFDeriv ℝ (i + 1) (fun y => g y - c) (Ψ x)‖ =
      ‖iteratedFDeriv ℝ (i + 1) g (Ψ x)‖ := fun i hi => by
    rw [iteratedFDeriv_sub_const_pos hg (by have := Finset.mem_range.1 hi; omega) (by omega)]
  rw [Finset.sum_congr rfl (fun i hi => by rw [e2 i hi])] at h
  simpa [hc] using h

end AVRegularity.ChartTransport
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.ChartTransport

/-! Chart transport, part (1): the time-integral assembly.  A pointwise-in-time domination of a
slice by a finite sum of slices gives the corresponding bound of the residual norm
`ν^{-1/2} (∫ A)^{1/2} + ∫ B^{1/2}`; measurability of the slices makes the lower integrals additive. -/

theorem rpow_sum_le {α : Type*} (S : Finset α) (a : α → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : (∑ s ∈ S, a s) ^ p ≤ ∑ s ∈ S, a s ^ p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp0]
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add_right ih _)

/-- Time assembly. -/
theorem time_assembly {α : Type*} (S : Finset α) {I : Set ℝ} (hI : MeasurableSet I)
    (A B : ℝ → ℝ≥0∞) (X Y : α → ℝ → ℝ≥0∞) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : ∀ t ∈ I, A t ≤ ENNReal.ofReal c₁ * ∑ s ∈ S, X s t)
    (hB : ∀ t ∈ I, B t ≤ ENNReal.ofReal c₂ * ∑ s ∈ S, Y s t)
    (hX : ∀ s ∈ S, Measurable (X s)) (hY : ∀ s ∈ S, Measurable (Y s)) (e : ℝ≥0∞) :
    e * (∫⁻ t in I, A t) ^ (1 / 2 : ℝ) + ∫⁻ t in I, B t ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (max (c₁ ^ (1 / 2 : ℝ)) (c₂ ^ (1 / 2 : ℝ))) *
        ∑ s ∈ S, (e * (∫⁻ t in I, X s t) ^ (1 / 2 : ℝ) + ∫⁻ t in I, Y s t ^ (1 / 2 : ℝ)) := by
  set m : ℝ := max (c₁ ^ (1 / 2 : ℝ)) (c₂ ^ (1 / 2 : ℝ)) with hm
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have h1 : (∫⁻ t in I, A t) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c₁ ^ (1 / 2 : ℝ)) * ∑ s ∈ S, (∫⁻ t in I, X s t) ^ (1 / 2 : ℝ) := by
    have hint : ∫⁻ t in I, A t ≤ ENNReal.ofReal c₁ * ∑ s ∈ S, ∫⁻ t in I, X s t := by
      calc ∫⁻ t in I, A t ≤ ∫⁻ t in I, ENNReal.ofReal c₁ * ∑ s ∈ S, X s t :=
            setLIntegral_mono' hI hA
        _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_finsetSum (f := fun s t => X s t) S hX]
    calc (∫⁻ t in I, A t) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal c₁ * ∑ s ∈ S, ∫⁻ t in I, X s t) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hint hp.le
      _ = ENNReal.ofReal (c₁ ^ (1 / 2 : ℝ)) * (∑ s ∈ S, ∫⁻ t in I, X s t) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg hc₁ hp.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_sum_le S _ hp hp1) zero_le
  have h2 : ∫⁻ t in I, B t ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c₂ ^ (1 / 2 : ℝ)) * ∑ s ∈ S, ∫⁻ t in I, Y s t ^ (1 / 2 : ℝ) := by
    calc ∫⁻ t in I, B t ^ (1 / 2 : ℝ)
        ≤ ∫⁻ t in I, ENNReal.ofReal (c₂ ^ (1 / 2 : ℝ)) * ∑ s ∈ S, Y s t ^ (1 / 2 : ℝ) := by
          refine setLIntegral_mono' hI fun t ht => ?_
          calc B t ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal c₂ * ∑ s ∈ S, Y s t) ^ (1 / 2 : ℝ) :=
                ENNReal.rpow_le_rpow (hB t ht) hp.le
            _ = ENNReal.ofReal (c₂ ^ (1 / 2 : ℝ)) * (∑ s ∈ S, Y s t) ^ (1 / 2 : ℝ) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
                  ENNReal.ofReal_rpow_of_nonneg hc₂ hp.le]
            _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_sum_le S _ hp hp1) zero_le
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finsetSum S (fun s hs => (hY s hs).pow_const _)]
  have hm1 : ENNReal.ofReal (c₁ ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal m :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hm2 : ENNReal.ofReal (c₂ ^ (1 / 2 : ℝ)) ≤ ENNReal.ofReal m :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc e * (∫⁻ t in I, A t) ^ (1 / 2 : ℝ) + ∫⁻ t in I, B t ^ (1 / 2 : ℝ)
      ≤ e * (ENNReal.ofReal m * ∑ s ∈ S, (∫⁻ t in I, X s t) ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal m * ∑ s ∈ S, ∫⁻ t in I, Y s t ^ (1 / 2 : ℝ) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (h1.trans ?_) zero_le) (h2.trans ?_)
        · exact mul_le_mul_of_nonneg_right hm1 zero_le
        · exact mul_le_mul_of_nonneg_right hm2 zero_le
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring

end AVRegularity.ChartTransport
end

section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Ergodic
open scoped ENNReal
namespace AVRegularity.ChartTransport

/-! Chart transport: a lattice-equivariant, unit-Jacobian `C¹` bijection with `C¹` inverse
preserves the cell integral of nonnegative periodic functions. -/

theorem det_fderiv_eq_jac (f : Vec 2 → Vec 2) (y : Vec 2) :
    (fderiv ℝ f y).det = (jacMatrix f y).det := by
  have h : jacMatrix f y = LinearMap.toMatrix' (fderiv ℝ f y : Vec 2 →ₗ[ℝ] Vec 2) := by
    ext i j
    simp [jacMatrix, LinearMap.toMatrix'_apply, basisVec]
  rw [h, LinearMap.det_toMatrix']

theorem measurePreserving_of_det {Φ Ψ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ 1 Φ)
    (hl : ∀ y, Ψ (Φ y) = y) (hr : ∀ x, Φ (Ψ x) = x)
    (hdet : ∀ y, (jacMatrix Φ y).det = 1) : MeasurePreserving Φ volume volume := by
  refine ⟨hΦ.continuous.measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply hΦ.continuous.measurable hA]
  have hinj : Set.InjOn Φ (Φ ⁻¹' A) := fun a _ b _ h => by
    have := congrArg Ψ h; rwa [hl, hl] at this
  have hs : MeasurableSet (Φ ⁻¹' A) := hΦ.continuous.measurable hA
  have hf' : ∀ x ∈ Φ ⁻¹' A, HasFDerivWithinAt Φ (fderiv ℝ Φ x) (Φ ⁻¹' A) x := fun x _ =>
    ((hΦ.differentiable (by norm_num)) x).hasFDerivAt.hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' hinj (fun _ => 1)
  have himg : Φ '' (Φ ⁻¹' A) = A := Set.image_preimage_eq _ (fun x => ⟨Ψ x, hr x⟩)
  rw [himg] at key
  simp only [det_fderiv_eq_jac, hdet, abs_one, ENNReal.ofReal_one, one_mul,
    setLIntegral_const] at key
  simpa using key.symm

theorem flowFundamentalCell_ae_unitCube :
    Flow.flowFundamentalCell 2 =ᵐ[volume] unitCube := by
  rw [← Flow.unitCellSet_eq_flowFundamentalCell]
  have he : unitCellSet 2 = Infra.Torus.unitCell 2 := by
    ext x
    simp [unitCellSet, Infra.Torus.unitCell, Infra.Torus.unitCellAt]
  rw [he]
  exact Infra.Torus.unitCell_ae_eq_unitCube

/-- The cell integral of a nonnegative periodic function is invariant under `Φ`. -/
theorem lintegral_cell_comp {Φ Ψ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ 1 Φ)
    (hΨ : Continuous Ψ) (hl : ∀ y, Ψ (Φ y) = y) (hr : ∀ x, Φ (Ψ x) = x)
    (heq : ∀ (n : Fin 2 → ℤ) y, Φ (y + latticeShift n) = Φ y + latticeShift n)
    (hdet : ∀ y, (jacMatrix Φ y).det = 1) (g : Vec 2 → ℝ≥0∞) (hg : IsZ2Periodic g) :
    ∫⁻ x in unitCube, g (Φ x) = ∫⁻ x in unitCube, g x := by
  let : Countable (Flow.flowLattice 2) := Flow.flowLattice_countable 2
  have hmp := measurePreserving_of_det hΦ hl hr hdet
  let e : Vec 2 ≃ᵐ Vec 2 :=
    MeasurableEquiv.mk ⟨Φ, Ψ, hl, hr⟩ hΦ.continuous.measurable hΨ.measurable
  have hemb : MeasurableEmbedding Φ := e.measurableEmbedding
  have hInv : MeasurePreserving (⇑e.toEquiv.symm) volume volume := by
    simpa [e] using MeasurePreserving.symm e hmp
  have hsemi : ∀ (g : Flow.flowLattice 2) (x : Vec 2), Φ (g +ᵥ x) = g +ᵥ Φ x := by
    intro g x
    obtain ⟨k, hk⟩ := Flow.flowLattice_mem_latticeVector g
    change Φ ((g : Vec 2) + x) = (g : Vec 2) + Φ x
    calc Φ ((g : Vec 2) + x) = Φ (x + latticeShift k) := by
          rw [hk, add_comm]; rfl
      _ = Φ x + latticeShift k := heq k x
      _ = (g : Vec 2) + Φ x := by rw [hk]; unfold Infra.Ergodic.latticeVector latticeShift; abel
  have hFD : IsAddFundamentalDomain (Flow.flowLattice 2) (Φ '' Flow.flowFundamentalCell 2)
      volume :=
    (Flow.flowFundamentalCell_isAddFundamentalDomain 2).image_of_equiv e.toEquiv
      hInv.quasiMeasurePreserving (Equiv.refl _) hsemi
  have hp := Flow.flowLattice_translation_invariant
    ((isZPeriodic_iff_isZ2Periodic g).2 hg)
  calc ∫⁻ x in unitCube, g (Φ x) = ∫⁻ x in Flow.flowFundamentalCell 2, g (Φ x) :=
        (setLIntegral_congr flowFundamentalCell_ae_unitCube).symm
    _ = ∫⁻ y in Φ '' Flow.flowFundamentalCell 2, g y :=
        hmp.setLIntegral_comp_emb hemb g _
    _ = ∫⁻ x in Flow.flowFundamentalCell 2, g x :=
        ((Flow.flowFundamentalCell_isAddFundamentalDomain 2).setLIntegral_eq hFD g hp).symm
    _ = ∫⁻ x in unitCube, g x := setLIntegral_congr flowFundamentalCell_ae_unitCube

theorem det_jac_inv_eq_one {Φ Ψ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ 1 Φ)
    (hΨ : ContDiff ℝ 1 Ψ) (hl : ∀ y, Ψ (Φ y) = y) (hr : ∀ x, Φ (Ψ x) = x)
    (hdet : ∀ y, (jacMatrix Φ y).det = 1) (x : Vec 2) : (jacMatrix Ψ x).det = 1 := by
  have hcomp : ∀ y, (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Φ y) = ContinuousLinearMap.id ℝ (Vec 2) := by
    intro y
    have h1 : Ψ ∘ Φ = id := funext hl
    have h2 := fderiv_comp y ((hΨ.differentiable (by norm_num)) (Φ y))
      ((hΦ.differentiable (by norm_num)) y)
    rw [h1] at h2
    simpa using h2.symm
  have h3 := hcomp (Ψ x)
  rw [hr] at h3
  have h4 := congrArg ContinuousLinearMap.det h3
  have e : ((fderiv ℝ Ψ x).comp (fderiv ℝ Φ (Ψ x)) : Vec 2 →ₗ[ℝ] Vec 2) =
      (fderiv ℝ Ψ x : Vec 2 →ₗ[ℝ] Vec 2) ∘ₗ (fderiv ℝ Φ (Ψ x) : Vec 2 →ₗ[ℝ] Vec 2) := rfl
  rw [ContinuousLinearMap.det, e, LinearMap.det_comp] at h4
  have h5 : (fderiv ℝ Φ (Ψ x)).det = 1 := by rw [det_fderiv_eq_jac, hdet]
  simp only [ContinuousLinearMap.det] at h5
  rw [h5, mul_one] at h4
  rw [← det_fderiv_eq_jac]
  simpa [ContinuousLinearMap.det] using h4

/-- The same cell invariance for the inverse chart. -/
theorem lintegral_cell_comp_inv {Φ Ψ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ 1 Φ)
    (hΨ : ContDiff ℝ 1 Ψ) (hl : ∀ y, Ψ (Φ y) = y) (hr : ∀ x, Φ (Ψ x) = x)
    (heq : ∀ (n : Fin 2 → ℤ) y, Φ (y + latticeShift n) = Φ y + latticeShift n)
    (hdet : ∀ y, (jacMatrix Φ y).det = 1) (g : Vec 2 → ℝ≥0∞) (hg : IsZ2Periodic g) :
    ∫⁻ x in unitCube, g (Ψ x) = ∫⁻ x in unitCube, g x := by
  refine lintegral_cell_comp hΨ hΦ.continuous hr hl ?_ (det_jac_inv_eq_one hΦ hΨ hl hr hdet) g hg
  intro n y
  have : Φ (Ψ y + latticeShift n) = y + latticeShift n := by rw [heq, hr]
  calc Ψ (y + latticeShift n) = Ψ (Φ (Ψ y + latticeShift n)) := by rw [this]
    _ = Ψ y + latticeShift n := hl _

end AVRegularity.ChartTransport
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.ChartTransport

/-! Chart transport, word calculus on `Vec 2`: the full iterated derivative and the ordered word
derivatives control each other (with dimension constants), ordered derivatives of periodic fields
are periodic, and the component projection commutes with ordered derivatives. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_basisVec (i : Fin 2) : ‖(basisVec i : Vec 2)‖ = 1 := by
  simp [basisVec, Pi.norm_single]

theorem vec2_eq_sum_basisVec (x : Vec 2) : x = ∑ j : Fin 2, x j • basisVec j := by
  ext j; simp [basisVec, Pi.single_apply, Finset.sum_apply]

theorem norm_le_sum_basisVec {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) F) :
    ‖f‖ ≤ ∑ w : DerivativeWord2 q, ‖f (fun i => basisVec (w i))‖ := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun x => ?_
  have hx : x = fun i => ∑ j : Fin 2, x i j • basisVec j := funext fun i => vec2_eq_sum_basisVec _
  have h1 : f x = ∑ r : DerivativeWord2 q, f (fun i => x i (r i) • basisVec (r i)) := by
    conv_lhs => rw [hx]
    exact f.toMultilinearMap.map_sum (fun i j => x i j • basisVec j)
  have h2 : ∀ r : DerivativeWord2 q, ‖f (fun i => x i (r i) • basisVec (r i))‖ ≤
      (∏ i, ‖x i‖) * ‖f (fun i => basisVec (r i))‖ := by
    intro r
    rw [f.map_smul_univ, norm_smul, norm_prod]
    refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      fun i _ => ?_) (norm_nonneg _)
    exact norm_le_pi_norm (x i) (r i)
  rw [h1]
  calc ‖∑ r : DerivativeWord2 q, f (fun i => x i (r i) • basisVec (r i))‖
      ≤ ∑ r : DerivativeWord2 q, ‖f (fun i => x i (r i) • basisVec (r i))‖ := norm_sum_le _ _
    _ ≤ ∑ r : DerivativeWord2 q, (∏ i, ‖x i‖) * ‖f (fun i => basisVec (r i))‖ :=
        Finset.sum_le_sum fun r _ => h2 r
    _ = (∑ w : DerivativeWord2 q, ‖f (fun i => basisVec (w i))‖) * ∏ i, ‖x i‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- Reversal of a derivative word, as an equivalence. -/
def wordRev (q : ℕ) : DerivativeWord2 q ≃ DerivativeWord2 q where
  toFun w := fun i => w (Fin.rev i)
  invFun w := fun i => w (Fin.rev i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

theorem card_derivativeWord2 (q : ℕ) :
    (Finset.univ : Finset (DerivativeWord2 q)).card = 2 ^ q := by
  simp

theorem norm_orderedDerivative_le {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (w : DerivativeWord2 q) (x : Vec 2) :
    ‖orderedDerivative w g x‖ ≤ ‖iteratedFDeriv ℝ q g x‖ := by
  rw [orderedDerivative_eq_iteratedFDeriv w hg]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [norm_basisVec]

theorem norm_iteratedFDeriv_le_sum_words {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ q g x‖ ≤ ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ := by
  have h1 := norm_le_sum_basisVec (iteratedFDeriv ℝ q g x)
  have h2 : ∑ w : DerivativeWord2 q, ‖iteratedFDeriv ℝ q g x (fun i => basisVec (w i))‖ =
      ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ := by
    rw [← Equiv.sum_comp (wordRev q)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [orderedDerivative_eq_iteratedFDeriv w hg]
    rfl
  rwa [h2] at h1

theorem norm_iteratedFDeriv_sq_le_words {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ q g x‖ ^ 2 ≤
      2 ^ q * ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ ^ 2 := by
  have h1 := norm_iteratedFDeriv_le_sum_words hg x
  have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (DerivativeWord2 q)))
    (f := fun w => ‖orderedDerivative w g x‖)
  rw [card_derivativeWord2] at h3
  calc ‖iteratedFDeriv ℝ q g x‖ ^ 2
      ≤ (∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by exact_mod_cast h3

theorem sum_orderedDerivative_sq_le {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (x : Vec 2) :
    ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ ^ 2 ≤
      2 ^ q * ‖iteratedFDeriv ℝ q g x‖ ^ 2 := by
  calc ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ ^ 2
      ≤ ∑ w : DerivativeWord2 q, ‖iteratedFDeriv ℝ q g x‖ ^ 2 :=
        Finset.sum_le_sum fun w _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_orderedDerivative_le hg w x) 2
    _ = 2 ^ q * ‖iteratedFDeriv ℝ q g x‖ ^ 2 := by
        rw [Finset.sum_const, card_derivativeWord2]; simp

theorem contDiff_orderedDerivative {p q : ℕ} (α : DerivativeWord2 q) {g : Vec 2 → F}
    (hg : ContDiff ℝ ((p + q : ℕ) : ℕ∞) g) : ContDiff ℝ (p : ℕ∞) (orderedDerivative α g) := by
  rw [orderedDerivative_eq_iteratedFDeriv α (hg.of_le (by exact_mod_cast Nat.le_add_left q p))]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) F
    (fun i => basisVec (α (Fin.rev i)))).contDiff.comp
    (hg.iteratedFDeriv_right (by exact_mod_cast le_rfl))

theorem continuous_orderedDerivative {q : ℕ} (α : DerivativeWord2 q) {g : Vec 2 → F}
    (hg : ContDiff ℝ (q : ℕ∞) g) : Continuous (orderedDerivative α g) :=
  (contDiff_orderedDerivative (p := 0) α (by simpa using hg)).continuous

/-- Ordered derivatives of `ℤ²`-periodic fields are periodic. -/
theorem isZ2Periodic_orderedDerivative {j : ℕ} (β : DerivativeWord2 j) {g : Vec 2 → F}
    (hg : AVenhance.IsZ2Periodic g) : AVenhance.IsZ2Periodic (orderedDerivative β g) := by
  induction j with
  | zero => rw [orderedDerivative_zero]; exact hg
  | succ j ih =>
    intro n x
    rw [orderedDerivative_succ]
    simp only
    have h := ih (fun i : Fin j => β i.castSucc)
    have e : fderiv ℝ (orderedDerivative (fun i : Fin j => β i.castSucc) g) (x + AVenhance.latticeShift n)
        = fderiv ℝ (orderedDerivative (fun i : Fin j => β i.castSucc) g) x := by
      have := fderiv_comp_add_right (𝕜 := ℝ) (x := x)
        (f := orderedDerivative (fun i : Fin j => β i.castSucc) g) (AVenhance.latticeShift n)
      have hf : (fun y => orderedDerivative (fun i : Fin j => β i.castSucc) g
          (y + AVenhance.latticeShift n)) = orderedDerivative (fun i : Fin j => β i.castSucc) g :=
        funext fun y => h n y
      rw [hf] at this
      exact this.symm
    rw [e]

/-- The component projection commutes with ordered derivatives. -/
theorem orderedDerivative_apply {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {j : ℕ} (β : DerivativeWord2 j)
    {g : Vec 2 → ∀ i, h i} (hg : ContDiff ℝ (j : ℕ∞) g) (v : ι) (x : Vec 2) :
    orderedDerivative β g x v = orderedDerivative β (fun x => g x v) x := by
  have := orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) β hg
  exact (congrFun this x).symm

end AVRegularity.ChartTransport
end

section
open Homogenization
namespace AVRegularity.ChartTransport

/-! Chart transport: scale-weighted Leibniz bounds for `M • H`, the Jacobian entries of a chart as
coefficient fields, and the jet-bound predicate for a chart. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalized jets of a chart: `‖D^p Θ‖ ≤ D Rχ^{1-p}` for `1 ≤ p ≤ N`. -/
def JetBound (Θ : Vec 2 → Vec 2) (N : ℕ) (D Rχ : ℝ) : Prop :=
  ∀ p, 1 ≤ p → p ≤ N → ∀ y, ‖iteratedFDeriv ℝ p Θ y‖ ≤ D * Rχ⁻¹ ^ (p - 1)

theorem jetBound_of_Cχ {Θ : Vec 2 → Vec 2} {N : ℕ} {Cχ : ℕ → ℝ} {Rχ : ℝ} (hR : 0 < Rχ)
    (h : ∀ p, 1 ≤ p → p ≤ N → ∀ y, ‖iteratedFDeriv ℝ p Θ y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) :
    JetBound Θ N (1 + ∑ p ∈ Finset.range (N + 1), |Cχ p|) Rχ := by
  intro p hp1 hpN y
  refine (h p hp1 hpN y).trans ?_
  have hpos : 0 ≤ Rχ⁻¹ ^ (p - 1) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hpos
  have : |Cχ p| ≤ ∑ p ∈ Finset.range (N + 1), |Cχ p| :=
    Finset.single_le_sum (f := fun p => |Cχ p|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hpN))
  linarith [le_abs_self (Cχ p)]

theorem one_le_jetConst (Cχ : ℕ → ℝ) (N : ℕ) :
    1 ≤ 1 + ∑ p ∈ Finset.range (N + 1), |Cχ p| := by
  have : 0 ≤ ∑ p ∈ Finset.range (N + 1), |Cχ p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

theorem smul_bound {M : Vec 2 → ℝ} {H : Vec 2 → E} {n : ℕ} (hM : ContDiff ℝ (n : ℕ∞) M)
    (hH : ContDiff ℝ (n : ℕ∞) H) {s A : ℝ} (hs : 0 < s) (x : Vec 2)
    (hA : ∀ i, i ≤ n → s ^ i * ‖iteratedFDeriv ℝ i M x‖ ≤ A) :
    s ^ n * ‖iteratedFDeriv ℝ n (fun y => M y • H y) x‖ ≤
      2 ^ n * A * ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q H x‖ := by
  have h := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := (n : ℕ∞)) hM hH x (n := n) le_rfl
  have hA0 : 0 ≤ A := (mul_nonneg (pow_nonneg hs.le 0) (norm_nonneg _)).trans (hA 0 (Nat.zero_le _))
  calc s ^ n * ‖iteratedFDeriv ℝ n (fun y => M y • H y) x‖
      ≤ s ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i M x‖ *
        ‖iteratedFDeriv ℝ (n - i) H x‖ := mul_le_mul_of_nonneg_left h (pow_nonneg hs.le n)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (s ^ i * ‖iteratedFDeriv ℝ i M x‖) *
        (s ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) H x‖) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : s ^ n = s ^ i * s ^ (n - i) := by
        rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
      rw [this]; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), 2 ^ n * A *
        (s ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) H x‖) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hc : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
      have hb := hA i hi'
      have h0 : 0 ≤ s ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) H x‖ := by positivity
      calc (n.choose i : ℝ) * (s ^ i * ‖iteratedFDeriv ℝ i M x‖) *
            (s ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) H x‖)
          ≤ 2 ^ n * A * (s ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) H x‖) := by
            refine mul_le_mul_of_nonneg_right ?_ h0
            exact mul_le_mul hc hb (by positivity) (by positivity)
        _ = _ := rfl
    _ = 2 ^ n * A * ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q H x‖ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_reflect (fun q => s ^ q * ‖iteratedFDeriv ℝ q H x‖) (n + 1)

/-- Jacobian entries (times a unimodular constant) are controlled by the next jet of the chart. -/
theorem norm_iteratedFDeriv_jac_entry {Φ : Vec 2 → Vec 2} {n i : ℕ}
    (hΦ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) Φ) (hi : i ≤ n) (k l : Fin 2) {c : ℝ} (hc : |c| ≤ 1)
    (y : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun z => c * jacMatrix Φ z k l) y‖ ≤ ‖iteratedFDeriv ℝ (i + 1) Φ y‖ := by
  let L : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    c • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec l)))
  have hL : ∀ z, c * jacMatrix Φ z k l = L (fderiv ℝ Φ z) := by
    intro z; simp [L, jacMatrix]
  have hL1 : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    simp only [L, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, one_mul]
    have h1 : |T (basisVec l) k| ≤ ‖T‖ := by
      calc |T (basisVec l) k| = ‖T (basisVec l) k‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖T (basisVec l)‖ := norm_le_pi_norm _ _
        _ ≤ ‖T‖ * ‖(basisVec l : Vec 2)‖ := T.le_opNorm _
        _ = ‖T‖ := by rw [norm_basisVec, mul_one]
    calc |c| * |T (basisVec l) k| ≤ 1 * ‖T‖ := mul_le_mul hc h1 (abs_nonneg _) zero_le_one
      _ = ‖T‖ := one_mul _
  have hfd : ContDiff ℝ (n : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  have e : (fun z => c * jacMatrix Φ z k l) = L ∘ fderiv ℝ Φ := funext hL
  have hfi : ContDiff ℝ (i : ℕ∞) (fderiv ℝ Φ) := hfd.of_le (by exact_mod_cast hi)
  rw [e]
  calc ‖iteratedFDeriv ℝ i (L ∘ fderiv ℝ Φ) y‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i (fderiv ℝ Φ) y‖ :=
        L.norm_iteratedFDeriv_comp_left
          hfi.contDiffAt (by exact_mod_cast le_rfl)
    _ ≤ 1 * ‖iteratedFDeriv ℝ i (fderiv ℝ Φ) y‖ := by gcongr
    _ = ‖iteratedFDeriv ℝ (i + 1) Φ y‖ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

end AVRegularity.ChartTransport
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.ChartTransport

/-! Chart transport: real pointwise densities of the (gradient) factorial norms, and the abstract
comparison lemma turning a pointwise jet bound into a density bound. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise real density of order `j` (`e = 0`: factorial norm; `e = 1`: gradient norm). -/
noncomputable def fdens (ρ : ℝ) (e j : ℕ) (u : Vec 2 → E) (x : Vec 2) : ℝ :=
  ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 * ∑ w : DerivativeWord2 (j + e), ‖orderedDerivative w u x‖ ^ 2

theorem fdens_nonneg (ρ : ℝ) (e j : ℕ) (u : Vec 2 → E) (x : Vec 2) : 0 ≤ fdens ρ e j u x := by
  unfold fdens
  have : 0 ≤ ρ ^ (2 * j) := by rw [pow_mul]; positivity
  positivity

theorem ofReal_fdens (ρ : ℝ) (e j : ℕ) (u : Vec 2 → E) (x : Vec 2) :
    ENNReal.ofReal (fdens ρ e j u x) = ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∑ w : DerivativeWord2 (j + e), ‖orderedDerivative w u x‖ₑ ^ 2 := by
  unfold fdens
  have h0 : 0 ≤ ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 := by
    have : 0 ≤ ρ ^ (2 * j) := by rw [pow_mul]; positivity
    positivity
  rw [ENNReal.ofReal_mul h0, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem measurable_enorm_sq_orderedDerivative {q : ℕ} {u : Vec 2 → E}
    (hu : ContDiff ℝ (q : ℕ∞) u) (w : DerivativeWord2 q) :
    Measurable (fun x => ‖orderedDerivative w u x‖ₑ ^ 2) :=
  ((continuous_orderedDerivative w hu).enorm.measurable).pow_const 2

theorem lintegral_fdens (ρ : ℝ) (e j : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((j + e : ℕ) : ℕ∞) u) (S : Set (Vec 2)) :
    ∫⁻ x in S, ENNReal.ofReal (fdens ρ e j u x) =
      ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
        ∑ w : DerivativeWord2 (j + e), ∫⁻ x in S, ‖orderedDerivative w u x‖ₑ ^ 2 := by
  simp only [ofReal_fdens]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
  exact fun w _ => measurable_enorm_sq_orderedDerivative hu w

theorem classicalFactorialSq_eq (ρ : ℝ) (m : ℕ) {u : Vec 2 → E} (hu : ContDiff ℝ (m : ℕ∞) u) :
    classicalFactorialSq ρ m u = ∑ j ∈ Finset.range (m + 1),
      ∫⁻ x in AVenhance.unitCube, ENNReal.ofReal (fdens ρ 0 j u x) := by
  unfold classicalFactorialSq
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  exact (lintegral_fdens ρ 0 j (hu.of_le (by exact_mod_cast hjm)) _).symm

theorem classicalGradFactorialSq_eq (ρ : ℝ) (m : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) u) :
    classicalGradFactorialSq ρ m u = ∑ j ∈ Finset.range (m + 1),
      ∫⁻ x in AVenhance.unitCube, ENNReal.ofReal (fdens ρ 1 j u x) := by
  unfold classicalGradFactorialSq
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  exact (lintegral_fdens ρ 1 j (hu.of_le (by exact_mod_cast hjm)) _).symm

end AVRegularity.ChartTransport
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.ChartTransport

/-! Chart transport: from a pointwise jet bound to a bound of the factorial densities. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fdens_le_jet {ρ : ℝ} (e j : ℕ) {u : Vec 2 → E} (hu : ContDiff ℝ ((j + e : ℕ) : ℕ∞) u)
    (x : Vec 2) :
    fdens ρ e j u x ≤ 2 ^ (j + e) / ((j.factorial : ℝ)) ^ 2 *
      (ρ ^ j * ‖iteratedFDeriv ℝ (j + e) u x‖) ^ 2 := by
  unfold fdens
  have hs := sum_orderedDerivative_sq_le hu x
  have h0 : 0 ≤ ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 := by
    have : 0 ≤ ρ ^ (2 * j) := by rw [pow_mul]; positivity
    positivity
  calc ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 * ∑ w : DerivativeWord2 (j + e),
        ‖orderedDerivative w u x‖ ^ 2
      ≤ ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 * (2 ^ (j + e) * ‖iteratedFDeriv ℝ (j + e) u x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hs h0
    _ = _ := by rw [pow_mul', mul_pow]; ring

theorem jet_le_fdens (ρ : ℝ) (e i : ℕ) {g : Vec 2 → E} (hg : ContDiff ℝ ((i + e : ℕ) : ℕ∞) g)
    (z : Vec 2) :
    (ρ ^ i * ‖iteratedFDeriv ℝ (i + e) g z‖) ^ 2 / ((i.factorial : ℝ)) ^ 2 ≤
      2 ^ (i + e) * fdens ρ e i g z := by
  unfold fdens
  have hs := norm_iteratedFDeriv_sq_le_words hg z
  have hf : (0 : ℝ) < ((i.factorial : ℝ)) ^ 2 := by positivity
  rw [div_le_iff₀ hf]
  calc (ρ ^ i * ‖iteratedFDeriv ℝ (i + e) g z‖) ^ 2
      = ρ ^ (2 * i) * ‖iteratedFDeriv ℝ (i + e) g z‖ ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm i 2]
    _ ≤ ρ ^ (2 * i) * (2 ^ (i + e) * ∑ w : DerivativeWord2 (i + e), ‖orderedDerivative w g z‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left hs ?_
        rw [pow_mul]; positivity
    _ = _ := by field_simp

/-- Abstract comparison: a pointwise jet bound gives a density bound. -/
theorem fdens_sum_le {κ : Type*} [Fintype κ] {M e : ℕ} {ρ K : ℝ} {u : Vec 2 → F}
    (hρ : 0 ≤ ρ) (hu : ContDiff ℝ ((M + e : ℕ) : ℕ∞) u) {g : κ → Vec 2 → E}
    (hg : ∀ l, ContDiff ℝ ((M + e : ℕ) : ℕ∞) (g l)) (x z : Vec 2)
    (H : ∀ j, j ≤ M → ρ ^ j * ‖iteratedFDeriv ℝ (j + e) u x‖ ≤
      K * ∑ l, ∑ i ∈ Finset.range (j + 1), ρ ^ i * ‖iteratedFDeriv ℝ (i + e) (g l) z‖) :
    ∑ j ∈ Finset.range (M + 1), fdens ρ e j u x ≤
      ((M + 1) * ((M + 1) * Fintype.card κ * (2 ^ (M + e)) ^ 2 * K ^ 2)) *
        ∑ l, ∑ i ∈ Finset.range (M + 1), fdens ρ e i (g l) z := by
  set SG : ℝ := ∑ l, ∑ i ∈ Finset.range (M + 1), fdens ρ e i (g l) z with hSG
  have hSG0 : 0 ≤ SG :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => fdens_nonneg _ _ _ _ _
  set B : ℝ := ((M + 1) * Fintype.card κ * (2 ^ (M + e)) ^ 2 * K ^ 2) * SG with hB
  have key : ∀ j, j ≤ M → fdens ρ e j u x ≤ B := by
    intro j hj
    have huj : ContDiff ℝ ((j + e : ℕ) : ℕ∞) u :=
      hu.of_le (by exact_mod_cast Nat.add_le_add_right hj e)
    have h1 := fdens_le_jet (ρ := ρ) e j huj x
    set a : κ → ℕ → ℝ := fun l i => ρ ^ i * ‖iteratedFDeriv ℝ (i + e) (g l) z‖ with ha
    have ha0 : ∀ l i, 0 ≤ a l i := fun l i => by simp only [ha]; positivity
    have hjet : ρ ^ j * ‖iteratedFDeriv ℝ (j + e) u x‖ ≤
        K * ∑ l, ∑ i ∈ Finset.range (j + 1), a l i := H j hj
    have hnn : 0 ≤ ρ ^ j * ‖iteratedFDeriv ℝ (j + e) u x‖ := by positivity
    set T : ℝ := ∑ l, ∑ i ∈ Finset.range (j + 1), a l i with hT
    have hsq : (ρ ^ j * ‖iteratedFDeriv ℝ (j + e) u x‖) ^ 2 ≤ K ^ 2 * T ^ 2 := by
      calc _ ≤ (K * T) ^ 2 := pow_le_pow_left₀ hnn hjet 2
        _ = _ := by ring
    have hS2 : ∀ l, (∑ i ∈ Finset.range (j + 1), a l i) ^ 2 ≤
        (j + 1) * ∑ i ∈ Finset.range (j + 1), a l i ^ 2 := by
      intro l
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := a l)
      simpa using this
    set Q : ℝ := ∑ l, ∑ i ∈ Finset.range (j + 1), a l i ^ 2 with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have hT2 : T ^ 2 ≤ Fintype.card κ * ((j + 1) * Q) := by
      have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ))
        (f := fun l => ∑ i ∈ Finset.range (j + 1), a l i)
      rw [Finset.card_univ] at h2
      refine h2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ∑ l, (∑ i ∈ Finset.range (j + 1), a l i) ^ 2
          ≤ ∑ l, ((j + 1 : ℝ) * ∑ i ∈ Finset.range (j + 1), a l i ^ 2) :=
            Finset.sum_le_sum fun l _ => hS2 l
        _ = (j + 1) * Q := by rw [← Finset.mul_sum]
    have hjf : (0 : ℝ) < ((j.factorial : ℝ)) ^ 2 := by positivity
    have hQd : Q / ((j.factorial : ℝ)) ^ 2 ≤ 2 ^ (M + e) * SG := by
      have e1 : Q / ((j.factorial : ℝ)) ^ 2 =
          ∑ l, ∑ i ∈ Finset.range (j + 1), a l i ^ 2 / ((j.factorial : ℝ)) ^ 2 := by
        simp only [hQ, Finset.sum_div]
      rw [e1]
      calc ∑ l, ∑ i ∈ Finset.range (j + 1), a l i ^ 2 / ((j.factorial : ℝ)) ^ 2
          ≤ ∑ l, ∑ i ∈ Finset.range (j + 1), 2 ^ (M + e) * fdens ρ e i (g l) z := by
            refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i hi => ?_
            have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            have hgi : ContDiff ℝ ((i + e : ℕ) : ℕ∞) (g l) :=
              (hg l).of_le (by exact_mod_cast Nat.add_le_add (hij.trans hj) le_rfl)
            have h3 := jet_le_fdens ρ e i hgi z
            have h4 : a l i ^ 2 / ((j.factorial : ℝ)) ^ 2 ≤ a l i ^ 2 / ((i.factorial : ℝ)) ^ 2 := by
              have : (i.factorial : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hij
              exact div_le_div_of_nonneg_left (by positivity) (by positivity)
                (pow_le_pow_left₀ (by positivity) this 2)
            have h5 : (2 : ℝ) ^ (i + e) ≤ 2 ^ (M + e) :=
              pow_le_pow_right₀ (by norm_num) (Nat.add_le_add (hij.trans hj) le_rfl)
            calc _ ≤ a l i ^ 2 / ((i.factorial : ℝ)) ^ 2 := h4
              _ ≤ 2 ^ (i + e) * fdens ρ e i (g l) z := h3
              _ ≤ _ := mul_le_mul_of_nonneg_right h5 (fdens_nonneg _ _ _ _ _)
        _ = 2 ^ (M + e) * ∑ l, ∑ i ∈ Finset.range (j + 1), fdens ρ e i (g l) z := by
            simp only [← Finset.mul_sum]
        _ ≤ 2 ^ (M + e) * SG := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum fun l _ => Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.2 (Nat.succ_le_succ hj))
              (fun _ _ _ => fdens_nonneg _ _ _ _ _)
    have h2j : (2 : ℝ) ^ (j + e) ≤ 2 ^ (M + e) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add hj le_rfl)
    have hj1 : (j : ℝ) + 1 ≤ M + 1 := by exact_mod_cast Nat.succ_le_succ hj
    calc fdens ρ e j u x ≤ 2 ^ (j + e) / ((j.factorial : ℝ)) ^ 2 * (K ^ 2 * T ^ 2) :=
          h1.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
      _ ≤ 2 ^ (j + e) / ((j.factorial : ℝ)) ^ 2 * (K ^ 2 * (Fintype.card κ * ((j + 1) * Q))) := by
          gcongr
      _ = 2 ^ (j + e) * K ^ 2 * Fintype.card κ * (j + 1) * (Q / ((j.factorial : ℝ)) ^ 2) := by
          field_simp
      _ ≤ 2 ^ (j + e) * K ^ 2 * Fintype.card κ * (j + 1) * (2 ^ (M + e) * SG) := by
          gcongr
      _ ≤ 2 ^ (M + e) * K ^ 2 * Fintype.card κ * (M + 1) * (2 ^ (M + e) * SG) := by
          gcongr
      _ = B := by rw [hB]; ring
  calc ∑ j ∈ Finset.range (M + 1), fdens ρ e j u x ≤ ∑ j ∈ Finset.range (M + 1), B :=
        Finset.sum_le_sum fun j hj => key j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end AVRegularity.ChartTransport
end

section
open Homogenization
open scoped ContDiff
namespace AVRegularity.ChartTransport

/-! Chart transport: pointwise jet bounds for `g ∘ Θ` and for Piola-type combinations
`∑_l M_l • (G_l ∘ Θ)` with Jacobian-entry coefficients. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Faà di Bruno constant. -/
def compConst (D : ℝ) (n : ℕ) : ℝ := (n + 1) * (n.factorial * D ^ n)

theorem compConst_mono {D : ℝ} (hD : 1 ≤ D) {i n : ℕ} (h : i ≤ n) :
    compConst D i ≤ compConst D n := by
  unfold compConst
  have h1 : (i.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le h
  have h2 : D ^ i ≤ D ^ n := pow_le_pow_right₀ hD h
  have h3 : (i : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ h
  have hD0 : 0 ≤ D := by linarith
  gcongr

theorem compConst_nonneg {D : ℝ} (hD : 1 ≤ D) (n : ℕ) : 0 ≤ compConst D n := by
  unfold compConst
  have : 0 ≤ D := by linarith
  positivity

/-- `∑_{q ≤ n} s^q ‖D^q (g ∘ Θ)‖` is controlled by `∑_{i ≤ n} s^i ‖D^i g(Θ x)‖`. -/
theorem comp_sum_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : Vec 2 → G}
    {Θ : Vec 2 → Vec 2} {n : ℕ} (hg : ContDiff ℝ (n : ℕ∞) g) (hΘ : ContDiff ℝ (n : ℕ∞) Θ)
    {D Rχ s : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hsR : s ≤ Rχ) (hJ : JetBound Θ n D Rχ) (x : Vec 2) :
    ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q (g ∘ Θ) x‖ ≤
      compConst D n * ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖ := by
  have hS : 0 ≤ ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖ :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q (g ∘ Θ) x‖
      ≤ ∑ q ∈ Finset.range (n + 1), (n.factorial * D ^ n *
          ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
        have hq' : ((q : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞) : ℕ∞ω) := by exact_mod_cast hqn
        have h := scaled_comp_bound (n := q) (hg.of_le hq') (hΘ.of_le hq') hD hs hsR x
          (fun p hp1 hpq => hJ p hp1 (hpq.trans hqn) x)
        refine h.trans ?_
        have hfq : (q.factorial : ℝ) * D ^ q ≤ n.factorial * D ^ n := by
          have h1 : (q.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hqn
          have h2 : D ^ q ≤ D ^ n := pow_le_pow_right₀ hD hqn
          have : 0 ≤ D := by linarith
          gcongr
        have hsub : ∑ i ∈ Finset.range (q + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖ ≤
            ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (Nat.succ_le_succ hqn)) (fun _ _ _ => by positivity)
        calc _ ≤ (n.factorial * D ^ n) *
              ∑ i ∈ Finset.range (q + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖ := by
              refine mul_le_mul_of_nonneg_right hfq (Finset.sum_nonneg fun _ _ => by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hsub (by
              have : 0 ≤ D := by linarith
              positivity)
    _ = compConst D n * ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i g (Θ x)‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        unfold compConst; push_cast; ring

/-- The coefficient `jacMatrix Φ ∘ Ψ` has weighted jets bounded by `compConst D n * D`. -/
theorem jacComp_bound {Φ Ψ : Vec 2 → Vec 2} {n : ℕ} (hΦ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (n : ℕ∞) Ψ) {D Rχ s : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hsR : s ≤ Rχ)
    (hJΦ : JetBound Φ (n + 1) D Rχ) (hJΨ : JetBound Ψ n D Rχ) (k l : Fin 2) (x : Vec 2) :
    ∀ i, i ≤ n → s ^ i * ‖iteratedFDeriv ℝ i (fun z => jacMatrix Φ (Ψ z) k l) x‖ ≤
      compConst D n * D := by
  intro i hi
  have hR : 0 < Rχ := lt_of_lt_of_le hs hsR
  have hgc : ContDiff ℝ (n : ℕ∞) (fun y => 1 * jacMatrix Φ y k l) := by
    simp only [one_mul]
    have : ContDiff ℝ (n : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
    exact (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
        (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec l)))).comp this
  have hi' : ((i : ℕ∞) : ℕ∞ω) ≤ ((n : ℕ∞) : ℕ∞ω) := by exact_mod_cast hi
  have e : (fun z => jacMatrix Φ (Ψ z) k l) = (fun y => 1 * jacMatrix Φ y k l) ∘ Ψ := by
    funext z; simp
  have h := scaled_comp_bound (n := i) (hgc.of_le hi') (hΨ.of_le hi') hD hs hsR x
    (fun p hp1 hpq => hJΨ p hp1 (hpq.trans hi) x)
  rw [e]
  refine h.trans ?_
  have hterm : ∀ q ∈ Finset.range (i + 1),
      s ^ q * ‖iteratedFDeriv ℝ q (fun y => 1 * jacMatrix Φ y k l) (Ψ x)‖ ≤ D := by
    intro q hq
    have hqi : q ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have h1 := norm_iteratedFDeriv_jac_entry (n := n) hΦ (hqi.trans hi) k l
      (c := 1) (by simp) (Ψ x)
    have h2 := hJΦ (q + 1) (by omega) (by omega) (Ψ x)
    simp only [Nat.add_sub_cancel] at h2
    have hh : 1 ≤ s * Rχ⁻¹ ∨ s * Rχ⁻¹ ≤ 1 := le_total _ _
    have h3 : s * Rχ⁻¹ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one hR).2 hsR
    calc s ^ q * ‖iteratedFDeriv ℝ q (fun y => 1 * jacMatrix Φ y k l) (Ψ x)‖
        ≤ s ^ q * (D * Rχ⁻¹ ^ q) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hs.le q)
      _ = D * (s * Rχ⁻¹) ^ q := by rw [mul_pow]; ring
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) h3) (by linarith)
      _ = D := mul_one D
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hD0 : 0 ≤ D := by linarith
  have hfq : (i.factorial : ℝ) * D ^ i ≤ n.factorial * D ^ n := by
    have h1 : (i.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hi
    have h2 : D ^ i ≤ D ^ n := pow_le_pow_right₀ hD hi
    gcongr
  have hi1 : (i : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hi
  calc (i.factorial : ℝ) * D ^ i * ∑ q ∈ Finset.range (i + 1),
        s ^ q * ‖iteratedFDeriv ℝ q (fun y => 1 * jacMatrix Φ y k l) (Ψ x)‖
      ≤ (i.factorial * D ^ i) * ((i + 1 : ℕ) * D) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (n.factorial * D ^ n) * ((n + 1) * D) := by
        push_cast
        gcongr
    _ = compConst D n * D := by unfold compConst; ring

/-- Two-term Leibniz plus chart composition. -/
theorem two_term_bound {M₀ M₁ : Vec 2 → ℝ} {H₀ H₁ : Vec 2 → E} {n : ℕ}
    (hM₀ : ContDiff ℝ (n : ℕ∞) M₀) (hM₁ : ContDiff ℝ (n : ℕ∞) M₁)
    (hH₀ : ContDiff ℝ (n : ℕ∞) H₀) (hH₁ : ContDiff ℝ (n : ℕ∞) H₁) {s A : ℝ} (hs : 0 < s)
    (x : Vec 2) (hA₀ : ∀ i, i ≤ n → s ^ i * ‖iteratedFDeriv ℝ i M₀ x‖ ≤ A)
    (hA₁ : ∀ i, i ≤ n → s ^ i * ‖iteratedFDeriv ℝ i M₁ x‖ ≤ A) :
    s ^ n * ‖iteratedFDeriv ℝ n (fun y => M₀ y • H₀ y + M₁ y • H₁ y) x‖ ≤
      2 ^ n * A * ((∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q H₀ x‖) +
        ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q H₁ x‖) := by
  have hadd := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n)
    (f := fun y => M₀ y • H₀ y) (g := fun y => M₁ y • H₁ y) (x := x)
    ((hM₀.smul hH₀).contDiffAt) ((hM₁.smul hH₁).contDiffAt)
  have hA0 : 0 ≤ A := (mul_nonneg (pow_nonneg hs.le 0) (norm_nonneg _)).trans (hA₀ 0 (Nat.zero_le _))
  have e : (fun y => M₀ y • H₀ y + M₁ y • H₁ y) = (fun y => M₀ y • H₀ y) + fun y => M₁ y • H₁ y := rfl
  rw [e, hadd]
  calc s ^ n * ‖iteratedFDeriv ℝ n (fun y => M₀ y • H₀ y) x +
        iteratedFDeriv ℝ n (fun y => M₁ y • H₁ y) x‖
      ≤ s ^ n * (‖iteratedFDeriv ℝ n (fun y => M₀ y • H₀ y) x‖ +
        ‖iteratedFDeriv ℝ n (fun y => M₁ y • H₁ y) x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hs.le n)
    _ = s ^ n * ‖iteratedFDeriv ℝ n (fun y => M₀ y • H₀ y) x‖ +
        s ^ n * ‖iteratedFDeriv ℝ n (fun y => M₁ y • H₁ y) x‖ := by ring
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (smul_bound hM₀ hH₀ hs x hA₀) (smul_bound hM₁ hH₁ hs x hA₁)
end

/-! Chart transport: pointwise bounds for the Piola flux `(DΦ R) ∘ Ψ` and the inverse-Piola flux
`(DΦ)⁻¹ (Fc ∘ Φ)`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_entry (k l : Fin 2) :
    ∃ (c : ℝ) (a b : Fin 2), |c| ≤ 1 ∧ ∀ J : Matrix (Fin 2) (Fin 2) ℝ, J.det = 1 →
      J⁻¹ k l = c * J a b := by
  have e : ∀ J : Matrix (Fin 2) (Fin 2) ℝ, J.det = 1 → J⁻¹ = J.adjugate := fun J h => by
    rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]
  fin_cases k <;> fin_cases l
  · exact ⟨1, 1, 1, by simp, fun J h => by rw [e J h, Matrix.adjugate_fin_two]; simp⟩
  · exact ⟨-1, 0, 1, by simp, fun J h => by rw [e J h, Matrix.adjugate_fin_two]; simp⟩
  · exact ⟨-1, 1, 0, by simp, fun J h => by rw [e J h, Matrix.adjugate_fin_two]; simp⟩
  · exact ⟨1, 0, 0, by simp, fun J h => by rw [e J h, Matrix.adjugate_fin_two]; simp⟩

/-- Piola flux `(DΦ R) ∘ Ψ`, pointwise order-`n` bound. -/
theorem flux_chart_bound {Φ Ψ : Vec 2 → Vec 2} {n : ℕ} (hΦ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (n : ℕ∞) Ψ) {G : Fin 2 → Vec 2 → E} (hG : ∀ l, ContDiff ℝ (n : ℕ∞) (G l))
    {D Rχ s : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hsR : s ≤ Rχ) (hJΦ : JetBound Φ (n + 1) D Rχ)
    (hJΨ : JetBound Ψ n D Rχ) (k : Fin 2) (x : Vec 2) :
    s ^ n * ‖iteratedFDeriv ℝ n (fun z => ∑ l : Fin 2, jacMatrix Φ (Ψ z) k l • G l (Ψ z)) x‖ ≤
      2 ^ n * (compConst D n * D) * compConst D n *
        ∑ l : Fin 2, ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i (G l) (Ψ x)‖ := by
  have hM : ∀ l, ContDiff ℝ (n : ℕ∞) (fun z => jacMatrix Φ (Ψ z) k l) := by
    intro l
    have hfd : ContDiff ℝ (n : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
    have : ContDiff ℝ (n : ℕ∞) (fun y => jacMatrix Φ y k l) :=
      (ContinuousLinearMap.contDiff
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).comp
          (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec l)))).comp hfd
    exact this.comp hΨ
  have hH : ∀ l, ContDiff ℝ (n : ℕ∞) (fun z => G l (Ψ z)) := fun l => (hG l).comp hΨ
  have hb := two_term_bound (hM 0) (hM 1) (hH 0) (hH 1) hs x
    (jacComp_bound hΦ hΨ hD hs hsR hJΦ hJΨ k 0 x) (jacComp_bound hΦ hΨ hD hs hsR hJΦ hJΨ k 1 x)
  have hc : ∀ l, ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q (fun z => G l (Ψ z)) x‖ ≤
      compConst D n * ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i (G l) (Ψ x)‖ :=
    fun l => comp_sum_bound (hG l) hΨ hD hs hsR hJΨ x
  simp only [Fin.sum_univ_two]
  have hA : 0 ≤ 2 ^ n * (compConst D n * D) := by
    have := compConst_nonneg hD n
    have : 0 ≤ D := by linarith
    positivity
  refine hb.trans ?_
  exact (mul_le_mul_of_nonneg_left (add_le_add (hc 0) (hc 1)) hA).trans_eq (by ring)

/-- Inverse-Piola flux `(c * DΦ_{ab}) (G ∘ Φ)`, pointwise order-`n` bound. -/
theorem piola_chart_bound {Φ : Vec 2 → Vec 2} {n : ℕ} (hΦ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) Φ)
    {G : Fin 2 → Vec 2 → E} (hG : ∀ l, ContDiff ℝ (n : ℕ∞) (G l)) {c : Fin 2 → ℝ}
    (hc : ∀ l, |c l| ≤ 1) (a b : Fin 2 → Fin 2)
    {D Rχ s : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hsR : s ≤ Rχ) (hJΦ : JetBound Φ (n + 1) D Rχ)
    (x : Vec 2) :
    s ^ n * ‖iteratedFDeriv ℝ n (fun z => ∑ l : Fin 2, (c l * jacMatrix Φ z (a l) (b l)) • G l (Φ z))
        x‖ ≤
      2 ^ n * D * compConst D n *
        ∑ l : Fin 2, ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i (G l) (Φ x)‖ := by
  have hR : 0 < Rχ := lt_of_lt_of_le hs hsR
  have hΦn : ContDiff ℝ (n : ℕ∞) Φ := hΦ.of_le (by exact_mod_cast Nat.le_succ n)
  have hM : ∀ l, ContDiff ℝ (n : ℕ∞) (fun z => c l * jacMatrix Φ z (a l) (b l)) := by
    intro l
    have hfd : ContDiff ℝ (n : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
    have : ContDiff ℝ (n : ℕ∞) (fun y => jacMatrix Φ y (a l) (b l)) :=
      (ContinuousLinearMap.contDiff
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (a l)).comp
          (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec (b l))))).comp hfd
    exact contDiff_const.mul this
  have hH : ∀ l, ContDiff ℝ (n : ℕ∞) (fun z => G l (Φ z)) := fun l => (hG l).comp hΦn
  have hA : ∀ l i, i ≤ n → s ^ i *
      ‖iteratedFDeriv ℝ i (fun z => c l * jacMatrix Φ z (a l) (b l)) x‖ ≤ D := by
    intro l i hi
    have h1 := norm_iteratedFDeriv_jac_entry (n := n) hΦ hi (a l) (b l) (hc l) x
    have h2 := hJΦ (i + 1) (by omega) (by omega) x
    simp only [Nat.add_sub_cancel] at h2
    have h3 : s * Rχ⁻¹ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one hR).2 hsR
    calc s ^ i * ‖iteratedFDeriv ℝ i (fun z => c l * jacMatrix Φ z (a l) (b l)) x‖
        ≤ s ^ i * (D * Rχ⁻¹ ^ i) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hs.le i)
      _ = D * (s * Rχ⁻¹) ^ i := by rw [mul_pow]; ring
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) h3) (by linarith)
      _ = D := mul_one D
  have hb := two_term_bound (hM 0) (hM 1) (hH 0) (hH 1) hs x (hA 0) (hA 1)
  have hJ' : JetBound Φ n D Rχ := fun p hp1 hpn y => hJΦ p hp1 (by omega) y
  have hcs : ∀ l, ∑ q ∈ Finset.range (n + 1), s ^ q * ‖iteratedFDeriv ℝ q (fun z => G l (Φ z)) x‖ ≤
      compConst D n * ∑ i ∈ Finset.range (n + 1), s ^ i * ‖iteratedFDeriv ℝ i (G l) (Φ x)‖ :=
    fun l => comp_sum_bound (hG l) hΦn hD hs hsR hJ' x
  have hA0 : 0 ≤ 2 ^ n * D := by
    have : 0 ≤ D := by linarith
    positivity
  simp only [Fin.sum_univ_two]
  refine hb.trans ?_
  exact (mul_le_mul_of_nonneg_left (add_le_add (hcs 0) (hcs 1)) hA0).trans_eq (by ring)
end

end AVRegularity.ChartTransport
end
