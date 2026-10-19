-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.Unit
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import AVRegularity.CycleWords.Seam.OldAdjointIdentification

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # the core of the homogeneous propagator in `H^j` with a kernel

Only four properties of the kernel are used: `0 ≤ κ`, `κ r r = 1`, the shrink property
`κ p s ≤ A κ p t` for `p ≤ s ≤ t ≤ s + 1`, and the `L²` decay of the curves. The shrink property
(not `anti`) is what survives time reversal, so the same core serves the adjoint (the adjoint propagator bound). -/

theorem rpow_sq (τ : ℝ) (hτ : 0 < τ) (j : ℕ) :
    (τ ^ (-(j : ℝ) / 2)) ^ 2 = (τ⁻¹) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le, show -(j : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(j : ℝ) by
    push_cast; ring, Real.rpow_neg hτ.le, Real.rpow_natCast, inv_pow]

theorem kernelCore_one (j : ℕ) (ρ A : ℝ) (hρ : 0 ≤ ρ) (hA : 1 ≤ A) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
      {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
      (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
      a ≤ b → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
    ∀ κ : ℝ → ℝ → ℝ, (∀ r s, 0 ≤ κ r s) → (∀ r, κ r r = 1) →
      (∀ p s t, a ≤ p → p ≤ s → s ≤ t → t ≤ s + 1 → t ≤ b → κ p s ≤ A * κ p t) →
      (∀ r s, a ≤ r → r ≤ s → s ≤ b → ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve r s u slice
          (fun t => cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
            (slice t) 0 0) → ‖u s‖ ≤ κ r s * ‖u r‖) →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t =>
        cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
          (slice t) 0 0) →
      (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b,
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
          ‖w‖ ≤ C * (1 + L) ^ Q * κ a t * ‖w₀‖) := by
  obtain ⟨Cr, Qr, hCr, hreg⟩ := cellDriftRegularity j ρ hρ
  refine ⟨A * Cr, Qr, by positivity, ?_⟩
  intro a b L G hG v hv V hb θ hab hL hθ hsm hjet κ hκ0 hself hshr hdec u slice hu
  set P : ℝ := 1 + L with hPdef
  have hP : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hJ : DriftJets v a b P j :=
    ⟨hsm, fun l hl t ht x => (hjet l t (by omega) ht x).trans (by linarith)⟩
  have hua : ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ‖u a‖ ≤ ‖w₀‖ := by
    intro w₀ hw₀
    rw [← hw₀]
    exact cellDriftValue_norm_le w₀
  have hdecu : ∀ s, a ≤ s → s ≤ b → ‖u s‖ ≤ κ a s * ‖u a‖ := fun s has hsb =>
    hdec a s le_rfl has hsb u slice (hu.mono (Icc_subset_Icc le_rfl hsb))
  intro w₀ hw₀ t ht
  rcases le_or_gt t (a + 1) with h1 | h1
  · obtain ⟨w, hw, hn⟩ := (hreg a b L G hG hv V hb θ hab hL hθ hsm hjet u slice hu).1 w₀
      hw₀ t ht h1
    refine ⟨w, hw, ?_⟩
    have h1' : 1 ≤ A * κ a t := by
      have := hshr a a t le_rfl le_rfl ht.1 h1 ht.2
      rwa [hself] at this
    have hn0 : 0 ≤ ‖w₀‖ := norm_nonneg _
    calc ‖w‖ ≤ Cr * P ^ Qr * ‖w₀‖ := hn
      _ ≤ (Cr * P ^ Qr * ‖w₀‖) * (A * κ a t) := le_mul_of_one_le_right (by positivity) h1'
      _ = (A * Cr) * P ^ Qr * κ a t * ‖w₀‖ := by ring
  · set s : ℝ := t - 1 with hs
    have has : a ≤ s := by linarith
    have hsb : s ≤ b := by linarith [ht.2]
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc has le_rfl
    obtain ⟨w, hw, hn⟩ := (hreg s b L G hG hv V hb θ hsb hL hθ
      (fun t' ht' => hsm t' (hsub ht'))
      (fun l t' hl ht' x => hjet l t' hl (hsub ht') x) u slice (hu.mono hsub)).2 t
      ⟨by linarith, ht.2⟩ (by linarith) (by linarith)
    refine ⟨w, hw, ?_⟩
    have hk := hshr a s t le_rfl has (by linarith) (by linarith) ht.2
    have hd := hdecu s has hsb
    have hn0 : 0 ≤ ‖w₀‖ := norm_nonneg _
    have hu1 : ‖u a‖ ≤ ‖w₀‖ := hua w₀ hw₀
    have hk0 := hκ0 a t
    have hCP : 0 ≤ Cr * P ^ Qr := by positivity
    calc ‖w‖ ≤ Cr * P ^ Qr * ‖u s‖ := hn
      _ ≤ Cr * P ^ Qr * (κ a s * ‖u a‖) := mul_le_mul_of_nonneg_left hd hCP
      _ ≤ Cr * P ^ Qr * ((A * κ a t) * ‖w₀‖) := by
        apply mul_le_mul_of_nonneg_left _ hCP
        exact mul_le_mul hk hu1 (norm_nonneg _) (by positivity)
      _ = (A * Cr) * P ^ Qr * κ a t * ‖w₀‖ := by ring

theorem kernelCore_two (j : ℕ) (ρ A : ℝ) (hρ : 0 ≤ ρ) (hA : 1 ≤ A) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
      {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
      (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
      a ≤ b → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
    ∀ κ : ℝ → ℝ → ℝ, (∀ r s, 0 ≤ κ r s) → (∀ r, κ r r = 1) →
      (∀ p s t, a ≤ p → p ≤ s → s ≤ t → t ≤ s + 1 → t ≤ b → κ p s ≤ A * κ p t) →
      (∀ r s, a ≤ r → r ≤ s → s ≤ b → ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve r s u slice
          (fun t => cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
            (slice t) 0 0) → ‖u s‖ ≤ κ r s * ‖u r‖) →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t =>
        cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
          (slice t) 0 0) →
      (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ t ∈ Set.Icc a b, a + τ ≤ t →
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
          ‖w‖ ≤ C * (1 + L) ^ Q * τ ^ (-(j : ℝ) / 2) * κ a t * ‖u a‖) := by
  obtain ⟨Cr, Qr, hCr, hreg⟩ := cellDriftRegularity j ρ hρ
  have hM := cellDriftWindowPrice_one_le j ρ hρ
  set M := cellDriftWindowPrice j ρ with hMdef
  set Y : ℝ := Real.exp 1 * (2 * Real.exp 1) * ((j : ℝ) + 1) * M with hYdef
  have hY : 0 ≤ Y := by
    have := Real.exp_pos 1
    positivity
  set sq : ℝ := Real.sqrt (Y ^ j) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  refine ⟨A * sq, j, by positivity, ?_⟩
  intro a b L G hG v hv V hb θ hab hL hθ hsm hjet κ hκ0 hself hshr hdec u slice hu
  set P : ℝ := 1 + L with hPdef
  have hP : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hJ : DriftJets v a b P j :=
    ⟨hsm, fun l hl t ht x => (hjet l t (by omega) ht x).trans (by linarith)⟩
  have hua : ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ‖u a‖ ≤ ‖w₀‖ := by
    intro w₀ hw₀
    rw [← hw₀]
    exact cellDriftValue_norm_le w₀
  have hdecu : ∀ s, a ≤ s → s ≤ b → ‖u s‖ ≤ κ a s * ‖u a‖ := fun s has hsb =>
    hdec a s le_rfl has hsb u slice (hu.mono (Icc_subset_Icc le_rfl hsb))
  intro τ hτ0 hτ1 t ht hat
  set s : ℝ := max a (t - 1) with hs
  have has : a ≤ s := le_max_left _ _
  have hts : τ ≤ t - s := by
    rcases le_total a (t - 1) with h | h
    · rw [hs, max_eq_right h]; linarith
    · rw [hs, max_eq_left h]; linarith
  have hst : s < t := by linarith
  have hsb : s ≤ b := by linarith [ht.2]
  have hstt : t ≤ s + 1 := by
    have : t - 1 ≤ s := le_max_right _ _
    linarith
  have hk := hshr a s t le_rfl has hst.le hstt ht.2
  have hd := hdecu s has hsb
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has ht.2
  have hMP : 1 ≤ M * P ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hP]
  have hMP0 : 0 < M * P ^ 2 := by linarith
  set δ : ℝ := τ / (((j : ℝ) + 1) * (M * P ^ 2)) with hδ
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hden : 0 < ((j : ℝ) + 1) * (M * P ^ 2) := by positivity
  have hδ0 : 0 < δ := by positivity
  have hprice : M * P ^ 2 * δ ≤ 1 := by
    rw [hδ, mul_div_assoc', div_le_one hden]
    nlinarith
  have hjδ : (j : ℝ) * δ ≤ τ := by
    rw [hδ, mul_div_assoc', div_le_iff₀ hden]
    nlinarith [mul_nonneg hj0 hτ0.le, mul_nonneg hj0 (sub_nonneg.mpr hMP), hτ0.le]
  have hfin : s + (j : ℝ) * δ ≤ t := by linarith only [hjδ, hts]
  obtain ⟨W, hW1, hW2⟩ := weakSmoothing_free j ρ P hρ hP G hG hv V hb θ hθ hst
    (hJ.mono has ht.2) u slice (hu.mono hsub) δ hδ0 hprice t ⟨hst.le, le_rfl⟩ hfin
  refine ⟨W, hW1, ?_⟩
  have hrate : Real.exp 1 * (2 * Real.exp 1) / δ = Y * P ^ 2 * τ⁻¹ := by
    rw [hδ, hYdef]
    field_simp
  rw [hrate] at hW2
  have hτr := rpow_sq τ hτ0 j
  have hτp : 0 ≤ τ ^ (-(j : ℝ) / 2) := Real.rpow_nonneg hτ0.le _
  have hus : 0 ≤ ‖u s‖ := norm_nonneg _
  have hbound : ‖W‖ ≤ sq * P ^ j * τ ^ (-(j : ℝ) / 2) * ‖u s‖ := by
    have h2 : ‖W‖ ^ 2 ≤ (sq * P ^ j * τ ^ (-(j : ℝ) / 2) * ‖u s‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hτr, hsq, Real.sq_sqrt (pow_nonneg hY j), ← pow_mul,
        mul_comm j 2, pow_mul]
      calc ‖W‖ ^ 2 ≤ (Y * P ^ 2 * τ⁻¹) ^ j * ‖u s‖ ^ 2 := hW2
        _ = _ := by rw [mul_pow, mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2
  have hk0 := hκ0 a t
  have hCP : 0 ≤ sq * P ^ j * τ ^ (-(j : ℝ) / 2) := by positivity
  calc ‖W‖ ≤ sq * P ^ j * τ ^ (-(j : ℝ) / 2) * ‖u s‖ := hbound
    _ ≤ sq * P ^ j * τ ^ (-(j : ℝ) / 2) * (κ a s * ‖u a‖) :=
        mul_le_mul_of_nonneg_left hd hCP
    _ ≤ sq * P ^ j * τ ^ (-(j : ℝ) / 2) * ((A * κ a t) * ‖u a‖) := by
        apply mul_le_mul_of_nonneg_left _ hCP
        exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ = (A * sq) * P ^ j * τ ^ (-(j : ℝ) / 2) * κ a t * ‖u a‖ := by ring

/-- **The core.** -/
theorem kernelCore (j : ℕ) (ρ A : ℝ) (hρ : 0 ≤ ρ) (hA : 1 ≤ A) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
      {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
      (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
      a ≤ b → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
    ∀ κ : ℝ → ℝ → ℝ, (∀ r s, 0 ≤ κ r s) → (∀ r, κ r r = 1) →
      (∀ p s t, a ≤ p → p ≤ s → s ≤ t → t ≤ s + 1 → t ≤ b → κ p s ≤ A * κ p t) →
      (∀ r s, a ≤ r → r ≤ s → s ≤ b → ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve r s u slice
          (fun t => cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
            (slice t) 0 0) → ‖u s‖ ≤ κ r s * ‖u r‖) →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t =>
        cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
          (slice t) 0 0) →
      (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b,
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
          ‖w‖ ≤ C * (1 + L) ^ Q * κ a t * ‖w₀‖) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ t ∈ Set.Icc a b, a + τ ≤ t →
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
          ‖w‖ ≤ C * (1 + L) ^ Q * τ ^ (-(j : ℝ) / 2) * κ a t * ‖u a‖) := by
  obtain ⟨C₁, Q₁, hC₁, h₁⟩ := kernelCore_one j ρ A hρ hA
  obtain ⟨C₂, Q₂, hC₂, h₂⟩ := kernelCore_two j ρ A hρ hA
  refine ⟨C₁ + C₂, Q₁ + Q₂, by positivity, ?_⟩
  intro a b L G hG v hv V hb θ hab hL hθ hsm hjet κ hκ0 hself hshr hdec u slice hu
  have hP : 1 ≤ 1 + L := by linarith
  have hQ₁ : (1 + L) ^ Q₁ ≤ (1 + L) ^ (Q₁ + Q₂) := pow_le_pow_right₀ hP (by omega)
  have hQ₂ : (1 + L) ^ Q₂ ≤ (1 + L) ^ (Q₁ + Q₂) := pow_le_pow_right₀ hP (by omega)
  have hk := hκ0 a b
  constructor
  · intro w₀ hw₀ t ht
    obtain ⟨w, hw, hn⟩ := h₁ a b L G hG hv V hb θ hab hL hθ hsm hjet κ hκ0 hself hshr hdec u
      slice hu w₀ hw₀ t ht
    refine ⟨w, hw, hn.trans ?_⟩
    have := hκ0 a t
    have := norm_nonneg w₀
    gcongr
    linarith
  · intro τ hτ0 hτ1 t ht hat
    obtain ⟨w, hw, hn⟩ := h₂ a b L G hG hv V hb θ hab hL hθ hsm hjet κ hκ0 hself hshr hdec u
      slice hu τ hτ0 hτ1 t ht hat
    refine ⟨w, hw, hn.trans ?_⟩
    have := hκ0 a t
    have := norm_nonneg (u a)
    have := Real.rpow_nonneg hτ0.le (-(j : ℝ) / 2)
    gcongr
    linarith

end AVRegularity.CycleWords.Discard
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open AVRegularity.CycleWords.Seam
namespace AVRegularity.CycleWords.Discard

/-! # A cut level of a word chain is a native energy curve

For an arbitrary chain the letter flux of a level need not be square integrable, so the level is
not a `PlaneWeakHilbertCurve` with an `L²(I; H⁻¹)` source. After a cut it is. Let `T` be a bounded
operator on `H¹` (multiplication by a compact cutoff) with `L²` shadow `P`, whose gradients vanish
almost everywhere outside a set `O`, and let `S` be an `L²(I; L²)` field that agrees with the
letter flux on `O`. Then:

* `weakCont_cut_increment`: the weak identity of the level, tested against `T φ`;
* `weakCont_cut_weakCurve`: `P` of the coordinate of the level is a native energy curve, with dual
  `T†(generator + div S)`;
* `weakCont_cut_pairing`: the pairing of the cut level with the scalar reversed chain of a test,
  from the product rule of two energy curves. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- **The weak identity of a level against a cut test.** The gradient of the test `φ` vanishes
almost everywhere outside `O`, and `S` agrees with the letter flux on `O`. -/
theorem weakCont_cut_increment (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (O : Set (Vec 2)) (S : ℝ → PlaneFluxL2 (h i.2))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume, z ∈ O →
      (S r k : Vec 2 → h i.2) z =
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k)
    (e : h i.2) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (φ : PlaneHk Set.univ 1 ℝ)
    (hφ : ∀ k : Fin 2, ∀ᵐ z ∂volume, z ∉ O →
      φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z = 0) :
    inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace U i t)) (planeHkValueOperator 1 φ) -
      inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace U i s)) (planeHkValueOperator 1 φ) =
      ∫ r in s..t, inner ℝ (planeRealBlochGeneratorDual (G r) v hv r C (hC r)
        (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r)) +
          planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r))) φ := by
  let Φ := mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ
  rw [planeFiberCoordinate_pair, planeFiberCoordinate_pair]
  have hinj : planeFiberInjectionCLM e (planeHkValueOperator 1 φ) = planeHkValueOperator 1 Φ :=
    (planeHkFiberValue 1 _ φ).symm
  rw [hinj, coupledPlaneL2Trace_inner, coupledPlaneL2Trace_inner]
  have he := coupledWeakIdentity_fixed_increment (volume.restrict Set.univ) hab v
    (fun r => (U i r).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    ((f i).toFunction.jet (valueIndex2 (κ i.1 i.2))) (Φ.toFunction.jet (valueIndex2 1))
    (fun k => Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r k => (Uw i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r => wordChainRawFlux G letters X0 δ κ (fun p => Uw p r) i r)
    (fun _ => (0 : PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2))).toFunction.jet
      (valueIndex2 (κ i.1 i.2)))
    (fun _ => (0 : PlaneHk Set.univ (κ i.1 i.2) (h i.2)).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    (fun r hr => hsol.2.2.2.2 i r hr Φ) hs ht
  simp only [Measure.restrict_univ] at he
  rw [he]
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : Set.uIoc s t ⊆ Icc a b := by
    rw [uIoc_of_le hst]
    exact fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hSr := ae_restrict_of_ae_restrict_of_subset hsub hS
  filter_upwards [hSr] with r hr
  have hp := planeScalarCoordinateNativeFlux_pair (κ i.1 i.2) e (G r) (hG.2.2.1 r 0)
    v hv r C (hC r) (Uw i r) (S r)
    (fun x => WithLp.toLp 2 (fun k => (S r k : Vec 2 → h i.2) x))
    (fun _ => Filter.EventuallyEq.rfl) φ
  have hraw := integral_congr_ae (wordChainRawSpatialRhs_split hD G letters X0 δ κ v Uw i Φ r)
  have hjet : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x =
        ((ContinuousLinearMap.id ℝ ℝ).smulRight e)
          (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x) :=
    ae_all_iff.mpr (fun _ => planeHkMapRawReadout _ φ _)
  have hcmp : (fun x => planeScalarRawRhsZeroFlux (κ i.1 i.2) (v r) (fun _ => G r) (Uw i r) Φ x -
        ∑ k : Fin 2, inner ℝ
          (wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r x k)
          (Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x)) =ᵐ[volume]
      fun x => planeScalarRawRhsZeroFlux (κ i.1 i.2) (v r) (fun _ => G r) (Uw i r) Φ x -
        ∑ k : Fin 2, inner ℝ
          ((WithLp.toLp 2 (fun k' => (S r k' : Vec 2 → h i.2) x) :
            PiLp 2 (fun _ : Fin 2 => h i.2)) k)
          (Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x) := by
    filter_upwards [ae_all_iff.mpr hr, ae_all_iff.mpr hφ, hjet] with x hx hφx hjx
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hxO : x ∈ O
    · exact congrArg (fun y => inner ℝ y (Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x))
        (hx k hxO).symm
    · rw [hjx k, hφx k hxO, map_zero, inner_zero_right, inner_zero_right]
  have hall := (hraw.trans (integral_congr_ae hcmp)).trans hp.symm
  simpa only [coupledPlaneH1Slice, Φ] using hall

/-- **The cut level is a native energy curve.** -/
theorem weakCont_cut_weakCurve (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (O : Set (Vec 2)) (S : ℝ → PlaneFluxL2 (h i.2))
    (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume, z ∈ O →
      (S r k : Vec 2 → h i.2) z =
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k)
    (e : h i.2)
    (P : Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)))
    (T : PlaneHk Set.univ 1 ℝ →L[ℝ] PlaneHk Set.univ 1 ℝ)
    (hPT : ∀ w, planeHkValueOperator 1 (T w) = P (planeHkValueOperator 1 w))
    (hPs : ∀ u w : Lp ℝ 2 (volume : Measure (Vec 2)), inner ℝ (P u) w = inner ℝ u (P w))
    (hTO : ∀ (w : PlaneHk Set.univ 1 ℝ) (k : Fin 2), ∀ᵐ z ∂volume, z ∉ O →
      (T w).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z = 0) :
    PlaneWeakHilbertCurve a b
      (fun r => P (planeFiberCoordinateCLM e (coupledPlaneL2Trace U i r)))
      (fun r => T (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e)
        (coupledPlaneH1Slice Uw i r)))
      (fun r => ContinuousLinearMap.adjoint T
        (planeRealBlochGeneratorDual (G r) v hv r C (hC r)
          (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r)) +
            planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r)))) := by
  have hd := coupledWeakSolution_h1_trace_data hsol i
  have hm : MemLp (fun r => mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e)
      (coupledPlaneH1Slice Uw i r)) 2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, mapPlaneHkOperator_apply] using
      (mapPlaneHkOperator 1 (InnerProductSpace.toDual ℝ (h i.2) e)).comp_memLp' hd.2.1
  have hgen := planeRealBlochGeneratorDual_timeMemLp (volume.restrict (Icc a b))
    G hG v hv C hCpos.le hC _ hm
  have hflux : MemLp (fun r => planeFluxFiberCoordinateCLM e (S r))
      2 (volume.restrict (Icc a b)) := (planeFluxFiberCoordinateCLM e).comp_memLp' hSl
  have hzero : MemLp (fun _ : ℝ => (0 : Lp ℝ 2 (volume : Measure (Vec 2))))
      2 (volume.restrict (Icc a b)) := MemLp.zero'
  have hsource := planeSourceDual_memLp (fun _ => 0) hzero _ hflux
  have hsum := nativeTime_add_memLp (volume.restrict (Icc a b)) _ _ hgen hsource
  refine ⟨P.continuous.comp_continuousOn
      ((planeFiberCoordinateCLM e).continuous.comp_continuousOn hd.1),
    T.comp_memLp' hm, (ContinuousLinearMap.adjoint T).comp_memLp' hsum, ?_, ?_⟩
  · filter_upwards [hd.2.2] with r hr
    rw [hPT, hr, planeHkFiberValue]
    rfl
  · intro s hs t ht hst φ
    have h1 := weakCont_cut_increment hD G hG letters X0 δ κ a b hab v hv C hC f U Uw hsol i O S
      hS e hs ht hst (T φ) (hTO φ)
    rw [hPT] at h1
    rw [hPs, hPs, h1]
    apply intervalIntegral.integral_congr
    intro r _
    exact (ContinuousLinearMap.adjoint_inner_left T _ _).symm

/-- **A native energy curve against the backward field of a test** (product rule of two energy
curves; the backward field solves the adjoint equation). -/
theorem weakCont_curve_backward_pairing {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C' : ℝ) (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (slice dual : ℝ → PlaneHk Set.univ 1 ℝ)
    (hu : PlaneWeakHilbertCurve a b u slice dual)
    (φ : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ (u b) φ - inner ℝ (u a)
        (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab)
          (planeBlochBackwardRealField hab G hG v hv V hb φ) (-a))) =
      ∫ r in a..b,
        (inner ℝ (dual r) (cellEnergyPlaneRealH1State (neg_le_neg hab)
            (planeBlochBackwardRealField hab G hG v hv V hb φ) (-r)) -
          inner ℝ (planeRealBlochGeneratorDual (G r) (fun t x => -v t x) (cellDrift_neg hv) r C'
              (hC' r) (cellEnergyPlaneRealH1State (neg_le_neg hab)
                (planeBlochBackwardRealField hab G hG v hv V hb φ) (-r)))
            (slice r)) := by
  have he := planeWeakPair_increment hu
    (planeBlochBackwardReal_weakCurve hab G hG v hv V hb Cr hCrpos hCr C' hC' φ)
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hab
  rw [planeBlochBackwardReal_terminal hab G hG v hv V hb φ] at he
  refine he.trans ?_
  apply intervalIntegral.integral_congr
  intro r _
  simp only [inner_neg_left]
  ring

/-- **A native energy curve against the scalar reversed chain of a test.** -/
theorem weakCont_curve_reversed_pairing {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C' : ℝ) (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (slice dual : ℝ → PlaneHk Set.univ 1 ℝ)
    (hu : PlaneWeakHilbertCurve a b u slice dual)
    (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw) :
    inner ℝ (u b) (planeHkValueOperator m (g ())) -
        inner ℝ (u a) (planeHkValueOperator m (ψ 0 () (-a))) =
      ∫ r in a..b,
        (inner ℝ (dual r) (truncatePlaneHk hm (ψ 0 () (-r))) -
          inner ℝ (planeRealBlochGeneratorDual (G r) (fun t x => -v t x) (cellDrift_neg hv) r C'
              (hC' r) (truncatePlaneHk hm (ψ 0 () (-r))))
            (slice r)) := by
  obtain ⟨Cr, hCrpos, hCr⟩ := cellDriftTorusSymbol_bound _ (cellDrift_timeReverse hv)
  have he := weakCont_curve_backward_pairing hab G hG v hv V hb C' hC' Cr hCrpos hCr u slice dual
    hu (planeHkValueOperator m (g ()))
  rw [backwardField_trace_eq_reversedChain hab G hG v hv V hb Cr hCrpos hCr m g ψ ψw hψ
    ⟨-a, ⟨neg_le_neg hab, le_rfl⟩⟩] at he
  refine he.trans ?_
  apply intervalIntegral.integral_congr_ae
  filter_upwards [backwardField_h1State_eq_reversedChain_neg hab G hG v hv V hb Cr hCrpos hCr m hm
    g ψ ψw hψ] with r hr hmem
  rw [Set.uIoc_of_le hab] at hmem
  rw [hr ⟨hmem.1.le, hmem.2⟩]

/-- **The cut level against the scalar reversed chain of a test.** -/
theorem weakCont_cut_pairing (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C) (C' : ℝ)
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (O : Set (Vec 2)) (S : ℝ → PlaneFluxL2 (h i.2))
    (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume, z ∈ O →
      (S r k : Vec 2 → h i.2) z =
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k)
    (e : h i.2)
    (P : Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)))
    (T : PlaneHk Set.univ 1 ℝ →L[ℝ] PlaneHk Set.univ 1 ℝ)
    (hPT : ∀ w, planeHkValueOperator 1 (T w) = P (planeHkValueOperator 1 w))
    (hPs : ∀ u w : Lp ℝ 2 (volume : Measure (Vec 2)), inner ℝ (P u) w = inner ℝ u (P w))
    (hTO : ∀ (w : PlaneHk Set.univ 1 ℝ) (k : Fin 2), ∀ᵐ z ∂volume, z ∉ O →
      (T w).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z = 0)
    (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw) :
    inner ℝ (P (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i b))))
        (planeHkValueOperator m (g ())) -
      inner ℝ (P (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i))))
        (planeHkValueOperator m (ψ 0 () (-a))) =
      ∫ r in a..b,
        (inner ℝ (planeRealBlochGeneratorDual (G r) v hv r C (hC r)
            (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r)) +
              planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r)))
            (T (truncatePlaneHk hm (ψ 0 () (-r)))) -
          inner ℝ (planeRealBlochGeneratorDual (G r) (fun t x => -v t x) (cellDrift_neg hv) r C'
              (hC' r) (truncatePlaneHk hm (ψ 0 () (-r))))
            (T (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e)
              (coupledPlaneH1Slice Uw i r)))) := by
  have hcut := weakCont_cut_weakCurve hD G hG letters X0 δ κ a b hab v hv C hCpos hC f U Uw hsol
    i O S hSl hS e P T hPT hPs hTO
  have he := weakCont_curve_reversed_pairing hab G hG v hv M hb C' hC' _ _ _ hcut m hm g ψ ψw hψ
  have hUa : U i a = f i := hsol.2.2.2.1 i
  simp only [coupledPlaneL2Trace, ContinuousLinearMap.adjoint_inner_left] at he
  rw [hUa] at he
  exact he

end AVRegularity.CycleWords.Discard
end
