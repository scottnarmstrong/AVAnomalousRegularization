-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.RetainedAssign
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
public import AVRegularity.CycleWords.MixedWords.RetainedLinear
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Existence of the retained map from the leaves

`retainedMapExists_of_leaves`: on a well-buffered block, the amplitudes of compact chain data
(`exists_blockAmplitudes`: lifts by `CompactDensityStatement`, chains by
`CompactChainExistenceStatement`, linearity by `ChainCombinationStatement` and
`CompactChainGaussianStatement` at the datum `0`, `L²` bounds by `AmplitudePlancherelStatement`,
`CompactChainGaussianStatement` and `GaussianPlancherelStatement` at output order `0`) extend by
`L²` limits and `LinearMap.exists_extend` to a linear map (`exists_band_extension`) that is
band-limited, a.e. invariant, equal to the retained cutoff of the endpoint on compact chain data at
any descending slots, and bounded from `∑ K_i` moments into `L²`. -/

universe u v

section Zero

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The Bloch fibre jets of the zero family vanish. -/
theorem blochFibreDerivNorm_zero_family (π : ι → ℝ) (χ : Vec 2 → ℝ) (α : ℕ × ℕ) (θ : Vec 2) :
    blochFibreDerivNorm π χ α (0 : ∀ x, Vec 2 → h x) θ = 0 := by
  have hc : ∀ x θ' z, blochCos θ' ((0 : ∀ x, Vec 2 → h x) x) z = 0 := fun x θ' z => by
    simp [blochCos]
  have hs : ∀ x θ' z, blochSin θ' ((0 : ∀ x, Vec 2 → h x) x) z = 0 := fun x θ' z => by
    simp [blochSin]
  have h0 : ∀ x (a b : ℕ), thetaPartial a b (fun _ : Vec 2 => (0 : h x)) θ = 0 := by
    intro x a b
    simp [thetaPartial, iteratedFDeriv_fun_zero]
  unfold blochFibreDerivNorm
  simp only [hc, hs, smul_zero, h0, norm_zero]
  simp [ENNReal.zero_rpow_of_pos]

/-- An amplitude pair of vanishing order-`0` jet norm vanishes. -/
theorem amplitude_eq_zero_of_amplitudeJetNorm (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (ϖ : ℝ)
    {A B : ∀ x, Vec 2 → h x} {θ : Vec 2} (h0 : amplitudeJetNorm π 0 ϖ A B θ = 0) (x : ι) :
    A x θ = 0 ∧ B x θ = 0 := by
  have hidx : momentIndices 0 = {(0, 0)} := by decide
  simp only [amplitudeJetNorm, hidx, Finset.sum_singleton, zero_add, pow_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one, div_one, ENNReal.ofReal_one, one_mul] at h0
  rw [ENNReal.rpow_eq_zero_iff] at h0
  rcases h0 with ⟨hz, -⟩ | ⟨-, hneg⟩
  · have hx := (Finset.sum_eq_zero_iff.1 hz) x (Finset.mem_univ x)
    rcases mul_eq_zero.1 hx with hπ0 | hsum
    · exact absurd hπ0 (ENNReal.ofReal_pos.2 (inv_pos.2 (hπ x))).ne'
    · have ha := (add_eq_zero.1 hsum).1
      have hb := (add_eq_zero.1 hsum).2
      rw [ENNReal.ofReal_eq_zero] at ha hb
      have hA : ‖thetaPartial 0 0 (A x) θ‖ = 0 := by
        nlinarith [norm_nonneg (thetaPartial 0 0 (A x) θ)]
      have hB : ‖thetaPartial 0 0 (B x) θ‖ = 0 := by
        nlinarith [norm_nonneg (thetaPartial 0 0 (B x) θ)]
      simp only [thetaPartial, norm_eq_zero] at hA hB
      exact ⟨hA, hB⟩
  · norm_num at hneg

end Zero

/-- **Existence of the retained map from the leaves.** -/
theorem retainedMapExists_of_leaves (hA1 : ChainCombinationStatement.{u, v})
    (hA3 : CompactChainExistenceStatement.{u, v}) (hA4 : CompactDensityStatement.{u, v})
    (hB0 : AmplitudePlancherelStatement.{v}) (hB1 : CompactChainGaussianStatement.{u, v})
    (hB2 : GaussianPlancherelStatement.{u, v}) : RetainedMapExistsStatement.{u, v} := by
  intro K
  have hA3K := (hA3 K).choose_spec
  have hB1K := (hB1 K).choose_spec
  refine ⟨min (hA3 K).choose (hB1 K).choose, lt_min hA3K.1 hB1K.1, ?_⟩
  intro χlo hχ Nw D H d Ks pos
  obtain ⟨CGa, cGa, c₁, Q₁, hCGa, hcGa, hc₁, hB1s⟩ := hB1K.2 χlo hχ Nw D H 0 d Ks pos
    (fun ξ => χlo ((2 : ℝ)⁻¹ • ξ)) χlo hχ.dilate_smooth hχ.dilate_hasCompactSupport hχ.smooth
    (exists_bound_iteratedFDeriv_of_hasCompactSupport hχ.smooth hχ.hasCompactSupport)
    (hχ.eq_dilate_pow_mul _)
  obtain ⟨C2, hC2, hB2s⟩ := hB2 0 (wordReserveN 0 Ks) (wordReserveP 0 Ks) 0 cGa hcGa
    (fun ξ => χlo ((2 : ℝ)⁻¹ • ξ)) hχ.dilate_smooth hχ.dilate_hasCompactSupport
  refine ⟨c₁, Q₁, hc₁, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ ϖ G v g reg pkg hB hJ hwb X₀
  have hKs : (fun i => (letters i).slow) = Ks := funext fun i => (hletters i).2.1
  have hd : (fun i => (letters i).order) = d := funext fun i => (hletters i).1
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN 0 fun i => (letters i).slow)
      fun i => (letters i).order) (fun i => (letters i).order) ≤ J := by
    rw [hKs, hd]
    exact hJ
  have hξ : 0 < K.ξlo := pkg.consts_pos.2.1
  have hr : 0 < 2 * K.ξlo * Real.sqrt η := by
    have := Real.sqrt_pos.2 hB.hη
    positivity
  have hΘ := hB.wordTheta_nonneg
  have hslots := wordBaseSlots_isWordSlots letters hB.hlet
  set C0 : ℝ := C2 * (CGa * wordTheta ηg letters) with hC0
  have hC00 : 0 ≤ C0 := mul_nonneg hC2.le (mul_nonneg hCGa.le hΘ)
  -- `hB1` and `hB2` on compact chains
  have hB1i : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume) ∧
        (∀ x, IsRetainedAmplitude
          (fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))
          (2 * K.ξlo * Real.sqrt η)
          (retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
          (retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))) ∧
        momentNorm π 0 1 (fun x =>
            fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S)))) ≤
          ENNReal.ofReal C0 * momentNorm π (wordReserveN 0 Ks) ϖ φ := by
    intro κ hκ φ hφ f u w hf hc
    have hb1 := hB1s J π letters hletters η S ηg t₀ ϖ G v g reg pkg (hB.mono (min_le_right _ _))
      hJ hwb X₀ κ hκ φ hφ f u w hf hc
    refine ⟨hb1.1, hb1.2.1, ?_⟩
    have hb2 := hB2s π hB.hπ η ϖ (2 * K.ξlo * Real.sqrt η) (CGa * wordTheta ηg letters) hB.hη
      hB.ϖ_pos hB.ϖ_le (mul_nonneg hCGa.le hΘ)
      (fun x => fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))
      (fun x => retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
      (fun x => retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) φ hφ
      hb1.2.1 hb1.2.2.1 (fun x θ hθ => by
        simp only [retainedCosAmplitude, retainedSinAmplitude, retainedCutoff_eq_zero hχ η hθ,
          mul_zero, zero_smul, and_self]) hb1.2.2.2
    rw [Nat.cast_zero, ← hC0] at hb2
    rw [← weightedJetNorm_zero_zero π ϖ ϖ⁻¹ fun x =>
      ((hB0 _ _ _ _ hr (hb1.2.1 x)).1 0).continuous.aestronglyMeasurable]
    exact hb2
  -- `hB1` at the datum `0`
  have hB1z : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (∀ x, planeValue (f x) =ᵐ[volume] 0) →
        ∀ x, retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0 := by
    intro κ hκ f u w hc hf0 x
    have hb1 := hB1s J π letters hletters η S ηg t₀ ϖ G v g reg pkg (hB.mono (min_le_right _ _))
      hJ hwb X₀ κ hκ 0 (isCompactFamily_zero) f u w hf0 hc
    have hpt : ∀ θ : Vec 2,
        retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) θ = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) θ = 0 := by
      intro θ
      by_cases hθ : ∀ i, |θ i| ≤ Real.pi
      · have hle := hb1.2.2.2 θ hθ
        simp only [blochFibreDerivNorm_zero_family, mul_zero, Finset.sum_const_zero] at hle
        exact amplitude_eq_zero_of_amplitudeJetNorm π hB.hπ ϖ (le_antisymm hle zero_le) x
      · push Not at hθ
        obtain ⟨i, hi⟩ := hθ
        have hbig : Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) := by
          have h1 : |θ i| ≤ Real.sqrt (vecDot θ θ) := Real.abs_le_sqrt (by
            rw [sq]
            exact Finset.single_le_sum (f := fun j => θ j * θ j) (fun j _ => mul_self_nonneg _)
              (Finset.mem_univ i))
          linarith [Real.pi_pos]
        simp only [retainedCosAmplitude, retainedSinAmplitude, retainedCutoff_eq_zero hχ η hbig,
          mul_zero, zero_smul, and_self]
    exact ⟨funext fun θ => (hpt θ).1, funext fun θ => (hpt θ).2⟩
  -- the amplitude assignment and its extension
  obtain ⟨ampC, ampS, hC, hS, hcb, hident⟩ := exists_blockAmplitudes hA1 hA4 hB0 hχ hB.hD π hB.hπ
    letters η S ηg t₀ ϖ hr G v X₀ (wordReserveN 0 Ks) C0 hslots
    (fun f hf => hA3K.2 H J π letters η S ηg t₀ ϖ G v g reg pkg (hB.mono (min_le_left _ _)) hJ0
      X₀ f hf) hB1i hB1z
  obtain ⟨R, hband, hcongr, hcomp, htransfer⟩ := exists_band_extension hB0 hr hC hS
    fun F hF => by
      obtain ⟨φs, hφs, hconv⟩ := hA4.2 F hF
      exact ⟨φs, fun k x => hφs k x, hconv⟩
  refine ⟨R, ⟨hband, hcongr, fun κ hκ f u w hc hcd => ?_, ⟨C0 + 1, by linarith, fun g' hg' => ?_⟩⟩⟩
  · obtain ⟨φ, hφ, hfφ⟩ := hcd.exists_family
    rw [hcongr _ φ hfφ, hcomp φ hφ]
    exact hident κ hκ φ hφ f u w hfφ hc
  · rw [hKs]
    refine htransfer (C0 + 1) (by linarith) (fun φ hφ => (hcb φ hφ).trans ?_) g' hg'
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Weights, representatives and Minkowski for the Bloch fibre norms

* `momentNorm` and `blochFibreDerivNorm` do not see the representative of the datum
  (`momentNorm_congr_ae`, `blochFibreDerivNorm_congr_ae`: the lattice translates of a null set are
  null).
* For `s > 0`, `∑_v π_v⁻¹ ∫ ⟨y⟩^{2N} ‖G_v‖² ≤ 3·9^N (1 + 2 s^{-2N}) (N!)² ‖G‖²_{moment N}`
  (`sum_lintegral_jbracket_le_momentNorm`).
* Minkowski in `L²` when only one summand is known to be measurable (`lintegral_sq_add_le`). -/

section
section Representatives

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem momentNorm_congr_ae {π : ι → ℝ} {n : ℕ} {s : ℝ} {F F' : ∀ v, Vec 2 → h v}
    (hF : ∀ v, F v =ᵐ[volume] F' v) : momentNorm π n s F = momentNorm π n s F' := by
  unfold momentNorm
  refine Finset.sum_congr rfl fun β _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  exact eLpNorm_congr_ae ((hF v).mono fun z hz => by simp only [hz])

theorem ae_lattice_eq {E : Type*} {f f' : Vec 2 → E} (hf : f =ᵐ[volume] f') :
    ∀ᵐ z ∂volume, ∀ k : Fin 2 → ℤ,
      f (z + fun i => (k i : ℝ)) = f' (z + fun i => (k i : ℝ)) :=
  ae_all_iff.2 fun k =>
    (measurePreserving_add_right volume (fun i => (k i : ℝ))).quasiMeasurePreserving.ae_eq_comp hf

theorem blochFibreDerivNorm_congr_ae {π : ι → ℝ} {χ : Vec 2 → ℝ} {α : ℕ × ℕ}
    {F F' : ∀ v, Vec 2 → h v} (hF : ∀ v, F v =ᵐ[volume] F' v) (θ : Vec 2) :
    blochFibreDerivNorm π χ α F θ = blochFibreDerivNorm π χ α F' θ := by
  have hall : ∀ᵐ z ∂volume, ∀ v, ∀ k : Fin 2 → ℤ,
      F v (z + fun i => (k i : ℝ)) = F' v (z + fun i => (k i : ℝ)) :=
    ae_all_iff.2 fun v => ae_lattice_eq (hF v)
  unfold blochFibreDerivNorm
  congr 1
  refine lintegral_congr_ae (ae_restrict_of_ae (hall.mono fun z hz => ?_))
  have hc : ∀ v θ', blochCos θ' (F v) z = blochCos θ' (F' v) z := fun v θ' =>
    tsum_congr fun k => by rw [hz v k]
  have hs : ∀ v θ', blochSin θ' (F v) z = blochSin θ' (F' v) z := fun v θ' =>
    tsum_congr fun k => by rw [hz v k]
  simp only [hc, hs]

end Representatives

section Weights

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- One moment term is bounded by `N!` times the moment norm. -/
theorem sum_eLpNorm_sq_le_momentNorm (π : ι → ℝ) {N : ℕ} (s : ℝ) (G : ∀ v, Vec 2 → h v)
    {β : ℕ × ℕ} (hβ : β ∈ momentIndices N) :
    ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2 ≤
      (ENNReal.ofReal (N.factorial : ℝ) * momentNorm π N s G) ^ 2 := by
  set T := ∑ v, ENNReal.ofReal ((π v)⁻¹) *
    eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2 with hT
  have hβN : β.1 + β.2 ≤ N := by
    simp only [momentIndices, Finset.mem_filter] at hβ
    exact hβ.2
  have hfac : ((β.1.factorial * β.2.factorial : ℕ) : ℝ) ≤ (N.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_factorial_dvd_factorial_add β.1 β.2 |> Nat.le_of_dvd
      (Nat.factorial_pos _)).trans (Nat.factorial_le hβN)
  have hpos : (0 : ℝ) < ((β.1.factorial * β.2.factorial : ℕ) : ℝ) := by positivity
  have hsingle : ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
      T ^ (1 / 2 : ℝ) ≤ momentNorm π N s G :=
    Finset.single_le_sum (f := fun β : ℕ × ℕ =>
      ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2) ^
            (1 / 2 : ℝ)) (fun _ _ => zero_le) hβ
  have hhalf : T ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (N.factorial : ℝ) * momentNorm π N s G := by
    calc T ^ (1 / 2 : ℝ) = ENNReal.ofReal ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
          (ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) * T ^ (1 / 2 : ℝ)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (N.factorial : ℝ) * momentNorm π N s G :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hfac) hsingle
  calc T = (T ^ (1 / 2 : ℝ)) ^ 2 := (rpow_half_sq T).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hhalf 2

/-- The pointwise bracket bound: `⟨y⟩^{2N} ≤ 3·9^N (1 + |y₀|^{2N} + |y₁|^{2N})`. -/
theorem jbracket_pow_two_mul_le (N : ℕ) (y : Vec 2) :
    jbracket y ^ (2 * N) ≤ 3 * 9 ^ N * (1 + |y 0| ^ (2 * N) + |y 1| ^ (2 * N)) := by
  have h1 := (pow_le_pow_left₀ (jbracket_pos y).le (jbracket_le y) N).trans
    (one_add_add_pow_le _ _ (abs_nonneg (y 0)) (abs_nonneg (y 1)) N)
  have hN : 0 ≤ jbracket y ^ N := pow_nonneg (jbracket_pos y).le N
  have h2 := pow_le_pow_left₀ hN h1 2
  have ha : 0 ≤ |y 0| ^ N := pow_nonneg (abs_nonneg _) N
  have hb : 0 ≤ |y 1| ^ N := pow_nonneg (abs_nonneg _) N
  calc jbracket y ^ (2 * N) = (jbracket y ^ N) ^ 2 := by ring
    _ ≤ (3 ^ N * (1 + |y 0| ^ N + |y 1| ^ N)) ^ 2 := h2
    _ = 9 ^ N * (1 + |y 0| ^ N + |y 1| ^ N) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm N 2, pow_mul]
        norm_num
    _ ≤ 9 ^ N * (3 * (1 + (|y 0| ^ N) ^ 2 + (|y 1| ^ N) ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg (|y 0| ^ N - 1), sq_nonneg (|y 1| ^ N - 1),
          sq_nonneg (|y 0| ^ N - |y 1| ^ N)]
    _ = 3 * 9 ^ N * (1 + |y 0| ^ (2 * N) + |y 1| ^ (2 * N)) := by ring

/-- **Weighted `L²` by the moment norm** (`s > 0`). -/
theorem sum_lintegral_jbracket_le_momentNorm (π : ι → ℝ) (N : ℕ) {s : ℝ} (hs : 0 < s)
    (G : ∀ v, Vec 2 → h v) (hG : ∀ v, AEStronglyMeasurable (G v) volume) :
    ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * N) * ‖G v y‖ ^ 2) ≤
      ENNReal.ofReal (3 * 9 ^ N * (1 + 2 * ((s ^ N) ^ 2)⁻¹)) *
        (ENNReal.ofReal (N.factorial : ℝ) * momentNorm π N s G) ^ 2 := by
  set c : ℝ := ((s ^ N) ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set A : ℕ × ℕ → ι → ℝ≥0∞ := fun β v =>
    eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2 with hA
  have hmem00 : ((0 : ℕ), (0 : ℕ)) ∈ momentIndices N := by simp [momentIndices]
  have hmemN0 : (N, (0 : ℕ)) ∈ momentIndices N := by simp [momentIndices]
  have hmem0N : ((0 : ℕ), N) ∈ momentIndices N := by simp [momentIndices]
  -- the three moment terms as lower integrals
  have hAm : ∀ (β : ℕ × ℕ) (v : ι), A β v = ∫⁻ y, ENNReal.ofReal
      (|s * y 0| ^ (2 * β.1) * |s * y 1| ^ (2 * β.2) * ‖G v y‖ ^ 2) := by
    intro β v
    have hm : AEStronglyMeasurable
        (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) volume :=
      ((by fun_prop : Continuous fun z : Vec 2 => (s * z 0) ^ β.1 * (s * z 1) ^ β.2)
        |>.aestronglyMeasurable).smul (hG v)
    show eLpNorm _ 2 volume ^ 2 = _
    rw [eLpNorm_two_sq hm]
    refine lintegral_congr fun y => ?_
    rw [enorm_sq_eq_ofReal, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, mul_pow,
      mul_pow, ← pow_mul, ← pow_mul, mul_comm β.1 2, mul_comm β.2 2]
  have hpt : ∀ v y, ENNReal.ofReal (jbracket y ^ (2 * N) * ‖G v y‖ ^ 2) ≤
      ENNReal.ofReal (3 * 9 ^ N) * (ENNReal.ofReal (|s * y 0| ^ (2 * 0) * |s * y 1| ^ (2 * 0) *
        ‖G v y‖ ^ 2) + ENNReal.ofReal c * ENNReal.ofReal (|s * y 0| ^ (2 * N) *
          |s * y 1| ^ (2 * 0) * ‖G v y‖ ^ 2) + ENNReal.ofReal c * ENNReal.ofReal
            (|s * y 0| ^ (2 * 0) * |s * y 1| ^ (2 * N) * ‖G v y‖ ^ 2)) := by
    intro v y
    have hsN : 0 < s ^ N := pow_pos hs N
    have hsc : c * s ^ (2 * N) = 1 := by
      rw [hc, pow_mul', inv_mul_cancel₀ (pow_ne_zero 2 hsN.ne')]
    have hy0 : |y 0| ^ (2 * N) = c * |s * y 0| ^ (2 * N) := by
      rw [abs_mul, mul_pow, abs_of_pos hs, ← mul_assoc, hsc, one_mul]
    have hy1 : |y 1| ^ (2 * N) = c * |s * y 1| ^ (2 * N) := by
      rw [abs_mul, mul_pow, abs_of_pos hs, ← mul_assoc, hsc, one_mul]
    have hb := jbracket_pow_two_mul_le N y
    rw [hy0, hy1] at hb
    have hg2 : 0 ≤ ‖G v y‖ ^ 2 := sq_nonneg _
    rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hc0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [mul_zero, pow_zero, one_mul]
    nlinarith [mul_le_mul_of_nonneg_right hb hg2]
  have hmeas : ∀ (β : ℕ × ℕ) (v : ι), AEMeasurable (fun y => ENNReal.ofReal
      (|s * y 0| ^ (2 * β.1) * |s * y 1| ^ (2 * β.2) * ‖G v y‖ ^ 2)) volume := fun β v =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((by fun_prop : Continuous fun y : Vec 2 => |s * y 0| ^ (2 * β.1) *
        |s * y 1| ^ (2 * β.2)).aemeasurable).mul ((hG v).norm.aemeasurable.pow_const 2))
  have hint : ∀ v, ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * N) * ‖G v y‖ ^ 2) ≤
      ENNReal.ofReal (3 * 9 ^ N) * (A (0, 0) v + ENNReal.ofReal c * A (N, 0) v +
        ENNReal.ofReal c * A (0, N) v) := by
    intro v
    set e00 : Vec 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (|s * y 0| ^ (2 * 0) *
      |s * y 1| ^ (2 * 0) * ‖G v y‖ ^ 2) with he00
    set eN0 : Vec 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (|s * y 0| ^ (2 * N) *
      |s * y 1| ^ (2 * 0) * ‖G v y‖ ^ 2) with heN0
    set e0N : Vec 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (|s * y 0| ^ (2 * 0) *
      |s * y 1| ^ (2 * N) * ‖G v y‖ ^ 2) with he0N
    have m00 : AEMeasurable e00 volume := hmeas (0, 0) v
    have mN0 : AEMeasurable eN0 volume := hmeas (N, 0) v
    have h00 : A (0, 0) v = ∫⁻ y, e00 y := hAm (0, 0) v
    have hN0 : A (N, 0) v = ∫⁻ y, eN0 y := hAm (N, 0) v
    have h0N : A (0, N) v = ∫⁻ y, e0N y := hAm (0, N) v
    refine (lintegral_mono (hpt v)).trans (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left' (f := fun y => e00 y + ENNReal.ofReal c * eN0 y)
        (m00.add (mN0.const_mul _)),
      lintegral_add_left' (f := e00) m00, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h00, hN0, h0N]
  set M := (ENNReal.ofReal (N.factorial : ℝ) * momentNorm π N s G) ^ 2 with hM
  have h00 := sum_eLpNorm_sq_le_momentNorm π s G hmem00
  have hN0 := sum_eLpNorm_sq_le_momentNorm π s G hmemN0
  have h0N := sum_eLpNorm_sq_le_momentNorm π s G hmem0N
  calc ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * N) * ‖G v y‖ ^ 2)
      ≤ ∑ v, ENNReal.ofReal ((π v)⁻¹) * (ENNReal.ofReal (3 * 9 ^ N) * (A (0, 0) v +
          ENNReal.ofReal c * A (N, 0) v + ENNReal.ofReal c * A (0, N) v)) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hint v
    _ = ENNReal.ofReal (3 * 9 ^ N) * ((∑ v, ENNReal.ofReal ((π v)⁻¹) * A (0, 0) v) +
          ENNReal.ofReal c * (∑ v, ENNReal.ofReal ((π v)⁻¹) * A (N, 0) v) +
          ENNReal.ofReal c * (∑ v, ENNReal.ofReal ((π v)⁻¹) * A (0, N) v)) := by
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ ≤ ENNReal.ofReal (3 * 9 ^ N) * (M + ENNReal.ofReal c * M + ENNReal.ofReal c * M) := by
        gcongr
    _ = ENNReal.ofReal (3 * 9 ^ N * (1 + 2 * c)) * M := by
        have hK : ENNReal.ofReal (3 * 9 ^ N * (1 + 2 * c)) =
            ENNReal.ofReal (3 * 9 ^ N) * (1 + 2 * ENNReal.ofReal c) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one (by positivity),
            ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        rw [hK]
        ring

end Weights

/-- **Minkowski in `L²`** when only the second summand is known to be measurable. -/
theorem lintegral_sq_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ≥0∞)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ a, (f a + g a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
      (∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  obtain ⟨H, hHm, hHle, hHeq⟩ := exists_measurable_le_lintegral_eq μ fun a => (f a + g a) ^ 2
  set f₁ : α → ℝ≥0∞ := fun a => H a ^ (1 / 2 : ℝ) - g a with hf₁
  have hf₁m : Measurable f₁ := (hHm.pow_const _).sub hg
  have hroot : ∀ a, H a ^ (1 / 2 : ℝ) ≤ f a + g a := fun a =>
    (ENNReal.rpow_le_rpow (hHle a) (by norm_num)).trans (le_of_eq (sq_rpow_half _))
  have hf₁le : ∀ a, f₁ a ≤ f a := fun a => tsub_le_iff_right.2 (hroot a)
  have hH : ∀ a, H a ≤ (f₁ a + g a) ^ 2 := fun a => by
    calc H a = (H a ^ (1 / 2 : ℝ)) ^ 2 := (rpow_half_sq _).symm
      _ ≤ (f₁ a + g a) ^ 2 := pow_le_pow_left₀ (by positivity) le_tsub_add 2
  have hmink := ENNReal.lintegral_Lp_add_le hf₁m.aemeasurable hg.aemeasurable (μ := μ)
    (p := 2) one_le_two
  simp only [Pi.add_apply, ENNReal.rpow_two] at hmink
  calc (∫⁻ a, (f a + g a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) = (∫⁻ a, H a ∂μ) ^ (1 / 2 : ℝ) := by rw [hHeq]
    _ ≤ (∫⁻ a, (f₁ a + g a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hH) (by norm_num)
    _ ≤ (∫⁻ a, f₁ a ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := hmink
    _ ≤ (∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        gcongr with a
        exact hf₁le a
end

/-! # Continuity of the Bloch fibre norms

At every `z` of the cell where the weighted lattice sums `∑_k ⟨z+k⟩^n ‖F_v(z+k)‖` and the same for
`F'` converge (almost every `z` under `n + 2` moments), the cut-off Bloch sums are `C^n` in `θ` and
linear in the datum, so the fibre derivative of `F` is that of `F'` plus that of `F - F'`, which is
bounded by `K ∑_k ⟨z+k⟩^n ‖(F - F')(z+k)‖` (`norm_thetaPartial_cutoffBloch_le`). Minkowski over
the components and then over the cell (`lintegral_sq_add_le`), Cauchy–Schwarz over the lattice
and the tiling, and the moment weights give `blochFibreContinuity`. -/

section
universe u v

section Fibre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_basisVec_eq_one (i : Fin 2) : ‖basisVec i‖ = 1 := by
  simp [basisVec, Pi.norm_single]

theorem norm_thetaPartial_le (a b : ℕ) (f : Vec 2 → E) (θ : Vec 2) :
    ‖thetaPartial a b f θ‖ ≤ ‖iteratedFDeriv ℝ (a + b) f θ‖ := by
  unfold thetaPartial
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  rw [Finset.prod_eq_one fun j _ => ?_, mul_one]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    exact norm_basisVec_eq_one 0
  · rw [Fin.append_right]
    exact norm_basisVec_eq_one 1

theorem thetaPartial_add (a b : ℕ) {f g : Vec 2 → E} {θ : Vec 2}
    (hf : ContDiffAt ℝ (a + b : ℕ) f θ) (hg : ContDiffAt ℝ (a + b : ℕ) g θ) :
    thetaPartial a b (f + g) θ = thetaPartial a b f θ + thetaPartial a b g θ := by
  unfold thetaPartial
  rw [iteratedFDeriv_add_apply hf hg]
  rfl

omit [NormedSpace ℝ E] in
theorem summable_weighted_sub {g₁ g₂ : Vec 2 → E} {z : Vec 2} {n : ℕ}
    (h₁ : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g₁ (z + fun i => (k i : ℝ))‖)
    (h₂ : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g₂ (z + fun i => (k i : ℝ))‖) :
    Summable fun k : Fin 2 → ℤ => jbracket (z + fun i => (k i : ℝ)) ^ n *
      ‖(fun y => g₁ y - g₂ y) (z + fun i => (k i : ℝ))‖ :=
  (h₁.add h₂).of_nonneg_of_le (fun _ => mul_nonneg (pow_nonneg (jbracket_pos _).le _)
    (norm_nonneg _)) fun k => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg (jbracket_pos _).le _)

variable [CompleteSpace E]

theorem cutoffBlochPhase_split (χ : Vec 2 → ℝ) {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ)
    {g₁ g₂ : Vec 2 → E} {z : Vec 2}
    (h₁ : Summable fun k : Fin 2 → ℤ => ‖g₁ (z + fun i => (k i : ℝ))‖)
    (h₂ : Summable fun k : Fin 2 → ℤ => ‖g₂ (z + fun i => (k i : ℝ))‖)
    (θ' : Vec 2) :
    χ θ' • blochPhase ψ θ' g₁ z = χ θ' • blochPhase ψ θ' g₂ z +
      χ θ' • blochPhase ψ θ' (fun y => g₁ y - g₂ y) z := by
  rw [blochPhase_sub hψ h₁ h₂, smul_sub]
  abel

/-- **One fibre component**: the derivative for `g₁` is that for `g₂` up to the weighted lattice
sum of `g₁ - g₂`. -/
theorem norm_thetaPartial_cutoffBloch_le {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {n : ℕ} {B : ℝ}
    (hB : ∀ i ≤ n, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B) {g₁ g₂ : Vec 2 → E} {z : Vec 2}
    (h₁ : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g₁ (z + fun i => (k i : ℝ))‖)
    (h₂ : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g₂ (z + fun i => (k i : ℝ))‖)
    {a b : ℕ} (hab : a + b ≤ n) (θ : Vec 2) :
    ‖thetaPartial a b (fun θ' => χ θ' • blochPhase ψ θ' g₁ z) θ‖ ≤
      ‖thetaPartial a b (fun θ' => χ θ' • blochPhase ψ θ' g₂ z) θ‖ +
        B * 2 ^ n * 2 ^ n * ∑' k : Fin 2 → ℤ, jbracket (z + fun i => (k i : ℝ)) ^ n *
          ‖g₁ (z + fun i => (k i : ℝ)) - g₂ (z + fun i => (k i : ℝ))‖ := by
  have h₃ := summable_weighted_sub h₁ h₂
  have c₂ := cutoffBloch_contDiff_bound (g := g₂) hχ hψ hB h₂
  have c₃ := cutoffBloch_contDiff_bound (g := fun y => g₁ y - g₂ y) hχ hψ hB h₃
  have hle : ((a + b : ℕ) : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hab
  have hsplit : (fun θ' => χ θ' • blochPhase ψ θ' g₁ z) =
      (fun θ' => χ θ' • blochPhase ψ θ' g₂ z) +
        fun θ' => χ θ' • blochPhase ψ θ' (fun y => g₁ y - g₂ y) z :=
    funext (cutoffBlochPhase_split χ hψ (summable_norm_of_weighted h₁)
      (summable_norm_of_weighted h₂))
  rw [hsplit, thetaPartial_add a b (c₂.1.of_le hle).contDiffAt (c₃.1.of_le hle).contDiffAt]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact (norm_thetaPartial_le a b _ θ).trans (c₃.2 (a + b) hab θ)

end Fibre

/-- Minkowski for weighted pairs. -/
theorem weighted_pair_minkowski {ι : Type*} [Fintype ι] (w p q c d : ι → ℝ≥0∞) :
    (∑ x, w x * ((p x + c x) ^ 2 + (q x + d x) ^ 2)) ^ (1 / 2 : ℝ) ≤
      (∑ x, w x * (p x ^ 2 + q x ^ 2)) ^ (1 / 2 : ℝ) +
        (∑ x, w x * (c x ^ 2 + d x ^ 2)) ^ (1 / 2 : ℝ) := by
  set r : ι → ℝ≥0∞ := fun x => w x ^ (1 / 2 : ℝ) with hr
  have hw : ∀ x, w x = r x ^ 2 := fun x => (rpow_half_sq (w x)).symm
  set P : ι × Fin 2 → ℝ≥0∞ := fun i => r i.1 * (if i.2 = 0 then p i.1 else q i.1) with hP
  set Q : ι × Fin 2 → ℝ≥0∞ := fun i => r i.1 * (if i.2 = 0 then c i.1 else d i.1) with hQ
  have hsum : ∀ e f : ι → ℝ≥0∞, ∑ x, w x * (e x ^ 2 + f x ^ 2) =
      ∑ i : ι × Fin 2, (r i.1 * (if i.2 = 0 then e i.1 else f i.1)) ^ (2 : ℝ) := by
    intro e f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Fin.sum_univ_two, mul_pow, hw x]
    ring
  have h := ENNReal.Lp_add_le Finset.univ P Q (p := 2) one_le_two
  rw [hsum p q, hsum c d]
  refine le_trans (le_of_eq ?_) h
  rw [hsum (fun x => p x + c x) (fun x => q x + d x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [hP, hQ]
  split_ifs <;> ring

/-- The weighted lattice sum `∑_k ⟨z+k⟩^n ‖g(z+k)‖` in `[0, ∞]`. -/
noncomputable def latticeSum {E : Type*} [NormedAddCommGroup E] (n : ℕ) (g : Vec 2 → E)
    (z : Vec 2) : ℝ≥0∞ :=
  ∑' k : Fin 2 → ℤ, ENNReal.ofReal
    (jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖)

theorem measurable_latticeSum {E : Type*} [NormedAddCommGroup E] (n : ℕ) {g : Vec 2 → E}
    (hg : Measurable fun y => ‖g y‖) : Measurable (latticeSum n g) := by
  have hjc : Continuous jbracket := jbracket_contDiff.continuous
  exact Measurable.tsum fun k => ENNReal.measurable_ofReal.comp
    (((hjc.measurable.comp (measurable_add_const _)).pow_const n).mul
      (hg.comp (measurable_add_const _)))

theorem latticeSum_eq_ofReal {E : Type*} [NormedAddCommGroup E] {n : ℕ} {g : Vec 2 → E}
    {z : Vec 2} (hs : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖) :
    latticeSum n g z = ENNReal.ofReal (∑' k : Fin 2 → ℤ,
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (pow_nonneg (jbracket_pos _).le _)
    (norm_nonneg _)) hs).symm

/-- A finite weighted lattice integral makes the lattice sums summable at almost every `z` of the
cell. -/
theorem ae_summable_lattice {E : Type*} [NormedAddCommGroup E] {g : Vec 2 → E}
    (hg : Measurable fun y => ‖g y‖) (n : ℕ)
    (hfin : ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖g y‖ ^ 2) ≠ ⊤) :
    ∀ᵐ z ∂(volume.restrict AVenhance.unitCube), Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖ := by
  have hint : ∫⁻ z in Applications.cellI, latticeSum n g z ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top latticeConst_ne_top hfin)
      (lintegral_cell_latticeSum_sq_le hg n)
  have hae := ae_lt_top ((measurable_latticeSum n hg).pow_const 2) hint
  rw [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube] at hae
  filter_upwards [hae] with z hz
  have hlt : latticeSum n g z ≠ ⊤ := fun h => by simp [h] at hz
  refine (ENNReal.summable_toReal hlt).congr fun k => ?_
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (jbracket_pos _).le _) (norm_nonneg _))

/-- Minkowski over the cell, with the measurable bound on the difference. -/
theorem rpow_lintegral_le_of_ae {μ : Measure (Vec 2)} {A A' G : Vec 2 → ℝ≥0∞}
    (hG : Measurable G) (h : ∀ᵐ z ∂μ, A z ^ (1 / 2 : ℝ) ≤ A' z ^ (1 / 2 : ℝ) + G z) :
    (∫⁻ z, A z ∂μ) ^ (1 / 2 : ℝ) ≤
      (∫⁻ z, A' z ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ z, G z ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hA : ∫⁻ z, A z ∂μ = ∫⁻ z, (A z ^ (1 / 2 : ℝ)) ^ 2 ∂μ :=
    lintegral_congr fun z => (rpow_half_sq _).symm
  have hA' : ∫⁻ z, A' z ∂μ = ∫⁻ z, (A' z ^ (1 / 2 : ℝ)) ^ 2 ∂μ :=
    lintegral_congr fun z => (rpow_half_sq _).symm
  rw [hA, hA']
  refine le_trans (ENNReal.rpow_le_rpow (lintegral_mono_ae (h.mono fun z hz =>
    pow_le_pow_left₀ (by positivity) hz 2)) (by norm_num)) ?_
  exact lintegral_sq_add_le (fun z => A' z ^ (1 / 2 : ℝ)) hG

section Assembly

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The integrand of `blochFibreDerivNorm`. -/
noncomputable def fibreIntegrand (π : ι → ℝ) (χ : Vec 2 → ℝ) (α : ℕ × ℕ) (G : ∀ x, Vec 2 → h x)
    (θ z : Vec 2) : ℝ≥0∞ :=
  ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (ENNReal.ofReal (‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochCos θ' (G x) z) θ‖ ^ 2) +
      ENNReal.ofReal (‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochSin θ' (G x) z) θ‖ ^ 2))

theorem blochFibreDerivNorm_eq (π : ι → ℝ) (χ : Vec 2 → ℝ) (α : ℕ × ℕ)
    (G : ∀ x, Vec 2 → h x) (θ : Vec 2) :
    blochFibreDerivNorm π χ α G θ =
      (∫⁻ z in AVenhance.unitCube, fibreIntegrand π χ α G θ z) ^ (1 / 2 : ℝ) := rfl

variable [∀ i, CompleteSpace (h i)]

theorem ofReal_sq_le_add_sq {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b + c) (ha : 0 ≤ a) :
    ENNReal.ofReal (a ^ 2) ≤ (ENNReal.ofReal b + ENNReal.ofReal c) ^ 2 := by
  rw [← ENNReal.ofReal_add hb hc, ← ENNReal.ofReal_pow (add_nonneg hb hc)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha h 2)

/-- **Pointwise fibre inequality** at a point where all lattice sums converge. -/
theorem fibreIntegrand_le {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {n : ℕ} {B : ℝ}
    (hB : ∀ i ≤ n, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B) (π : ι → ℝ) {α : ℕ × ℕ}
    (hα : α.1 + α.2 ≤ n) (θ : Vec 2) {F F' : ∀ x, Vec 2 → h x} {z : Vec 2}
    (hF : ∀ x, Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖F x (z + fun i => (k i : ℝ))‖)
    (hF' : ∀ x, Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖F' x (z + fun i => (k i : ℝ))‖) :
    fibreIntegrand π χ α F θ z ^ (1 / 2 : ℝ) ≤ fibreIntegrand π χ α F' θ z ^ (1 / 2 : ℝ) +
      ENNReal.ofReal (B * 2 ^ n * 2 ^ n) * (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (2 * latticeSum n (fun y => F x y - F' x y) z ^ 2)) ^ (1 / 2 : ℝ) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  set K : ℝ := B * 2 ^ n * 2 ^ n with hK
  have hK0 : 0 ≤ K := by positivity
  set t : ι → ℝ := fun x => ∑' k : Fin 2 → ℤ, jbracket (z + fun i => (k i : ℝ)) ^ n *
    ‖F x (z + fun i => (k i : ℝ)) - F' x (z + fun i => (k i : ℝ))‖ with ht
  have ht0 : ∀ x, 0 ≤ t x := fun x => tsum_nonneg fun _ =>
    mul_nonneg (pow_nonneg (jbracket_pos _).le _) (norm_nonneg _)
  have hlat : ∀ x, latticeSum n (fun y => F x y - F' x y) z = ENNReal.ofReal (t x) := fun x =>
    latticeSum_eq_ofReal (summable_weighted_sub (hF x) (hF' x))
  set p : ι → ℝ≥0∞ := fun x => ENNReal.ofReal
    ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochCos θ' (F' x) z) θ‖ with hp
  set q : ι → ℝ≥0∞ := fun x => ENNReal.ofReal
    ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochSin θ' (F' x) z) θ‖ with hq
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal (K * t x) with hc
  have hcos : ∀ x, ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochCos θ' (F x) z) θ‖ ≤
      ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochCos θ' (F' x) z) θ‖ + K * t x := fun x =>
    norm_thetaPartial_cutoffBloch_le hχ isUnitPhase_cos hB (hF x) (hF' x) hα θ
  have hsin : ∀ x, ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochSin θ' (F x) z) θ‖ ≤
      ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochSin θ' (F' x) z) θ‖ + K * t x := fun x =>
    norm_thetaPartial_cutoffBloch_le hχ isUnitPhase_sin hB (hF x) (hF' x) hα θ
  have hstep : fibreIntegrand π χ α F θ z ≤
      ∑ x, ENNReal.ofReal ((π x)⁻¹) * ((p x + c x) ^ 2 + (q x + c x) ^ 2) :=
    Finset.sum_le_sum fun x _ => by
      gcongr
      · exact ofReal_sq_le_add_sq (norm_nonneg _) (mul_nonneg hK0 (ht0 x)) (hcos x)
          (norm_nonneg _)
      · exact ofReal_sq_le_add_sq (norm_nonneg _) (mul_nonneg hK0 (ht0 x)) (hsin x)
          (norm_nonneg _)
  have hF'eq : fibreIntegrand π χ α F' θ z =
      ∑ x, ENNReal.ofReal ((π x)⁻¹) * (p x ^ 2 + q x ^ 2) :=
    Finset.sum_congr rfl fun x _ => by
      rw [hp, hq, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
  have hceq : ∑ x, ENNReal.ofReal ((π x)⁻¹) * (c x ^ 2 + c x ^ 2) =
      ENNReal.ofReal K ^ 2 * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (2 * latticeSum n (fun y => F x y - F' x y) z ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hc, hlat x]
    rw [ENNReal.ofReal_mul hK0]
    ring
  calc fibreIntegrand π χ α F θ z ^ (1 / 2 : ℝ)
      ≤ (∑ x, ENNReal.ofReal ((π x)⁻¹) * ((p x + c x) ^ 2 + (q x + c x) ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hstep (by norm_num)
    _ ≤ (∑ x, ENNReal.ofReal ((π x)⁻¹) * (p x ^ 2 + q x ^ 2)) ^ (1 / 2 : ℝ) +
          (∑ x, ENNReal.ofReal ((π x)⁻¹) * (c x ^ 2 + c x ^ 2)) ^ (1 / 2 : ℝ) :=
        weighted_pair_minkowski _ p q c c
    _ = _ := by
        rw [← hF'eq, hceq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]

omit [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem lintegral_Gd_sq_le {D : ∀ x, Vec 2 → h x} (hD : ∀ x, Measurable fun y => ‖D x y‖)
    (π : ι → ℝ) (n : ℕ) (K : ℝ) :
    ∫⁻ z in AVenhance.unitCube, (ENNReal.ofReal K * (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (2 * latticeSum n (D x) z ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 ≤
      ENNReal.ofReal K ^ 2 * (2 * latticeConst) * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖D x y‖ ^ 2) := by
  have hm : ∀ x, Measurable fun z => ENNReal.ofReal ((π x)⁻¹) *
      (2 * latticeSum n (D x) z ^ 2) := fun x =>
    measurable_const.mul (measurable_const.mul ((measurable_latticeSum n (hD x)).pow_const 2))
  have hcell : ∀ x, ∫⁻ z in AVenhance.unitCube, latticeSum n (D x) z ^ 2 ≤
      latticeConst * ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖D x y‖ ^ 2) := by
    intro x
    rw [← Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
    exact lintegral_cell_latticeSum_sq_le (hD x) n
  calc ∫⁻ z in AVenhance.unitCube, (ENNReal.ofReal K * (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (2 * latticeSum n (D x) z ^ 2)) ^ (1 / 2 : ℝ)) ^ 2
      = ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal K ^ 2 * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          (2 * latticeSum n (D x) z ^ 2) :=
        lintegral_congr fun z => by rw [mul_pow, rpow_half_sq]
    _ = ENNReal.ofReal K ^ 2 * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          (2 * ∫⁻ z in AVenhance.unitCube, latticeSum n (D x) z ^ 2) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun x _ => hm x),
          lintegral_finsetSum _ fun x _ => hm x]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ ENNReal.ofReal K ^ 2 * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          (2 * (latticeConst * ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) *
            ‖D x y‖ ^ 2))) := by
        gcongr with x
        exact hcell x
    _ = _ := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

theorem constant_algebra {K cW f : ℝ} (hK : 0 ≤ K) (hcW : 0 ≤ cW) (hf : 0 ≤ f) (M : ℝ≥0∞) :
    ENNReal.ofReal K ^ 2 * (2 * latticeConst) * (ENNReal.ofReal cW * (ENNReal.ofReal f * M) ^ 2) =
      (ENNReal.ofReal (K * Real.sqrt (2 * latticeConst.toReal * cW) * f) * M) ^ 2 := by
  set L := latticeConst.toReal with hLdef
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hX : 0 ≤ 2 * L * cW := by positivity
  have e1 : (K * Real.sqrt (2 * L * cW) * f) ^ 2 = K ^ 2 * 2 * L * cW * f ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hX]
    ring
  have e2 : ENNReal.ofReal (K * Real.sqrt (2 * L * cW) * f) ^ 2 =
      ENNReal.ofReal K ^ 2 * 2 * latticeConst * ENNReal.ofReal cW * ENNReal.ofReal f ^ 2 := by
    rw [← ENNReal.ofReal_pow (by positivity), e1,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K ^ 2 * 2 * L * cW),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K ^ 2 * 2 * L),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K ^ 2 * 2),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K ^ 2), ENNReal.ofReal_pow hK,
      ENNReal.ofReal_pow hf, ENNReal.ofReal_ofNat, hLdef,
      ENNReal.ofReal_toReal latticeConst_ne_top]
  rw [mul_pow (ENNReal.ofReal (K * Real.sqrt (2 * L * cW) * f)) M, e2]
  ring

/-- **D1 for strongly measurable data.** -/
theorem blochFibre_le_of_stronglyMeasurable {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {n : ℕ} {B : ℝ} (hB : ∀ i ≤ n, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B) {s : ℝ} (hs : 0 < s)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {F F' : ∀ x, Vec 2 → h x}
    (hFm : ∀ x, StronglyMeasurable (F x)) (hF'm : ∀ x, StronglyMeasurable (F' x))
    (hfin : momentNorm π (n + 2) s F < ⊤) (hfin' : momentNorm π (n + 2) s F' < ⊤)
    {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ n) (θ : Vec 2) :
    blochFibreDerivNorm π χ α F θ ≤ blochFibreDerivNorm π χ α F' θ +
      ENNReal.ofReal (B * 2 ^ n * 2 ^ n *
        Real.sqrt (2 * latticeConst.toReal * (3 * 9 ^ (n + 2) * (1 + 2 * ((s ^ (n + 2)) ^ 2)⁻¹)))
          * ((n + 2).factorial : ℝ)) *
        momentNorm π (n + 2) s (fun x z => F x z - F' x z) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  set cW : ℝ := 3 * 9 ^ (n + 2) * (1 + 2 * ((s ^ (n + 2)) ^ 2)⁻¹) with hcW
  have hcW0 : 0 ≤ cW := by positivity
  have hexp : 2 * (n + 2) = 2 * n + 4 := by ring
  -- weighted finiteness of each component
  have hfinite : ∀ G : ∀ x, Vec 2 → h x, (∀ x, StronglyMeasurable (G x)) →
      momentNorm π (n + 2) s G < ⊤ → ∀ x,
        ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖G x y‖ ^ 2) ≠ ⊤ := by
    intro G hG hGfin x
    have hsum := sum_lintegral_jbracket_le_momentNorm π (n + 2) hs G
      fun x => (hG x).aestronglyMeasurable
    rw [hexp] at hsum
    have hlt : ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖G v y‖ ^ 2) < ⊤ :=
      lt_of_le_of_lt hsum (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGfin)))
    have hx := lt_of_le_of_lt (Finset.single_le_sum (f := fun v => ENNReal.ofReal ((π v)⁻¹) *
      ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * n + 4) * ‖G v y‖ ^ 2))
      (fun _ _ => zero_le) (Finset.mem_univ x)) hlt
    have hw : ENNReal.ofReal ((π x)⁻¹) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.2 (hπ x)
    exact ((ENNReal.mul_lt_top_iff.1 hx).elim (fun h => h.2.ne)
      (fun h => h.elim (fun h => absurd h hw) fun h => h ▸ ENNReal.zero_ne_top))
  have hae : ∀ᵐ z ∂(volume.restrict AVenhance.unitCube), ∀ x,
      (Summable fun k : Fin 2 → ℤ =>
        jbracket (z + fun i => (k i : ℝ)) ^ n * ‖F x (z + fun i => (k i : ℝ))‖) ∧
      Summable fun k : Fin 2 → ℤ =>
        jbracket (z + fun i => (k i : ℝ)) ^ n * ‖F' x (z + fun i => (k i : ℝ))‖ :=
    ae_all_iff.2 fun x => (ae_summable_lattice (hFm x).norm.measurable n
      (hfinite F hFm hfin x)).and (ae_summable_lattice (hF'm x).norm.measurable n
        (hfinite F' hF'm hfin' x))
  set D : ∀ x, Vec 2 → h x := fun x z => F x z - F' x z with hD
  have hDm : ∀ x, Measurable fun y => ‖D x y‖ := fun x => ((hFm x).sub (hF'm x)).norm.measurable
  set K : ℝ := B * 2 ^ n * 2 ^ n with hK
  have hGd : Measurable fun z => ENNReal.ofReal K * (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (2 * latticeSum n (D x) z ^ 2)) ^ (1 / 2 : ℝ) :=
    measurable_const.mul ((Finset.measurable_sum _ fun x _ => measurable_const.mul
      (measurable_const.mul ((measurable_latticeSum n (hDm x)).pow_const 2))).pow_const _)
  have hmain := rpow_lintegral_le_of_ae hGd (hae.mono fun z hz =>
    fibreIntegrand_le hχ hB π hα θ (fun x => (hz x).1) fun x => (hz x).2)
  rw [blochFibreDerivNorm_eq, blochFibreDerivNorm_eq]
  refine hmain.trans (add_le_add le_rfl ?_)
  have hsumD := sum_lintegral_jbracket_le_momentNorm π (n + 2) hs D
    fun x => ((hFm x).sub (hF'm x)).aestronglyMeasurable
  rw [hexp] at hsumD
  have hint := (lintegral_Gd_sq_le hDm π n K).trans
    (mul_le_mul' (le_refl (ENNReal.ofReal K ^ 2 * (2 * latticeConst))) hsumD)
  rw [constant_algebra (by positivity) hcW0 (Nat.cast_nonneg _)] at hint
  calc (∫⁻ z in AVenhance.unitCube, (ENNReal.ofReal K * (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (2 * latticeSum n (D x) z ^ 2)) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal (K * Real.sqrt (2 * latticeConst.toReal * cW) *
          ((n + 2).factorial : ℝ)) * momentNorm π (n + 2) s D) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = _ := sq_rpow_half _

end Assembly

/-- **Continuity of the Bloch fibre norms** (`BlochFibreContinuityStatement`). -/
theorem blochFibreContinuity : BlochFibreContinuityStatement.{u, v} := by
  intro n χ hχ hc s hs
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound hχ hc n
  set C₀ : ℝ := B * 2 ^ n * 2 ^ n *
    Real.sqrt (2 * latticeConst.toReal * (3 * 9 ^ (n + 2) * (1 + 2 * ((s ^ (n + 2)) ^ 2)⁻¹))) *
      ((n + 2).factorial : ℝ) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ π hπ F F' hF hF' hfin hfin' α hα θ
  have e : ∀ x, F x =ᵐ[volume] (hF x).mk (F x) := fun x => (hF x).ae_eq_mk
  have e' : ∀ x, F' x =ᵐ[volume] (hF' x).mk (F' x) := fun x => (hF' x).ae_eq_mk
  have eD : ∀ x, (fun z => F x z - F' x z) =ᵐ[volume]
      fun z => (hF x).mk (F x) z - (hF' x).mk (F' x) z := fun x => (e x).sub (e' x)
  rw [momentNorm_congr_ae e] at hfin
  rw [momentNorm_congr_ae e'] at hfin'
  rw [blochFibreDerivNorm_congr_ae e θ, blochFibreDerivNorm_congr_ae e' θ,
    momentNorm_congr_ae eD]
  refine (blochFibre_le_of_stronglyMeasurable hχ hB hs π hπ
    (fun x => (hF x).stronglyMeasurable_mk) (fun x => (hF' x).stronglyMeasurable_mk)
    hfin hfin' hα θ).trans (add_le_add le_rfl ?_)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
end

end AVRegularity.CycleWords.Assembly
end
