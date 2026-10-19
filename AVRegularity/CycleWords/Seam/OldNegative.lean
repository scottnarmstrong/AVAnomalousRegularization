-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
public import AVRegularity.CycleWords.Seam.B1NegFullField
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # the kernel clauses of the seam's future kernel

`seamFutureKernelClausesAssembly : SeamFutureKernelClausesAssembly`: from the negative-input
Gaussian Plancherel and the finiteness of the moments of the cell low pass, with the
proved `retainedMapExists` and `retainedGaussian`, the kernel `seamFutureKernel` has smooth outputs
and is bounded `(ϖ⁻¹,-L;p_in) → (r,M;p_out)` at cost `C_{L,M}Θ₊`.

The regime is `c₀ = min c₁ᴱ c₁ᴳ`, `Q₀ = max Q₁ᴱ Q₁ᴳ`; the block is taken on the window regions
(`isWordBlock_of_seam`, `ScalarPackage.inWindow`). On a well-buffered block with `Θ₊ ≠ 0` the
kernel is the retained map of `μ(D)g`; a field of infinite negative norm is bounded trivially
(`Θ₊ > 0`); otherwise the finiteness of the low-pass moments gives the moments, retainedGaussian the amplitudes (supported in
`|θ| ≤ 2ξ_lo√η < π/2`, `consts_pos`), and Gaussian Plancherel the bound. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- `2ξ_lo < π/2` on a scalar package. -/
theorem two_xilo_lt {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (hCw : 0 ≤ K.Cw) :
    2 * K.ξlo < Real.pi / 2 := by
  obtain ⟨-, hξ, -, hCg, -, -, -, -, -, hsmall⟩ := pkg.consts_pos
  by_contra hcon
  push Not at hcon
  have h1 : (Real.pi / 2) ^ 2 ≤ (2 * K.ξlo) ^ 2 := pow_le_pow_left₀ (by positivity) hcon 2
  have h2 : 2 * (2 * K.ξlo) ^ 2 ≤ (2 + K.Cw * K.Cg) * (2 * K.ξlo) ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCw hCg.le]) (sq_nonneg _)
  nlinarith [Real.pi_pos]

/-- The word amplitude is nonnegative. -/
theorem wordTheta_nonneg {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D Nw J H : ℕ} {π : ι → ℝ} {dom : Set (ℝ × Vec 2)} {ηg : ℝ}
    (hηg : 0 ≤ ηg) {letters : Fin Nw → CycleLetter ι h D}
    (hL : ∀ i, IsCycleLetter π (letters i) dom J H) : 0 ≤ wordTheta ηg letters :=
  Finset.prod_nonneg fun i _ => mul_nonneg (hL i).theta_nonneg (by split_ifs <;> linarith)

/-- **Assembly of the kernel clauses.** -/
theorem seamFutureKernelClausesAssembly : SeamFutureKernelClausesAssembly.{u, v} := by
  intro hGN hLP K
  obtain ⟨gE, hgE, hE⟩ := retainedMapExists.{u, v} K
  obtain ⟨gG, hgG, hG⟩ := retainedGaussian.{u, v} K
  refine ⟨min gE gG, lt_min hgE hgG, fun χlo hχ μ hμ σ hσ => ?_⟩
  subst hσ
  obtain ⟨c₁E, Q₁E, hc₁E, hE'⟩ := hE (fun ξ => χlo ξ ^ (σ.pout + ∑ i, σ.KsF i + 1))
    (hχ.pow _) σ.Np σ.D σ.H σ.dF σ.KsF σ.posF
  obtain ⟨CGa, cGa, c₁G, Q₁G, hCGa, hcGa, hc₁G, hG'⟩ :=
    hG χlo hχ σ.Np σ.D σ.H σ.pout σ.dF σ.KsF σ.posF
  refine ⟨min c₁E c₁G, max Q₁E Q₁G, lt_min hc₁E hc₁G,
    fun c₁ Q₁ hc₁ hc₁le hQ₁ Cout hCout => ?_⟩
  have hB := fun L M => hGN σ.pout (wordReserveN σ.pout σ.KsF) (wordReserveP σ.pout σ.KsF) M L
    cGa Cout hcGa hCout μ χlo hμ.smooth hμ.compact hμ.even hμ.supp hχ.smooth hχ.hasCompactSupport
  choose CB hCB0 hCB using hB
  refine ⟨fun L M => CB L M * CGa, fun L M => (mul_pos (hCB0 L M) hCGa).le, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ lettersF hlet η S ηg ϖ δ hη hη1 hS hηg hηg1 hϖ hδ tF GF vF gF
    hGm hv hv0 hvs hvw hvj hg0 hg hg1 hGn regF hpkg hL hT hQ hM X₀F
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hϖ0 : 0 < ϖ := by
    rw [hϖ]
    exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖη : ϖ ≤ Real.sqrt η := by
    rw [hϖ]
    exact Real.sqrt_le_sqrt (div_le_self hη.le hS)
  have hη1' : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  have hϖ1 : ϖ ≤ 1 := hϖη.trans hη1'
  have hΘ0 : 0 ≤ wordTheta ηg lettersF := wordTheta_nonneg hηg.le hL
  -- the trivial kernels
  have hzero : seamFutureKernel σ.K χlo (σ.pout + ∑ i, σ.KsF i) hμ π lettersF η S ηg tF ϖ GF vF
      X₀F c₁ Q₁ regF = 0 →
      (∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
        ∀ x (M : ℕ), ContDiff ℝ M (seamFutureKernel σ.K χlo (σ.pout + ∑ i, σ.KsF i) hμ π
          lettersF η S ηg tF ϖ GF vF X₀F c₁ Q₁ regF g x)) ∧
      ∀ (L M : ℕ) (r : ℝ) (g : ∀ x, Vec 2 → h x), 0 < r → r ≤ max 1 Cout * ϖ⁻¹ →
        (∀ x, MemLp (g x) 2 volume) →
        weightedJetNorm π (σ.pout : ℝ) M ϖ r
            (fun x _ wd z => orderedDerivative wd (seamFutureKernel σ.K χlo
              (σ.pout + ∑ i, σ.KsF i) hμ π lettersF η S ηg tF ϖ GF vF X₀F c₁ Q₁ regF g x) z) ≤
          ENNReal.ofReal (CB L M * CGa * wordTheta ηg lettersF) *
            negJetNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ g := by
    intro h0
    rw [h0]
    refine ⟨fun g _ x M => contDiff_zero_fun, fun L M r g _ _ _ => ?_⟩
    refine (le_of_eq (weightedJetNorm_of_zero _ _ _ _ _ _ fun x a w z => ?_)).trans (by positivity)
    exact orderedDerivative_zero_function w z
  by_cases hΘ : wordTheta ηg lettersF = 0
  · exact hzero (seamFutureKernel_of_theta hμ hΘ)
  by_cases hW : IsWellBuffered c₁ Q₁ η S regF
  swap
  · exact hzero (seamFutureKernel_of_not_wellBuffered hμ hW)
  -- the retained map of the block
  have hbuf : 0 ≤ regF.buffer := hpkg.buffer_nonneg
  have hWE : IsWellBuffered c₁E Q₁E η S (regF.inWindow tF S) :=
    hW.mono (hc₁le.trans (min_le_left _ _)) ((le_max_left _ _).trans hQ₁) hS0 hbuf
  have hWG : IsWellBuffered c₁G Q₁G η S (regF.inWindow tF S) :=
    hW.mono (hc₁le.trans (min_le_right _ _)) ((le_max_right _ _).trans hQ₁) hS0 hbuf
  have hpkgW := hpkg.inWindow
  obtain ⟨R, hR⟩ := hE' σ.Jstar π lettersF hlet η S ηg tF ϖ GF vF gF (regF.inWindow tF S) hpkgW
    (isWordBlock_of_seam σ.hD hπ hη hη1 hS hηg hηg1 hϖ hGm hv hv0 hvs hvw hvj hg0 hg
      (hg1.trans (min_le_left _ _)) hGn hL hT hQ hM)
    (seam_reserve_le σ (Nat.zero_le _)) hWE X₀F
  have hRM := retainedMap_spec ⟨R, hR⟩
  refine ⟨fun g hgL x M => ?_, fun L M r g hr hrC hgL => ?_⟩
  · rw [seamFutureKernel_apply hμ hΘ hW g hgL]
    exact (hRM.band _ x).1 M
  rw [seamFutureKernel_apply hμ hΘ hW g hgL]
  have hΘpos : 0 < wordTheta ηg lettersF := lt_of_le_of_ne hΘ0 (Ne.symm hΘ)
  by_cases hfin : negJetNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ g = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by
      have := hCB0 L M
      positivity)).ne']
    exact le_top
  have hmom := hLP (σ.pout + ∑ i, σ.KsF i + 2) L μ hμ.smooth hμ.compact hμ.even hμ.supp π hπ ϖ
    hϖ0 hϖ1 g hgL (lt_top_iff_ne_top.2 hfin)
  have hmeasF : ∀ x, AEStronglyMeasurable (fourierCutoff μ (g x)) volume := fun x =>
    (Lp.aestronglyMeasurable _).congr
      (fourierCutoff_ae_seamCutoffL2 μ (Real.pi / 2) hμ.supp hμ.smooth (hgL x)).symm
  obtain ⟨A, B, hAB, hsm, -, hbd⟩ := hG' σ.Jstar π lettersF hlet η S ηg tF ϖ GF vF gF
    (regF.inWindow tF S) hpkgW
    (isWordBlock_of_seam σ.hD hπ hη hη1 hS hηg hηg1 hϖ hGm hv hv0 hvs hvw hvj hg0 hg
      (hg1.trans (min_le_right _ _)) hGn hL hT hQ hM)
    (seam_reserve_le σ le_rfl) hWG X₀F _ hRM (fun x => fourierCutoff μ (g x)) hmeasF hmom
  -- the amplitudes vanish beyond `π/2`
  have hCw : 0 ≤ σ.K.Cw := (by positivity : (0 : ℝ) ≤ Real.sqrt η *
    Real.sqrt (∑ i, vF 0 0 i ^ 2)).trans (hvw 0 0)
  have h2ξ := two_xilo_lt hpkg.toCoreScalarPackage hCw
  have hξ0 : 0 < σ.K.ξlo := hpkg.consts_pos.2.1
  have hρlt : 2 * σ.K.ξlo * Real.sqrt η < Real.pi / 2 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) hη1') h2ξ
  have hvan : ∀ x θ, Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) → A x θ = 0 ∧ B x θ = 0 := by
    intro x θ hθ
    refine (hAB x).1 θ ?_
    have h := pow_lt_pow_left₀ (hρlt.trans_le hθ) (by positivity) two_ne_zero
    rwa [Real.sq_sqrt (vecDot_self_nonneg θ)] at h
  have key := hCB L M π hπ η ϖ r (2 * σ.K.ξlo * Real.sqrt η) (CGa * wordTheta ηg lettersF) hη
    hη1 hϖ0 hϖη hr hrC (mul_nonneg hCGa.le hΘ0) _ A B g hgL hAB hsm hvan hbd
  refine key.trans_eq ?_
  rw [mul_assoc]
  rfl

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CycleWords.Assembly AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The old negative bound** (`SeamOldNegativeStatement`),
by instantiating the level claim of the adjoint word chain at the last level, the end of the old
window and smooth compactly supported tests. The scalar adjoint bound is the package's
`neg_adjoint` (power `K.Qneg k`); the flux realizations come from the compact support
of the datum. -/

theorem weightedJetNorm_congr_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    {J₁ J₂ : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v}
    (hJ : ∀ v a w, J₁ v a w =ᵐ[volume] J₂ v a w) :
    weightedJetNorm π p j s r J₁ = weightedJetNorm π p j s r J₂ := by
  unfold weightedJetNorm
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_all_iff.mpr fun w => hJ v a w] with z hz
  simp only [hz]

theorem weightedJetNorm_congr_ae_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    {J₁ J₂ : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v}
    (hJ : ∀ v a, a ≤ j → ∀ w, J₁ v a w =ᵐ[volume] J₂ v a w) :
    weightedJetNorm π p j s r J₁ = weightedJetNorm π p j s r J₂ := by
  unfold weightedJetNorm
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_all_iff.mpr fun w => hJ v a ha' w] with z hz
  simp only [hz]

/-- A smooth compactly supported test is a rapidly decaying carrier. -/
theorem smoothCompactPlaneHk_rapid {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (ϖ : ℝ) :
    IsRapidPlaneHk ϖ (smoothCompactPlaneHk K f hf hc) := by
  intro q j w
  by_cases hj : j ≤ K
  · have hcont : Continuous (fun z => polynomialMomentRoot ϖ z ^ q * ‖orderedDerivative w f z‖) :=
      ((polynomialMomentRoot_continuous ϖ).pow q).mul
        (orderedDerivative_continuous w (hf.of_le (by exact_mod_cast le_top))).norm
    have hsupp : HasCompactSupport
        (fun z => polynomialMomentRoot ϖ z ^ q * ‖orderedDerivative w f z‖) :=
      (orderedDerivative_hasCompactSupport hc w).norm.mul_left
    refine (hcont.memLp_of_hasCompactSupport hsupp).ae_eq ?_
    filter_upwards [smoothCompactPlaneHk_jet_ae K f hf hc j hj w] with z hz
    rw [hz]
  · have hz : (fun z => polynomialMomentRoot ϖ z ^ q *
        ‖planeJetOrder (smoothCompactPlaneHk K f hf hc) j w z‖) = 0 := by
      funext z
      simp [planeJetOrder, hj]
    rw [hz]
    exact MemLp.zero

/-- The seam chain is a plane chain with zero source (a separate declaration). -/
theorem isPlaneChain_of_seamChain {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D N : ℕ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hc : seamChain G letters X₀ δ κ a b v f u w) :
    IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0) u w :=
  hc

theorem levelTheta_wordAmplitudes {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {D N : ℕ} (letters : Fin N → CycleLetter ι h D) (ζ : ℝ) :
    levelTheta (wordAmplitudes letters ζ) N = wordTheta ζ letters := by
  unfold levelTheta wordTheta
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact wordAt_of_lt _ _ i.isLt

universe u v

/-- **The old negative bound.** -/
theorem seamOldNegative : SeamOldNegativeStatement.{u, v} := by
  intro K
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro σ hσK
  subst hσK
  set dd : ℕ → ℕ := wordAt σ.dO 0 with hdd
  set KK : ℕ → ℕ := wordAt σ.KsO 0 with hKK
  set Lc : ℕ → ℕ → ℝ := fun j n =>
    letterNormConst n (dd j) σ.Jstar (KK j) (wordAt σ.posO false j) with hLc
  set Ca : ℕ → ℕ → ℝ := fun k p => max (σ.K.Cneg k p) 0 with hCadef
  have hCa : ∀ k p, 0 ≤ Ca k p := fun _ _ => le_max_right _ _
  have hLc0 : ∀ j n, 0 ≤ Lc j n := fun _ _ => letterNormConst_nonneg _ _ _ _ _
  refine ⟨levelQ σ.K.Qneg dd σ.Nm σ.k, fun CH hCH p =>
    ⟨levelC Ca dd KK Lc σ.Nm σ.k p * (1 + CH) ^ levelQ σ.K.Qneg dd σ.Nm σ.k,
      mul_nonneg (levelC_nonneg Ca hCa dd KK Lc hLc0 _ _ _) (by positivity), ?_⟩⟩
  intro ι _ h _ _ _ _ _ _ π hπ lettersO hlet η S ηg ϖ δ hη hη1 hS hηg hηg1 hϖdef hδ tO SO aO bO GO
    vO gO hG hv _ hvs hvw hvj hg0 _ hg1 hGn regO pkg hwin hdur hL _ _ hmeas X₀O κO hκO f uO wO
    hsupp hchain
  obtain rfl : δ = ηg * ϖ := hδ.trans (mul_comm _ _)
  set Q := levelQ σ.K.Qneg dd σ.Nm σ.k with hQ
  have hSη : 0 < η / S := div_pos hη (by linarith)
  have hϖpos : 0 < ϖ := by rw [hϖdef]; exact Real.sqrt_pos.mpr hSη
  have hϖ1 : ϖ ≤ 1 := by
    rw [hϖdef, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_one (by linarith)).mpr (by linarith))
  have hsol := isPlaneChain_of_seamChain GO lettersO X₀O (ηg * ϖ) κO aO bO vO f uO wO hchain
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hb : ∀ t x, ∑ k, vO t x k ^ 2 ≤ (σ.K.Cw / Real.sqrt η) ^ 2 := by
    intro t x
    have h1 := hvw t x
    have h2 : Real.sqrt (∑ i, vO t x i ^ 2) ≤ σ.K.Cw / Real.sqrt η := by
      rw [le_div_iff₀ hsη, mul_comm]
      exact h1
    have h3 := Real.sqrt_le_sqrt (le_of_eq (rfl : ∑ i, vO t x i ^ 2 = ∑ i, vO t x i ^ 2))
    calc ∑ k, vO t x k ^ 2 = Real.sqrt (∑ i, vO t x i ^ 2) ^ 2 :=
          (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have hP : 1 ≤ peFactor η := by
    unfold peFactor
    have := inv_nonneg.mpr (Real.sqrt_nonneg η)
    linarith
  have hadj : ∀ (k p : ℕ) (s t : ℝ), aO ≤ s → s ≤ t → t ≤ bO →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => GO (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(vO (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * peFactor η ^ σ.K.Qneg k * (1 + (t - s)) ^ σ.K.Qneg k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w') := by
    intro k p s t has hst htb f u w hc
    refine (pkg.neg_adjoint k p s t (hwin.1.trans has) hst (htb.trans hwin.2.2) f u w hc).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have h0 : 0 ≤ 1 + (t - s) := by linarith
    have hP0 : 0 ≤ peFactor η := zero_le_one.trans hP
    gcongr
    exact le_max_left _ _
  obtain ⟨R, hR⟩ := hsupp
  have hmeas' : ∀ j x u o (k : Fin ((lettersO j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((lettersO j).edge x u o).get k).coeff wd t X z) :=
    fun j x u o k wd X z => hmeas j x u o _ (List.get_mem _ _) wd X z
  have hsumO : ∑ j, (lettersO j).order = ∑ j, σ.dO j :=
    Finset.sum_congr rfl fun j _ => (hlet j).1
  have hkJ : σ.k ≤ σ.Jstar := by
    have := σ.hk
    unfold SeamShape.Jstar
    omega
  have hreserve : ∑ j, (lettersO j).order ≤ σ.Jstar := by
    rw [hsumO]
    have := σ.hk
    omega
  have hflux := wordChain_flux_of_compactDatum σ.hD π hπ lettersO σ.Jstar σ.H aO bO hwin.2.1 hL κO
    hreserve hκO X₀O (ηg * ϖ) hmeas' vO hv hvs hη σ.K.Cvj hvj ϖ hϖpos GO hG tO SO σ.K.Cwt
    pkg.weights hwin.1 hwin.2.2 f uO wO hsol R hR (σ.K.Cw / Real.sqrt η) hb
  -- the shape identifications
  have hwo : wordOrders lettersO = dd := by
    funext i
    unfold wordOrders
    rw [hdd]
    unfold wordAt
    split_ifs with hi
    · exact (hlet ⟨i, hi⟩).1
    · rfl
  have hws : wordSlows lettersO = KK := by
    funext i
    unfold wordSlows
    rw [hKK]
    unfold wordAt
    split_ifs with hi
    · exact (hlet ⟨i, hi⟩).2.1
    · rfl
  have hwl : wordLetterConsts lettersO σ.Jstar = Lc := by
    funext j n
    unfold wordLetterConsts
    rw [hwo, hws, hLc]
    congr 1
    unfold wordAt
    split_ifs with hi
    · exact (hlet ⟨j, hi⟩).2.2
    · rfl
  have hsumrange : ∑ i ∈ Finset.range σ.Nm, dd i = ∑ i, σ.dO i := by
    rw [hdd, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => wordAt_of_lt _ _ i.isLt
  have hsumKK : ∑ i ∈ Finset.range σ.Nm, KK i = ∑ i, σ.KsO i := by
    rw [hKK, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => wordAt_of_lt _ _ i.isLt
  have hm : (∑ i ∈ Finset.range σ.Nm, wordOrders lettersO i) + 1 ≤ σ.k := by
    rw [hwo, hsumrange]
    have := σ.hk
    omega
  have hclaim := wordChain_level_bound σ.hD π hπ lettersO aO bO σ.Jstar σ.H hL GO hG gO hg0
    (hg1.trans (by norm_num)) hGn vO hv hvs hη σ.K.Cvj hvj (σ.K.Cw / Real.sqrt η) hb ϖ ηg hϖpos
    hϖ1 hηg.le hηg1 (peFactor η) hP Ca hCa σ.K.Qneg hadj X₀O κO f uO wO hsol hflux σ.Nm le_rfl
    σ.k hm (by omega) p bO ⟨hwin.2.1, le_rfl⟩
  rw [hwo, hws, hwl, levelTheta_wordAmplitudes, hsumKK] at hclaim
  -- the negative norm through smooth compactly supported tests
  unfold negJetNorm
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hφn => ?_
  set Φ : ∀ x, PlaneHk Set.univ σ.k (h x) := fun x =>
    smoothCompactPlaneHk σ.k (φ x) (hφ x).1 (hφ x).2 with hΦdef
  have hpair : ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (planeValue (uO (Fin.last σ.Nm) x bO) z) (φ x z) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κO (Fin.last σ.Nm) x)
        (uO (Fin.last σ.Nm) x bO)) (planeHkValueOperator σ.k (Φ x)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [planeJetL2_value_ae (uO (Fin.last σ.Nm) x bO), planeJetL2_value_ae (Φ x),
      smoothCompactPlaneHk_jet_ae σ.k (φ x) (hφ x).1 (hφ x).2 0 (Nat.zero_le _) Fin.elim0]
      with z h1 h2 h3
    rw [h1, h2, h3, orderedDerivative_zero]
    rfl
  rw [hpair]
  have hΦn : weightedJetNorm π (-(p : ℝ)) σ.k ϖ 1
      (fun x i w z => planeJetOrder (Φ x) i w z) ≤ 1 := by
    rw [weightedJetNorm_congr_ae_le π (-(p : ℝ)) σ.k ϖ 1 (J₂ := fun x _ wd z =>
      orderedDerivative wd (φ x) z) fun x a ha w =>
        smoothCompactPlaneHk_jet_ae σ.k (φ x) (hφ x).1 (hφ x).2 a ha w]
    exact hφn
  have hb2 := hclaim Φ fun x => smoothCompactPlaneHk_rapid σ.k (φ x) (hφ x).1 (hφ x).2 ϖ
  refine hb2.trans ?_
  have hθ0 : 0 ≤ wordTheta ηg lettersO := by
    rw [← levelTheta_wordAmplitudes]
    refine levelTheta_nonneg _ (fun i => ?_) _
    unfold wordAmplitudes wordAt
    split_ifs
    · exact mul_nonneg (hL _).theta_nonneg (by split <;> positivity)
    · exact zero_le_one
  have hC0 : 0 ≤ levelC Ca dd KK Lc σ.Nm σ.k p := levelC_nonneg Ca hCa dd KK Lc hLc0 _ _ _
  have hP0 : 0 ≤ peFactor η ^ Q := pow_nonneg (zero_le_one.trans hP) _
  have hT : (1 + (bO - aO)) ^ Q ≤ (1 + CH) ^ Q * (1 + S) ^ Q := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [hwin.2.1]) ?_ Q
    nlinarith [hdur, hCH, hS]
  calc ENNReal.ofReal (levelC Ca dd KK Lc σ.Nm σ.k p * wordTheta ηg lettersO * peFactor η ^ Q *
          (1 + (bO - aO)) ^ Q) * weightedJetNorm π (-(p : ℝ)) σ.k ϖ 1
          (fun x i w z => planeJetOrder (Φ x) i w z) *
        weightedJetNorm π ((p + ∑ i, σ.KsO i : ℕ) : ℝ) 0 ϖ 1
          (fun x i w z => planeJetOrder (f x) i w z)
      ≤ ENNReal.ofReal (levelC Ca dd KK Lc σ.Nm σ.k p * wordTheta ηg lettersO * peFactor η ^ Q *
          (1 + (bO - aO)) ^ Q) * 1 *
        weightedJetNorm π ((p + ∑ i, σ.KsO i : ℕ) : ℝ) 0 ϖ 1
          (fun x i w z => planeJetOrder (f x) i w z) := by gcongr
    _ ≤ _ := by
        rw [mul_one]
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        calc levelC Ca dd KK Lc σ.Nm σ.k p * wordTheta ηg lettersO * peFactor η ^ Q *
              (1 + (bO - aO)) ^ Q
            ≤ levelC Ca dd KK Lc σ.Nm σ.k p * wordTheta ηg lettersO * peFactor η ^ Q *
              ((1 + CH) ^ Q * (1 + S) ^ Q) :=
              mul_le_mul_of_nonneg_left hT (mul_nonneg (mul_nonneg hC0 hθ0) hP0)
          _ = _ := by ring

end AVRegularity.CycleWords.Seam
end
