-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.WeakContStatements
import AVRegularity.CycleWords.Seam.OldNegative
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleWords.MixedWords.Discard.QuietOp
import AVRegularity.CycleWords.Seam.B1PlainNeg
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Seam
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # Weak continuity on rough data from the level claim

`ChainWeakContinuityStatement` from `WeakContLevelBoundStatement`: the level claim at the last
level, the end of the block, weight `p = 0` and the smooth compactly supported test; the scalar
reversed-adjoint bound is the package's `neg_adjoint`, as in `seamOldNegative`. The weighted `L²`
norm of the datum at weight `∑K_i` is bounded by its moment norm of order `m + ∑K_i`
(`sum_lintegral_jbracket_le_momentNorm`). The constant does not depend on the slots. -/

universe u v

/-- The weighted `L²` norm of a datum at weight `q` is bounded by its moment norm of any order
`n ≥ q` (`0 < ϖ ≤ 1`). -/
theorem weakCont_datum_le_momentNorm {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) {κ0 : ι → ℕ} (f : ∀ x, PlaneHk Set.univ (κ0 x) (h x)) (q n : ℕ) (hq : q ≤ n)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) :
    weightedJetNorm π ((q : ℕ) : ℝ) 0 ϖ 1 (fun x i w z => planeJetOrder (f x) i w z) ≤
      ENNReal.ofReal (Real.sqrt (3 * 9 ^ n * (1 + 2 * ((ϖ ^ n) ^ 2)⁻¹)) * (n.factorial : ℝ)) *
        momentNorm π n ϖ (fun x => planeValue (f x)) := by
  set c₁ : ℝ := 3 * 9 ^ n * (1 + 2 * ((ϖ ^ n) ^ 2)⁻¹) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hFm : ∀ x, AEStronglyMeasurable (planeValue (f x)) volume := fun x =>
    planeJetOrder_aestronglyMeasurable (f x) 0 _
  -- the weighted integrand of each component
  set gw : ι → Vec 2 → ℝ := fun x z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((q : ℝ) / 2) *
    Real.sqrt (∑ w : DerivativeWord2 0, ‖planeJetOrder (f x) 0 w z‖ ^ 2) with hgw
  have hsq : ∀ x z, Real.sqrt (∑ w : DerivativeWord2 0, ‖planeJetOrder (f x) 0 w z‖ ^ 2) =
      ‖planeValue (f x) z‖ := by
    intro x z
    have : Unique (DerivativeWord2 0) :=
      { default := fun i => i.elim0, uniq := fun w => funext fun i => i.elim0 }
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    exact congrArg (fun w => ‖planeJetOrder (f x) 0 w z‖) (funext fun i => i.elim0)
  have hgm : ∀ x, AEStronglyMeasurable (gw x) volume := by
    intro x
    have hcont : Continuous fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((q : ℝ) / 2) := by
      refine Continuous.rpow_const (by fun_prop) fun z => Or.inl ?_
      have : 0 ≤ ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by positivity
      linarith
    have he : gw x = fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((q : ℝ) / 2) *
        ‖planeValue (f x) z‖ := by
      funext z
      rw [hgw]
      simp only [hsq]
    rw [he]
    exact hcont.aestronglyMeasurable.mul (hFm x).norm
  have hpt : ∀ x z, gw x z ^ 2 ≤ jbracket z ^ (2 * n) * ‖planeValue (f x) z‖ ^ 2 := by
    intro x z
    have hs0 : 0 ≤ z 0 ^ 2 + z 1 ^ 2 := by positivity
    have hb0 : 0 ≤ ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by positivity
    have hb1 : (1 : ℝ) ≤ 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by linarith
    have hϖ2 : ϖ ^ 2 ≤ 1 := pow_le_one₀ hϖ.le hϖ1
    have hle : 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) ≤ 1 + (z 0 ^ 2 + z 1 ^ 2) := by
      nlinarith
    have hj2 : jbracket z ^ 2 = 1 + (z 0 ^ 2 + z 1 ^ 2) := by
      unfold jbracket
      exact Real.sq_sqrt (by linarith)
    have hw : ((1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((q : ℝ) / 2)) ^ 2 =
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ q := by
      have h2 : (q : ℝ) / 2 * ((2 : ℕ) : ℝ) = (q : ℝ) := by norm_num
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), h2, Real.rpow_natCast]
    have hwle : (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ q ≤ jbracket z ^ (2 * n) := by
      rw [pow_mul, hj2]
      calc (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ q ≤ (1 + (z 0 ^ 2 + z 1 ^ 2)) ^ q :=
            pow_le_pow_left₀ (by linarith) hle q
        _ ≤ (1 + (z 0 ^ 2 + z 1 ^ 2)) ^ n := pow_le_pow_right₀ (by linarith) hq
    rw [hgw]
    simp only [hsq]
    rw [mul_pow, hw]
    exact mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
  have hsum : ∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (gw v) 2 volume ^ 2 ≤
      (ENNReal.ofReal (Real.sqrt c₁) * (ENNReal.ofReal (n.factorial : ℝ) *
        momentNorm π n ϖ (fun x => planeValue (f x)))) ^ 2 := by
    have h1 := sum_lintegral_jbracket_le_momentNorm π n hϖ (fun x => planeValue (f x)) hFm
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hc₁0]
    refine le_trans (Finset.sum_le_sum fun v _ => ?_) h1
    rw [eLpNorm_two_sq_real (gw v) (hgm v)]
    exact mul_le_mul' le_rfl (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpt v z))
  have hroot : (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (gw v) 2 volume ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt c₁) * (ENNReal.ofReal (n.factorial : ℝ) *
        momentNorm π n ϖ (fun x => planeValue (f x))) := by
    refine (ENNReal.rpow_le_rpow hsum (by norm_num)).trans (le_of_eq ?_)
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold weightedJetNorm
  rw [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, ENNReal.ofReal_one, one_mul]
  refine hroot.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]

/-- Weak continuity of the endpoint on rough data from the level claim
for every chain. -/
theorem chainWeakContinuity_of_levelBound (hLB : WeakContLevelBoundStatement.{u, v}) :
    ChainWeakContinuityStatement.{u, v} := by
  unfold WeakContLevelBoundStatement at hLB
  intro K
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro Nw D H Kf m d Ks pos ι _ h _ _ _ _ _ _ J π letters hlet η S ηg t₀ ϖ G v g reg pkg hB hJ
    X₀ Φ hΦ
  have hη := hB.hη
  have hS := hB.hS
  have hSη : 0 < η / S := div_pos hη (by linarith)
  have hϖpos : 0 < ϖ := by rw [hB.hϖ]; exact Real.sqrt_pos.mpr hSη
  have hϖ1 : ϖ ≤ 1 := by
    rw [hB.hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_one (by linarith)).mpr (by linarith [hB.hη1]))
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ (K.Cw / Real.sqrt η) ^ 2 := by
    intro t x
    have h1 := hB.hvw t x
    have h2 : Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw / Real.sqrt η := by
      rw [le_div_iff₀ hsη, mul_comm]
      exact h1
    calc ∑ k, v t x k ^ 2 = Real.sqrt (∑ i, v t x i ^ 2) ^ 2 :=
          (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have hP : 1 ≤ peFactor η := by
    unfold peFactor
    have := inv_nonneg.mpr (Real.sqrt_nonneg η)
    linarith
  obtain ⟨Ca, hCadef⟩ : ∃ Ca : ℕ → ℕ → ℝ, Ca = fun k p => max (K.Cneg k p) 0 := ⟨_, rfl⟩
  have hCa : ∀ k p, 0 ≤ Ca k p := fun k p => by rw [hCadef]; exact le_max_right _ _
  have hadj : ∀ (k p : ℕ) (s t : ℝ), t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * peFactor η ^ K.Qneg k * (1 + (t - s)) ^ K.Qneg k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w') := by
    intro k p s t has hst htb f u w hc
    refine (pkg.neg_adjoint k p s t has hst htb f u w hc).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have h0 : 0 ≤ 1 + (t - s) := by linarith
    have hP0 : 0 ≤ peFactor η := zero_le_one.trans hP
    have hle : K.Cneg k p ≤ Ca k p := by rw [hCadef]; exact le_max_left _ _
    gcongr
  -- the shape of the word
  have hsumO : ∑ i ∈ Finset.range Nw, wordOrders letters i = ∑ i, d i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => (wordAt_of_lt _ _ i.isLt).trans (hlet i).1
  have hsumK : ∑ i ∈ Finset.range Nw, wordSlows letters i = ∑ i, Ks i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => (wordAt_of_lt _ _ i.isLt).trans (hlet i).2.1
  have hdJ : ∑ i, d i ≤ J := by
    refine le_trans ?_ hJ
    unfold wordReserveJstar wordReserveKstar
    omega
  -- the test as a rapidly decaying carrier of order `∑d + 1`
  obtain ⟨Φc, hΦc⟩ : ∃ Φc : ∀ x, PlaneHk Set.univ ((∑ i, d i) + 1) (h x),
      Φc = fun x => smoothCompactPlaneHk ((∑ i, d i) + 1) (Φ x) (hΦ x).1 (hΦ x).2 := ⟨_, rfl⟩
  have hΦr : ∀ x, IsRapidPlaneHk ϖ (Φc x) := fun x => by
    rw [hΦc]
    exact smoothCompactPlaneHk_rapid _ (Φ x) (hΦ x).1 (hΦ x).2 ϖ
  -- the constants
  obtain ⟨Clev, hClev⟩ : ∃ Clev : ℝ, Clev = levelC Ca (wordOrders letters) (wordSlows letters)
      (wordLetterConsts letters J) Nw ((∑ i, d i) + 1) 0 *
        levelTheta (wordAmplitudes letters ηg) Nw *
        peFactor η ^ levelQ K.Qneg (wordOrders letters) Nw ((∑ i, d i) + 1) *
        (1 + (t₀ + S - t₀)) ^ levelQ K.Qneg (wordOrders letters) Nw ((∑ i, d i) + 1) :=
    ⟨_, rfl⟩
  have hClev0 : 0 ≤ Clev := by
    rw [hClev]
    have hθ : ∀ i, 0 ≤ wordAmplitudes letters ηg i := by
      intro i
      unfold wordAmplitudes wordAt
      split_ifs
      · exact mul_nonneg (hB.hlet _).theta_nonneg (by split <;> linarith [hB.hηg])
      · exact zero_le_one
    have h1 := levelC_nonneg Ca hCa (wordOrders letters) (wordSlows letters)
      (wordLetterConsts letters J) (fun _ _ => letterNormConst_nonneg _ _ _ _ _) Nw
      ((∑ i, d i) + 1) 0
    have h2 := levelTheta_nonneg _ hθ Nw
    have h3 : 0 ≤ peFactor η := zero_le_one.trans hP
    have h4 : 0 ≤ 1 + (t₀ + S - t₀) := by linarith
    positivity
  obtain ⟨AΦ, hAΦ⟩ : ∃ AΦ : ℝ≥0∞, AΦ = weightedJetNorm π (-((0 : ℕ) : ℝ)) ((∑ i, d i) + 1) ϖ 1
      (fun x i w z => planeJetOrder (Φc x) i w z) := ⟨_, rfl⟩
  have hAΦfin : AΦ ≠ ⊤ := by
    rw [hAΦ, Nat.cast_zero]
    exact weightedJetNorm_neg_ne_top π Φc 0 ϖ le_rfl _
  obtain ⟨Cmom, hCmom⟩ : ∃ Cmom : ℝ, Cmom =
      Real.sqrt (3 * 9 ^ wordReserveN m Ks * (1 + 2 * ((ϖ ^ wordReserveN m Ks) ^ 2)⁻¹)) *
        ((wordReserveN m Ks).factorial : ℝ) := ⟨_, rfl⟩
  have hCmom0 : 0 ≤ Cmom := by
    rw [hCmom]
    positivity
  refine ⟨Clev * AΦ.toReal * Cmom,
    mul_nonneg (mul_nonneg hClev0 ENNReal.toReal_nonneg) hCmom0, ?_⟩
  intro κ _ _ f u w _ hchain
  have hsol : IsPlaneChain (wordChainData G letters X₀ (ηg * ϖ)) κ t₀ (t₀ + S) v f
      (fun _ _ _ => 0) u w := by
    rw [mul_comm]
    exact hchain
  have hclaim := hLB hB.hD π hB.hπ letters t₀ (t₀ + S) J H hB.hlet hB.hmeas G hB.hGm g hB.hg0
    hB.hg₁ hB.hGn v hB.hv hB.hvs hη K.Cvj hB.hvj (K.Cw / Real.sqrt η) hb ϖ ηg hϖpos hϖ1
    hB.hηg.le hB.hηg1 (peFactor η) hP Ca hCa K.Qneg hadj X₀ κ f u w hsol Nw le_rfl
    ((∑ i, d i) + 1) (by rw [hsumO]) (by omega) 0 (t₀ + S) ⟨by linarith, le_rfl⟩ Φc hΦr
  -- the pairing with the test
  have hpair : ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (planeValue (u (Fin.last Nw) x (t₀ + S)) z) (Φ x z) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ (Fin.last Nw) x)
        (u (Fin.last Nw) x (t₀ + S))) (planeHkValueOperator ((∑ i, d i) + 1) (Φc x)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have h3 := smoothCompactPlaneHk_jet_ae ((∑ i, d i) + 1) (Φ x) (hΦ x).1 (hΦ x).2 0
      (Nat.zero_le _) Fin.elim0
    rw [hΦc]
    filter_upwards [planeJetL2_value_ae (u (Fin.last Nw) x (t₀ + S)),
      planeJetL2_value_ae (smoothCompactPlaneHk ((∑ i, d i) + 1) (Φ x) (hΦ x).1 (hΦ x).2), h3]
      with z h1 h2 h3
    rw [h1, h2, h3, orderedDerivative_zero]
    rfl
  rw [hpair]
  have hdat := weakCont_datum_le_momentNorm π f (0 + ∑ i ∈ Finset.range Nw, wordSlows letters i)
    (wordReserveN m Ks) (by rw [hsumK]; unfold wordReserveN; omega) ϖ hϖpos hϖ1
  rw [← hCmom] at hdat
  have hclaim' : ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ
        (planeHkValueOperator (κ (Fin.last Nw) x) (u (Fin.last Nw) x (t₀ + S)))
        (planeHkValueOperator ((∑ i, d i) + 1) (Φc x))| ≤
      ENNReal.ofReal Clev * AΦ *
        weightedJetNorm π ((0 + ∑ i ∈ Finset.range Nw, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
          (fun x i w z => planeJetOrder (f x) i w z) := by
    rw [hClev, hAΦ]
    exact hclaim
  refine hclaim'.trans ?_
  calc ENNReal.ofReal Clev * AΦ *
        weightedJetNorm π ((0 + ∑ i ∈ Finset.range Nw, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
          (fun x i w z => planeJetOrder (f x) i w z)
      ≤ ENNReal.ofReal Clev * ENNReal.ofReal AΦ.toReal *
          (ENNReal.ofReal Cmom * momentNorm π (wordReserveN m Ks) ϖ
            (fun x => planeValue (f x))) := by
        rw [ENNReal.ofReal_toReal hAΦfin]
        exact mul_le_mul' le_rfl hdat
    _ = ENNReal.ofReal (Clev * AΦ.toReal * Cmom) *
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hClev0 ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul hClev0]
        ring

end AVRegularity.CycleWords.Discard
end

section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open AVRegularity.CycleWords.Seam
open scoped Topology
namespace AVRegularity.CycleWords.Discard

/-! # The step of the adjoint word chain for every chain

`weakContStepDuality : WeakContStepDualityStatement`. The scalar split-weight duality (`weakCont_component_duality`) for each coordinate of each component, the sum
over an orthonormal basis (`weakCont_vector_of_components`), and the transposition of the letter
(`letterTranspose_duality`), which needs no weight on the chain. -/

universe u v

section Assemble

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- At one time: the coordinate flux pairings add up to the pairing with the assembled test. -/
theorem weakCont_assemble_pointwise {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E)
    (mm : ℕ) (hmm : 1 ≤ mm) (ψe : n → PlaneHk Set.univ mm ℝ)
    (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hint : ∀ e (k : Fin 2), Integrable (fun z => inner ℝ (B e) (F z k) *
      (planeH1GradientOperator (truncatePlaneHk hmm (ψe e)) k : Vec 2 → ℝ) z) volume) :
    ∑ e, ∫ z, ∑ k : Fin 2, inner ℝ (B e) (F z k) *
        (planeH1GradientOperator (truncatePlaneHk hmm (ψe e)) k : Vec 2 → ℝ) z =
      ∫ z, ∑ k : Fin 2, inner ℝ (F z k)
        ((planeHkAssemble B ψe).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
  rw [← integral_finsetSum _ fun e _ => integrable_finsetSum _ fun k _ => hint e k]
  refine integral_congr_ae ?_
  have hG : ∀ e (k : Fin 2),
      (planeH1GradientOperator (truncatePlaneHk hmm (ψe e)) k : Vec 2 → ℝ) =ᵐ[volume]
        (ψe e).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ := by
    intro e k
    rw [planeH1Gradient_truncate_eq]
    exact planeJetL2_ae (ψe e) _
  have hA : ∀ k : Fin 2,
      (planeHkAssemble B ψe).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ =ᵐ[volume]
        fun z => ∑ e, (ψe e).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z • B e := by
    intro k
    have h1 := planeJetL2_ae (planeHkAssemble B ψe) ⟨⟨1, by omega⟩, fun _ => k⟩
    rw [planeJetL2_assemble] at h1
    have h2 := Lp.coeFn_finsetSum Finset.univ
      (fun e => planeFiberInjectionCLM (B e) (planeJetL2 (ψe e) ⟨⟨1, by omega⟩, fun _ => k⟩))
    have h3 : ∀ e, planeFiberInjectionCLM (B e)
        (planeJetL2 (ψe e) ⟨⟨1, by omega⟩, fun _ => k⟩) =ᵐ[volume]
        fun z => (ψe e).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z • B e := by
      intro e
      filter_upwards [((ContinuousLinearMap.id ℝ ℝ).smulRight (B e)).coeFn_compLpL
        (planeJetL2 (ψe e) ⟨⟨1, by omega⟩, fun _ => k⟩),
        planeJetL2_ae (ψe e) ⟨⟨1, by omega⟩, fun _ => k⟩] with z h4 h5
      change planeFiberInjectionCLM (B e) (planeJetL2 (ψe e) ⟨⟨1, by omega⟩, fun _ => k⟩) z =
        (planeJetL2 (ψe e) ⟨⟨1, by omega⟩, fun _ => k⟩ : Vec 2 → ℝ) z • B e at h4
      rw [h4, h5]
    filter_upwards [h1, h2, ae_all_iff.mpr h3] with z h1 h2 h3
    rw [← h1, h2, Finset.sum_apply]
    exact Finset.sum_congr rfl fun e _ => h3 e
  filter_upwards [ae_all_iff.mpr fun e => ae_all_iff.mpr (hG e), ae_all_iff.mpr hA]
    with z hGz hAz
  simp only [hGz, hAz, inner_sum, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
  rw [real_inner_comm (B e) (F z k), mul_comm]

omit [FiniteDimensional ℝ E] in
/-- **Vector duality of one component from its coordinates.** -/
theorem weakCont_vector_of_components {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E)
    {a b : ℝ} (hab : a ≤ b) {K : ℕ} (Ub fa : PlaneHk Set.univ K E)
    (mm : ℕ) (hmm : 1 ≤ mm) (Φ : PlaneHk Set.univ mm E) (ψ : n → ℝ → PlaneHk Set.univ mm ℝ)
    (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hint : ∀ e, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2,
      Integrable (fun z => inner ℝ (B e) (Fl r z k) *
        (planeH1GradientOperator (truncatePlaneHk hmm (ψ e (-r))) k : Vec 2 → ℝ) z) volume)
    (hII : ∀ e, IntervalIntegrable (fun r => ∫ z, ∑ k : Fin 2, inner ℝ (B e) (Fl r z k) *
      (planeH1GradientOperator (truncatePlaneHk hmm (ψ e (-r))) k : Vec 2 → ℝ) z) volume a b)
    (hid : ∀ e, inner ℝ (planeFiberCoordinateCLM (B e) (planeHkValueOperator K Ub))
        (planeHkValueOperator mm (planeHkCoord (B e) Φ)) =
      inner ℝ (planeFiberCoordinateCLM (B e) (planeHkValueOperator K fa))
          (planeHkValueOperator mm (ψ e (-a))) -
        ∫ r in a..b, ∫ z, ∑ k : Fin 2, inner ℝ (B e) (Fl r z k) *
          (planeH1GradientOperator (truncatePlaneHk hmm (ψ e (-r))) k : Vec 2 → ℝ) z) :
    IntervalIntegrable (fun r => ∫ z, ∑ k : Fin 2, inner ℝ (Fl r z k)
        ((planeHkAssemble B (fun e => ψ e (-r))).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z))
        volume a b ∧
      inner ℝ (planeHkValueOperator K Ub) (planeHkValueOperator mm Φ) =
        inner ℝ (planeHkValueOperator K fa)
            (planeHkValueOperator mm (planeHkAssemble B (fun e => ψ e (-a)))) -
          ∫ r in a..b, ∫ z, ∑ k : Fin 2, inner ℝ (Fl r z k)
            ((planeHkAssemble B (fun e => ψ e (-r))).toFunction.jet
              ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
  have hae : ∀ᵐ r ∂volume.restrict (Icc a b),
      ∑ e, (∫ z, ∑ k : Fin 2, inner ℝ (B e) (Fl r z k) *
        (planeH1GradientOperator (truncatePlaneHk hmm (ψ e (-r))) k : Vec 2 → ℝ) z) =
      ∫ z, ∑ k : Fin 2, inner ℝ (Fl r z k)
        ((planeHkAssemble B (fun e => ψ e (-r))).toFunction.jet
          ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
    filter_upwards [ae_all_iff.mpr hint] with r hr
    exact weakCont_assemble_pointwise B mm hmm (fun e => ψ e (-r)) (Fl r) hr
  have hsumI : Integrable (fun r => ∑ e, ∫ z, ∑ k : Fin 2, inner ℝ (B e) (Fl r z k) *
      (planeH1GradientOperator (truncatePlaneHk hmm (ψ e (-r))) k : Vec 2 → ℝ) z)
      (volume.restrict (Icc a b)) :=
    integrable_finsetSum _ fun e _ =>
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hII e)
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hsumI.congr hae), ?_⟩
  rw [inner_eq_sum_planeFiberCoordinate B]
  simp only [planeHkValueOperator_eq_planeJetL2, planeJetL2_assemble, inner_assemble]
  simp only [planeHkValueOperator_eq_planeJetL2, planeJetL2_coord] at hid
  rw [Finset.sum_congr rfl fun e _ => hid e, Finset.sum_sub_distrib,
    ← intervalIntegral.integral_finsetSum fun e _ => hII e]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hae] with r hr hmem
  rw [uIoc_of_le hab] at hmem
  exact hr ⟨hmem.1.le, hmem.2⟩

end Assemble

/-- Inverse-mass sum of component identities with a time integral. -/
theorem weakCont_sum_components {ι : Type*} [Fintype ι] (π : ι → ℝ) {a b : ℝ}
    (L R : ι → ℝ) (Hx : ι → ℝ → ℝ) (hI : ∀ x, IntervalIntegrable (Hx x) volume a b)
    (hid : ∀ x, L x = R x - ∫ r in a..b, Hx x r) :
    ∑ x, (π x)⁻¹ * L x = ∑ x, (π x)⁻¹ * R x - ∫ r in a..b, ∑ x, (π x)⁻¹ * Hx x r := by
  rw [intervalIntegral.integral_finsetSum fun x _ => (hI x).const_mul _,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intervalIntegral.integral_const_mul, ← mul_sub, hid x]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- **Vector duality of one component of a level of an arbitrary chain**, from the two facts of
(17a) at that component. -/
theorem weakCont_component_vector_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (j : Fin N) (x : ι)
    (hcut : ∀ n : ℕ, ∃ S : ℝ → PlaneFluxL2 (h x), MemLp S 2 (volume.restrict (Icc a b)) ∧
      ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume,
        z ∈ Metric.ball (0 : Vec 2) ((n : ℝ) + 1) → (S r k : Vec 2 → h x) z =
          wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z k)
    (wt : Vec 2 → ℝ) (hwc : Continuous wt) (hw1 : ∀ z, 0 < wt z)
    (A : ℝ → ℝ) (hA0 : ∀ r, 0 ≤ A r) (hA : IntegrableOn A (Icc a b))
    (hwt : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2,
      eLpNorm (fun z => (wt z)⁻¹ •
        wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z k) 2 volume ≤
        ENNReal.ofReal (A r))
    {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ (h x)) (mm : ℕ) (hmm : 1 ≤ mm)
    (Φ : PlaneHk Set.univ mm (h x))
    (ψ : n → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ mm ℝ)
    (ψw : n → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (mm + 1) ℝ)
    (hψ : ∀ e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => mm)
      (-b) (-a) (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B e) Φ)
      (fun _ _ _ => 0) (ψ e) (ψw e))
    (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hΨv : ∀ r ∈ Icc a b, ∀ e, eLpNorm (fun z => wt z *
      (planeHkValueOperator 1 (truncatePlaneHk hmm (ψ e 0 () (-r))) : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd)
    (hΨg : ∀ r ∈ Icc a b, ∀ e, ∀ k : Fin 2, eLpNorm (fun z => wt z *
      (planeH1GradientOperator (truncatePlaneHk hmm (ψ e 0 () (-r))) k : Vec 2 → ℝ) z) 2
        volume ≤ ENNReal.ofReal Bd) :
    IntervalIntegrable (fun r => ∫ z, ∑ k : Fin 2, inner ℝ
        (wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z k)
        ((planeHkAssemble B (fun e => ψ e 0 () (-r))).toFunction.jet
          ⟨⟨1, by omega⟩, fun _ => k⟩ z)) volume a b ∧
      inner ℝ (planeHkValueOperator (κ j.succ x) (U (j.succ, x) b))
          (planeHkValueOperator mm Φ) =
        inner ℝ (planeHkValueOperator (κ j.succ x) (f (j.succ, x)))
            (planeHkValueOperator mm (planeHkAssemble B (fun e => ψ e 0 () (-a)))) -
          ∫ r in a..b, ∫ z, ∑ k : Fin 2, inner ℝ
            (wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z k)
            ((planeHkAssemble B (fun e => ψ e 0 () (-r))).toFunction.jet
              ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
  have hcomp := fun e => weakCont_component_duality hD G hG letters X₀ δ κ a b hab v hv M
    hb f U Uw hsol (j.succ, x) hcut wt hwc hw1 A hA0 hA hwt (B e) mm hmm
    (fun _ => planeHkCoord (B e) Φ) (ψ e) (ψw e) (hψ e) Bd hBd
    (fun r hr => hΨv r hr e) (fun r hr => hΨg r hr e)
  exact weakCont_vector_of_components B hab (U (j.succ, x) b) (f (j.succ, x)) mm hmm
    Φ (fun e r => ψ e 0 () r)
    (fun r z => wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z)
    (fun e => (hcomp e).1) (fun e => (hcomp e).2.1) (fun e => (hcomp e).2.2)

/-- At one time: the letter flux against the assembled test is the level below against the
transposed letter (`letterTranspose_duality`; no weight on the chain). -/
theorem weakCont_transpose_at_time (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ)
    (j : Fin N) (m d : ℕ) (hd : 1 ≤ d)
    (hempty : ∀ x u (o : Finset.Icc 2 D), d < o.1 → (letters j).edge x u o = [])
    (r : ℝ) (Uj : ∀ u, PlaneHk Set.univ (κ j.castSucc u) (h u))
    (Uwj : ∀ u, PlaneHk Set.univ (κ j.castSucc u + 1) (h u))
    (htr : ∀ u, truncatePlaneHk (Nat.le_succ _) (Uwj u) = Uj u)
    (Uwr : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hUwr : ∀ u, Uwr (j.castSucc, u) = Uwj u)
    (Ψ : ∀ x, PlaneHk Set.univ (m + d) (h x))
    (hreg : LetterTermRegular (letters j) (if (letters j).positive then 1 else 0) X₀ δ r m d Ψ) :
    ∑ x, (π x)⁻¹ * ∫ z, ∑ k : Fin 2, inner ℝ
        (wordChainPreviousFlux letters X₀ δ κ Uwr (j.succ, x) r z k)
        ((Ψ x).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) =
      ∑ u, (π u)⁻¹ * ∫ z,
        inner ℝ ((Uj u).toFunction.jet (valueIndex2 (κ j.castSucc u)) z)
          (letterTransposeJet π (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
            (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
            (if (letters j).positive then 1 else 0) X₀ δ r m d
            (fun x => (Ψ x).toFunction.jet) u (valueIndex2 m) z) := by
  calc ∑ x, (π x)⁻¹ * ∫ z, ∑ k : Fin 2, inner ℝ
          (wordChainPreviousFlux letters X₀ δ κ Uwr (j.succ, x) r z k)
          ((Ψ x).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z)
      = ∑ x, (π x)⁻¹ * ∫ z, ∑ k : Fin 2,
          inner ℝ ((letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
            (j.succ, x) (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0)
            X₀ δ (fun u => Uwj u) r z) k)
          ((Ψ x).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
        simp only [wordChainPreviousFlux_succ, hUwr]
    _ = ∑ u, (π u)⁻¹ * ∫ z,
          inner ℝ ((Uwj u).toFunction.jet (valueIndex2 (κ j.castSucc u + 1)) z)
            (letterTransposeJet π (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
              (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
              (if (letters j).positive then 1 else 0) X₀ δ r m d
              (fun x => (Ψ x).toFunction.jet) u (valueIndex2 m) z) :=
        letterTranspose_duality π hπ (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
          (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
          (if (letters j).positive then 1 else 0) X₀ δ r m d hd hempty
          (fun u => Uwj u) Ψ hreg
    _ = _ := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← htr u]
        rfl

/-- The step of the adjoint word chain from the vector dualities of the components: the sum
over the components and the transposition of the letter. -/
theorem weakCont_step_of_components (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (j : Fin N) {n : ι → Type*} [∀ x, Fintype (n x)]
    (B : ∀ x, OrthonormalBasis (n x) ℝ (h x)) (m d : ℕ) (hd : 1 ≤ d)
    (hempty : ∀ x u (o : Finset.Icc 2 D), d < o.1 → (letters j).edge x u o = [])
    (Φ : ∀ x, PlaneHk Set.univ (m + d) (h x))
    (ψ : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + d) ℝ)
    (hreg : ∀ᵐ r ∂volume.restrict (Icc a b),
      LetterTermRegular (letters j) (if (letters j).positive then 1 else 0) X₀ δ r m d
        (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))))
    (hx : ∀ x, IntervalIntegrable (fun r => ∫ z, ∑ k : Fin 2, inner ℝ
        (wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z k)
        ((planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet
          ⟨⟨1, by omega⟩, fun _ => k⟩ z)) volume a b ∧
      inner ℝ (planeHkValueOperator (κ j.succ x) (U (j.succ, x) b))
          (planeHkValueOperator (m + d) (Φ x)) =
        inner ℝ (planeHkValueOperator (κ j.succ x) (f (j.succ, x)))
            (planeHkValueOperator (m + d) (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) -
          ∫ r in a..b, ∫ z, ∑ k : Fin 2, inner ℝ
            (wordChainPreviousFlux letters X₀ δ κ (fun p => Uw p r) (j.succ, x) r z k)
            ((planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet
              ⟨⟨1, by omega⟩, fun _ => k⟩ z)) :
    ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ j.succ x) (U (j.succ, x) b))
        (planeHkValueOperator (m + d) (Φ x)) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ j.succ x) (f (j.succ, x)))
          (planeHkValueOperator (m + d) (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) -
        ∫ r in a..b, ∑ u, (π u)⁻¹ * ∫ z,
          inner ℝ ((U (j.castSucc, u) r).toFunction.jet (valueIndex2 (κ j.castSucc u)) z)
            (letterTransposeJet π (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
              (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
              (if (letters j).positive then 1 else 0) X₀ δ r m d
              (fun x => (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet) u
              (valueIndex2 m) z) := by
  refine (weakCont_sum_components π _ _ _ (fun x => (hx x).1) (fun x => (hx x).2)).trans ?_
  congr 1
  apply intervalIntegral.integral_congr_ae
  have htr : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ u,
      truncatePlaneHk (Nat.le_succ _) (Uw (j.castSucc, u) r) = U (j.castSucc, u) r :=
    ae_all_iff.mpr fun u => hsol.2.2.1 (j.castSucc, u)
  have hall := (ae_restrict_iff' measurableSet_Icc).mp (htr.and hreg)
  filter_upwards [hall] with r hr hmem
  rw [Set.uIoc_of_le hab] at hmem
  have hrr := hr ⟨hmem.1.le, hmem.2⟩
  have htr_r := hrr.1
  have hreg_r := hrr.2
  exact weakCont_transpose_at_time π hπ letters X₀ δ κ j m d hd hempty r
    (fun u => U (j.castSucc, u) r) (fun u => Uw (j.castSucc, u) r) htr_r (fun p => Uw p r)
    (fun _ => rfl) (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) hreg_r

/-- **(17b)**: the step of the adjoint word chain for every chain, with the flux hypothesis
replaced by the split-weight pair. -/
theorem weakContStepDuality : WeakContStepDualityStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D N hD π hπ letters a b hab G hG v hv M hb ϖ ζ X₀ κ f U Uw hsol j hcut
    hwt B m d hd hempty Φ ψ ψw hψ hreg hrap
  refine hrap.elim fun Bd hB => ?_
  have hBd := hB.1
  have hrapB := hB.2
  have hUwm : ∀ u, MemLp (Uw (j.castSucc, u)) 2 (volume.restrict (Icc a b)) :=
    fun u => hsol.2.1 (j.castSucc, u)
  refine weakCont_step_of_components π hπ G letters X₀ (ζ * ϖ) κ a b hab v f U Uw hsol j B m d hd
    hempty Φ ψ hreg fun x => ?_
  refine (hwt x).elim fun Cx hC => ?_
  have hCx := hC.1
  have hwtx := hC.2
  exact weakCont_component_vector_duality hD G hG letters X₀ (ζ * ϖ) κ a b hab v hv M hb f U Uw
    hsol j x (hcut x) (fun z => polynomialMomentRoot ϖ z ^ (letters j).slow)
    ((polynomialMomentRoot_continuous ϖ).pow _)
    (fun z => pow_pos (lt_of_lt_of_le one_pos (polynomialMomentRoot_one_le ϖ z)) _)
    (fun r => Cx * ∑ u, ‖Uw (j.castSucc, u) r‖)
    (fun r => mul_nonneg hCx (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    ((integrable_finsetSum _ fun u _ => ((hUwm u).integrable one_le_two).norm).const_mul Cx)
    hwtx (B x) (m + d) (le_trans hd (Nat.le_add_left d m)) (Φ x) (ψ x) (ψw x) (hψ x) Bd hBd
    (fun r hr e => (hrapB r hr x e).1) (fun r hr e => (hrapB r hr x e).2)

end AVRegularity.CycleWords.Discard
end
