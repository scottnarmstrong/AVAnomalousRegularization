-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Interior.NegativeAdjoint
import AVRegularity.CycleJoint.ScalarPlaneUniformMassSquaredEnergy
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
public import AVRegularity.CycleWords.Seam.TransCalc
public import AVRegularity.CycleWords.MixedWords.Discard.CellMean
import AVRegularity.CycleWords.MixedWords.Discard.BandCoeff

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.Weighted
namespace AVRegularity.CycleWords.Seam

/-! The reversed scalar adjoint chain of an old block exists for every datum in `PlaneHk m`, when the
frozen metric is within `1/32` of the identity: `exists_frozenMetricScalarChain` on the reversed
coefficients `(G(-τ), -v(-τ))`, with the drift-jet bookkeeping (jets of the
reversed drift at most `A_m/√η · l!`). -/

/-- The derivatives of the reversed drift. -/
theorem reversedDrift_iteratedFDeriv_le {η : ℝ} (hη : 0 < η) (v : ℝ → Vec 2 → Vec 2)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (l : ℕ) (τ : ℝ) (x : Vec 2) :
    Real.sqrt η * ‖iteratedFDeriv ℝ l (fun z => -(v (-τ) z)) x‖ ≤ Cvj l := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have h := hvj l (-τ) x
  change ‖iteratedFDeriv ℝ l (Real.sqrt η • v (-τ)) x‖ ≤ _ at h
  have hs : iteratedFDeriv ℝ l (Real.sqrt η • v (-τ)) x =
      Real.sqrt η • iteratedFDeriv ℝ l (v (-τ)) x :=
    iteratedFDeriv_const_smul_apply ((hvs (-τ)).contDiffAt.of_le (by exact_mod_cast le_top))
  have hn : iteratedFDeriv ℝ l (fun z => -(v (-τ) z)) x = -iteratedFDeriv ℝ l (v (-τ)) x :=
    iteratedFDeriv_neg_apply
  rw [hs, norm_smul, Real.norm_of_nonneg hsη.le] at h
  rw [hn, norm_neg]
  exact h

/-- The jets of the reversed drift through order `k`. -/
theorem reversedDrift_jets {η : ℝ} (hη : 0 < η) (v : ℝ → Vec 2 → Vec 2)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (k : ℕ) (τ : ℝ) (l : ℕ) (hlk : l ≤ k) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient (fun z => -(v (-τ) z))) l x‖ ≤
      Interior.negAdjointJetConstant Cvj k / Real.sqrt η * (l.factorial : ℝ) := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have h1 := driftCoefficient_array_norm_le_iterated (fun z => -(v (-τ) z)) l
    (((hvs (-τ)).neg).of_le (by simp)) x
  have h2 := reversedDrift_iteratedFDeriv_le hη v hvs Cvj hvj l τ x
  have h3 := Interior.negAdjointJetConstant_term Cvj hlk
  have hc : 0 ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ := by
    positivity
  have hit : ‖iteratedFDeriv ℝ l (fun z => -(v (-τ) z)) x‖ ≤ |Cvj l| / Real.sqrt η := by
    rw [le_div_iff₀ hsη, mul_comm]
    exact h2.trans (le_abs_self _)
  have hfac : (1 : ℝ) ≤ l.factorial := by exact_mod_cast Nat.factorial_pos l
  have hA : 0 ≤ Interior.negAdjointJetConstant Cvj k / Real.sqrt η :=
    div_nonneg (zero_le_one.trans (Interior.one_le_negAdjointJetConstant Cvj k)) hsη.le
  calc ‖coefficientDerivativeArray (driftCoefficient (fun z => -(v (-τ) z))) l x‖
      ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ *
          (|Cvj l| / Real.sqrt η) := h1.trans (mul_le_mul_of_nonneg_left hit hc)
    _ = (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l| /
          Real.sqrt η := by ring
    _ ≤ Interior.negAdjointJetConstant Cvj k / Real.sqrt η :=
        div_le_div_of_nonneg_right h3 hsη.le
    _ ≤ Interior.negAdjointJetConstant Cvj k / Real.sqrt η * l.factorial :=
        le_mul_of_one_le_right hA hfac

/-- **Existence of the reversed adjoint chain.** -/
theorem exists_reversedAdjoint (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (g : ℝ) (hg0 : 0 ≤ g) (hg : g ≤ 1 / 32)
    (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (m : ℕ) {a t : ℝ} (hat : a ≤ t) (φ : PlaneHk Set.univ m ℝ) :
    ∃ (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
      (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ),
      IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a)
        (fun τ z => -(v (-τ) z)) (fun _ => φ) (fun _ _ _ => 0) ψ ψw := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  set A := Interior.negAdjointJetConstant Cvj m with hAdef
  have hA : 1 ≤ A := Interior.one_le_negAdjointJetConstant Cvj m
  set strain := A / Real.sqrt η with hstraindef
  have hstrain0 : 0 ≤ strain := by positivity
  set ρ := 1 / (3 * A * (1 + (Real.sqrt η)⁻¹)) with hρdef
  have hP : 1 ≤ 1 + (Real.sqrt η)⁻¹ := by
    have := inv_pos.mpr hsη
    linarith
  have hρ : 0 < ρ := by positivity
  have hρ3 : ρ ≤ 1 / 3 := by
    rw [hρdef]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hsmall : 1 * ρ / 1 ≤ 1 / 2 := by
    rw [one_mul, div_one]
    linarith
  have hstrain : strain * 1 * ρ ^ 2 ≤ 1 / 8 := by
    have hsP : Real.sqrt η * (1 + (Real.sqrt η)⁻¹) = Real.sqrt η + 1 := by
      field_simp
    have hX : 1 ≤ A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹) := by
      rw [hsP]
      have h1 : 1 ≤ Real.sqrt η + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ A * (Real.sqrt η + 1) * (1 + (Real.sqrt η)⁻¹) := by gcongr
    have he : strain * 1 * ρ ^ 2 =
        1 / (9 * (A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹))) := by
      rw [hstraindef, hρdef]
      field_simp
      ring
    rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set vr : ℝ → Vec 2 → Vec 2 := fun τ z => -(v (-τ) z) with hvrdef
  have hvrD : IsCellDrift vr := cellDrift_timeReverse hv
  have hvrs : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (vr τ) := fun τ => (hvs (-τ)).neg
  set V := |Cvj 0| / Real.sqrt η with hVdef
  have hV : 0 ≤ V := by positivity
  have hbv : ∀ τ ∈ Icc (-t) (-a), ∀ x, ‖vr τ x‖ ≤ V := fun τ _ x => by
    have h := reversedDrift_iteratedFDeriv_le hη v hvs Cvj hvj 0 τ x
    rw [norm_iteratedFDeriv_zero] at h
    rw [hVdef, le_div_iff₀ hsη, mul_comm]
    exact h.trans (le_abs_self _)
  have hjets : ∀ τ ∈ Icc (-t) (-a), ∀ l, 1 ≤ l → l ≤ m → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (vr τ)) l x‖ ≤
        strain * (1 : ℝ) ^ l * (l.factorial : ℝ) * (1 : ℝ) ^ ((1 : ℤ) - l) := by
    intro τ _ l _ hlk x
    rw [one_pow, one_zpow, mul_one, mul_one]
    exact reversedDrift_jets hη v hvs Cvj hvj m τ l hlk x
  have hdiv : ∀ τ ∈ Icc (-t) (-a), ∀ x, ∑ k : Fin 2, fderiv ℝ (vr τ) x (basisVec k) k = 0 :=
    fun τ _ x => cellDrift_classical_divergence_zero hvrD hvrs τ x
  have hvm : Measurable (fun q : Icc (-t) (-a) × Vec 2 => vr q.1 q.2) :=
    hvrD.1.comp (measurable_subtype_coe.prodMap measurable_id)
  have hM : Measurable (fun τ : ℝ => G (-τ)) :=
    hG.1.comp ((measurable_neg).prodMk (measurable_const (a := (0 : Vec 2))))
  obtain ⟨u, w, hsol⟩ := CycleJointProofs.exists_frozenMetricScalarChain (ι := Unit)
    (h := fun _ => ℝ) (fun _ => m) m (fun _ => le_rfl) ρ strain 1 1 hρ hstrain0 le_rfl one_pos
    hsmall hstrain (-t) (-a) (by linarith) vr (fun τ _ => hvrs τ) V hV hbv hdiv hjets
    (fun τ => G (-τ)) hM g hg0 (by linarith) (fun τ _ => hG.2.2.1 (-τ) 0)
    (fun τ _ ξ => hGn (-τ) 0 ξ) (fun _ _ => 0) (fun _ => planeHk_zero_time_memLp _ _)
    (fun _ => φ) hvm
  refine ⟨fun _ i => u i, fun _ i => w i, ?_⟩
  unfold IsPlaneChain
  unfold IsPlaneChainFrom at hsol
  convert hsol using 2
  all_goals first
    | rfl
    | (rename_i q
       obtain ⟨j, x⟩ := q
       obtain rfl : j = 0 := Fin.fin_one_eq_zero j
       rfl)

/-- The reversed adjoint chain on `[-t, -a]` is one on `[-t, -s]` for `a ≤ s ≤ t`, with the same
datum. -/
theorem reversedAdjoint_restrict (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (vr : ℝ → Vec 2 → Vec 2) (m : ℕ) {a s t : ℝ} (has : a ≤ s) (hst : s ≤ t)
    (φ : PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a)
      vr (fun _ => φ) (fun _ _ _ => 0) ψ ψw) :
    IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-s)
      vr (fun _ => φ) (fun _ _ _ => 0) ψ ψw := by
  have hfrom : IsPlaneChainFrom (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m)
      (-t) (-a) vr (fun j x => (fun _ : Unit => φ) x) (fun _ _ _ => 0) ψ ψw := by
    unfold IsPlaneChain at hψ
    unfold IsPlaneChainFrom
    convert hψ using 2
    rename_i q
    obtain ⟨j, x⟩ := q
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rfl
  have h0 : ψ 0 () (-t) = φ := hψ.2.2.2.1 ((0 : Fin 1), ())
  have hr := CycleJointProofs.planeChainFrom_restart_subwindow _ _ (-t) (-a) (-t) (-s) le_rfl
    (by linarith) (by linarith) vr _ _ ψ ψw hfrom
  unfold IsPlaneChain
  unfold IsPlaneChainFrom at hr
  convert hr using 2
  rename_i q
  obtain ⟨j, x⟩ := q
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  exact h0.symm

end AVRegularity.CycleWords.Seam
end
end

section
section
/-! # Quiet margin fibre bound, part II: the frame cut at an earlier end

`AmplitudeIdFrame.b1Cut F c`: the frame on `[a, c]`, `a ≤ c ≤ b`, with the same data, letters and
solution. Only the letter envelopes (`IsCycleLetter` on `[a, b] × ℝ²`, monotone in the domain:
`b1_isCycleLetter_mono`) and the plane chain (restricted to `[a, c]`) see the end. The stage values
and the regions are those of `F` (by definition). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

open AVRegularity.CycleWords.Discard

universe u v

/-- The jet suprema are monotone in the domain. -/
theorem b1_jetSupOn_mono {dom dom' : Set (ℝ × Vec 2)} (hsub : dom' ⊆ dom) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) : jetSupOn dom' r q f ≤ jetSupOn dom r q f := by
  unfold jetSupOn
  refine essSup_mono_ae (Filter.Eventually.of_forall fun t => ?_)
  exact biSup_mono fun Y hY => hsub hY

/-- Analytic envelopes on a domain are envelopes on every smaller domain. -/
theorem b1_isAnalyticEnvelope_mono {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {dom dom' : F.Domain} {E C : ℝ} {Ks Ls : ℕ}
    {b : ι → ι → ℝ} (hsub : ∀ p c, dom' p c ⊆ dom p c)
    (hA : IsAnalyticEnvelope F π dom E C Ks Ls b) : IsAnalyticEnvelope F π dom' E C Ks Ls b := by
  unfold IsAnalyticEnvelope at hA ⊢
  obtain ⟨h1, h2⟩ := hA
  refine ⟨fun p c v u γ d I tY htY z => h1 p c v u γ d I tY (hsub p c htY) z, fun v u => ?_⟩
  refine le_trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun γ _ => mul_le_mul' le_rfl
    (Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun r _ =>
      Finset.sum_le_sum fun q _ => mul_le_mul' le_rfl ?_))) (h2 v u)
  exact iSup_mono fun x : F.Index => b1_jetSupOn_mono (hsub x.1 x.2) r q _

/-- Cycle letters on a domain are cycle letters on every smaller domain. -/
theorem b1_isCycleLetter_mono {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {π : ι → ℝ}
    {L : CycleLetter ι h D} {dom dom' : Set (ℝ × Vec 2)} {Jstar H : ℕ} (hsub : dom' ⊆ dom)
    (hL : IsCycleLetter π L dom Jstar H) : IsCycleLetter π L dom' Jstar H :=
  { hL with analytic := b1_isAnalyticEnvelope_mono (fun _ _ => hsub) hL.analytic }

/-- A word piece on `[a, b]` is a word piece on `[a, c]`, `c ≤ b`. -/
theorem b1_isWordPiece_cut {K : ScalarConstants} {g₁ : ℝ} {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw H J : ℕ}
    {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D} {η S ηg ϖ : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ} {reg : BlockRegions}
    {a b c : ℝ} (hP : IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b) (hcb : c ≤ b) :
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a c :=
  { hP with
    hlet := fun i => b1_isCycleLetter_mono
      (Set.prod_mono (Set.Icc_subset_Icc le_rfl hcb) subset_rfl) (hP.hlet i) }

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- **The frame cut at `c ∈ [a, b]`.** -/
def AmplitudeIdFrame.b1Cut {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (c : ℝ) (hac : F.a ≤ c)
    (hcb : c ≤ F.b) : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁ :=
  { F with
    b := c
    piece := b1_isWordPiece_cut F.piece hcb
    ordered := hac
    right := hcb.trans F.right
    solution := by
      have hs := F.solution
      have hsub : Set.Icc F.a c ⊆ Set.Icc F.a F.b := Set.Icc_subset_Icc le_rfl hcb
      unfold IsPlaneChain at hs ⊢
      exact ⟨fun i => (hs.1 i).mono hsub,
        fun i => (hs.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
        fun i => ae_restrict_of_ae_restrict_of_subset hsub (hs.2.2.1 i), hs.2.2.2.1,
        fun i t ht φ => hs.2.2.2.2 i t (hsub ht) φ⟩ }

end Frame

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the fast remainder of the seam's future kernel (statements)

Clause (3) of `SeamFutureKernelStatement` for `seamFutureKernel`:
`‖Z₊f − K₊f‖_{(ρ_*,K_out;p_out)} ≤ CΘ₊P_e^Q(1+S)^Q[e^{-cS} + (1+B_p)e^{-cD_q} + e^{-ca}]
‖f‖_{(e,-k;p_in)}`, the entrance quietMargin `[t_F, t_F + a]` quiet.

Route. The kernel is `R ∘ μ(D)` with the cell low pass `μ` (`IsSeamLowPass`), so the split of the
input with `μ(D)` is exact: `E₊f = [Z₊(μf) − R(μf)] + Z₊((1 − μ)f)`. The low part is the chain
discard of `cycle_mixed_words` (`ChainDiscardStatement`). The high part `|ξ| ≥ 3π/8` is damped and
smoothed by the quiet margin (`QuietMarginFibreStatement`). Chains exist only from compact data, so
the split runs on compact approximants (`compactDensity`, `chainCombination`), the quiet margin
statement pays the leftover low band
`μ₂(D)f'` (`μ₂ = 1` on `|ξ| ≤ π/4`, supported in `|ξ| < 3π/8`, `μ₂(1 − μ) = 0`) at full price,
and weak continuity passes to the seam datum.

* `QuietMarginFibreStatement`: the quiet margin at the fibre level.
* `QuietMarginDatumStatement`: the negative and low-band norms of the stage data.
* `CellLowPassMomentStatement`: the cell-scale low pass is lossless.
* `SeamFutureFastStatement`: clause (3) for `seamFutureKernel`; `SeamFutureFastAssembly`.
* `seamFutureKernel_of_parts`: the seam future kernel from its two parts and the cutoffs. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- The squared `H^{-k}` norm of a Bloch fibre at `θ`: `∑_n (1 + |2πn + θ|²)^{-k} |f̂(n)|²`. -/
def cellNegSq (k : ℕ) (θ : Vec 2) (f : Vec 2 → ℂ) : ℝ≥0∞ :=
  ∑' n : Fin 2 → ℤ, ENNReal.ofReal
    (((1 + vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n)) ^ k)⁻¹ *
      ‖cellFourierCoeff f n‖ ^ 2)

/-- The squared `L²` norm of the modes `|2πn + θ| < ρ` of a Bloch fibre. -/
def cellLowSq (ρ : ℝ) (θ : Vec 2) (f : Vec 2 → ℂ) : ℝ≥0∞ :=
  ∑' n : Fin 2 → ℤ,
    if vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) < ρ ^ 2 then
      ENNReal.ofReal (‖cellFourierCoeff f n‖ ^ 2) else 0

section FrameSums

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- The `H^{-k}` norms of the scaled stage values at the start of the frame. -/
def stageDatumNegSq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ) (Ks : Fin Nw → ℕ)
    (k : ℕ) (θ : Vec 2) : ℝ≥0∞ :=
  ∑ i : B1WIndex ι h Nw m Ks, cellNegSq k θ (stageScaled F θ i F.a)

/-- The low-band norms (`|2πn + θ| < ρ`) of the scaled stage values at the start of the frame. -/
def stageDatumLowSq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ) (Ks : Fin Nw → ℕ)
    (ρ : ℝ) (θ : Vec 2) : ℝ≥0∞ :=
  ∑ i : B1WIndex ι h Nw m Ks, cellLowSq ρ θ (stageScaled F θ i F.a)

end FrameSums

/-- **The quiet entrance quiet margin at the fibre level.** On a frame of duration at least one
whose first stretch `[a, a + a']` is quiet with zero drift, at every frequency of the zone, the
terminal stages are in `H^{K_f}` at the end, with norm at most `C P_e^Q (1 + (b - a))^Q` times
`e^{-c a'}` times the `H^{-k}` norms of the stage values at the start, plus the full price of their
low band `|2πn + θ| < π/8`.

Route. The plain pass with negative input (adjoint curves in `H^{s_k + k}`, `CellAdjointKernelHsStatement`); on the
quiet margin the adjoint curves are mode preserving (quiet: zero drift, letters fast independent) and
every mode `|2πn + θ| ≥ π/16` is damped by `e^{-c a'}` and smoothed; the positive terminal window
of `fullFieldFibre_of_families` for the output order.

For `N_w = 0`, moment `0`, `v = 0` throughout and `G = I`, each mode is multiplied by
`e^{-|y|²(b - a)}`, `y = 2πn + θ`, and `(1+|y|²)^{K_f + k} e^{-2|y|²(b-a)} ≤ C e^{-c a'}` for
`|y| ≥ π/8`, `b - a ≥ max(1, a')`; the modes `|y| < π/8` are the second term. For `a' = 0` this is
the negative-input full field (smoothing on the last unit of time), since `(1+|y|²)^{-k} ≥ c` on the
low band. For zero datum the bound reads `0 ≤ 0`. Quantifier order: `C, c, Q` after the shape,
`K_f` and `k`; before the frame, the frequency and `a'`. -/
def QuietMarginFibreStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf k : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d ≤ F.J →
    F.a + 1 ≤ F.b → θ ∈ freqCube →
  ∀ a' : ℝ, 0 ≤ a' → F.a + a' ≤ F.b → Icc F.a (F.a + a') ⊆ F.reg.quiet →
    (∀ t ∈ Icc F.a (F.a + a'), ∀ z, F.v t z = 0) →
    stageTerminalBandSq F m Ks Kf 0 θ ≤
      ENNReal.ofReal ((C * peFactor F.η ^ Q * (1 + (F.b - F.a)) ^ Q) ^ 2) *
        (ENNReal.ofReal (Real.exp (-2 * c * a')) * stageDatumNegSq F m Ks k θ +
          stageDatumLowSq F m Ks (Real.pi / 8) θ)

/-- **The stage data in negative order and in the low band**, integrated over the zone, for
the compactly supported datum of a frame: at most the cell-scale negative norm of the datum
(weight `n = m + ∑K_i`, the moments of the level-`0` stages), and the moment norm of `μ₂(D)φ` for a
multiplier `μ₂` equal to one on `|ξ| ≤ π/4` (a neighbourhood of the band `|ξ| < π/8`, so the
derivatives of `μ₂` vanish there). Stated for the combination `A N_k + L_2` with an arbitrary
weight `A`: the integrand is a sum, and the lower integral of a sum splits only for measurable
summands, which the proof (measurable majorants, as `StageDatumStatement`) provides.

For `m = 0`, `N_w = 0`, `k = 0` this is Parseval of the Bloch sums, as in `StageDatumStatement`.
For zero datum the bound reads `0 ≤ 0`. Since `μ₂ = 1` near the band, `∂^β(μ₂φ̂) = ∂^βφ̂` on
`|ξ| < π/4`; for `A = 0` only the low band remains. Quantifier order: `C` after the orders and
`μ₂`; before the frame and `A`. -/
def QuietMarginDatumStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m k : ℕ) (Ks : Fin Nw → ℕ) (μ₂ : Vec 2 → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) μ₂ → HasCompactSupport μ₂ → (∀ ξ, μ₂ (-ξ) = μ₂ ξ) →
    (∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ Real.pi / 4 → μ₂ ξ = 1) →
  ∃ C : ℝ, 0 < C ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁),
    (∀ l, (F.letters l).slow = Ks l) → ∀ A : ℝ≥0∞,
    ∫⁻ θ in freqCube, (A * stageDatumNegSq F m Ks k θ +
        stageDatumLowSq F m Ks (Real.pi / 8) θ) ≤
      ENNReal.ofReal C *
        (A * negJetNorm F.π ((wordReserveN m Ks : ℕ) : ℝ) k F.ϖ 1 F.φ ^ 2 +
          momentNorm F.π (wordReserveN m Ks) F.ϖ (fun x => fourierCutoff μ₂ (F.φ x)) ^ 2)

/-- **The cell-scale low pass is lossless**: for a multiplier supported in `|ξ| < π/2`, the
moment norm of `μ(D)G` is at most the negative norm of `G` at the cell scale (derivative scale
`1`), with the same weight, for every order `k`.

For `n = k = 0`, `‖μ(D)G‖ ≤ sup|μ| ‖G‖` and `negJetNorm π 0 0 ϖ 1 G` is the weighted
`L²` norm. On the band `|ξ| < π/2` at scale `1`, `(1 + |ξ|²)^k ≤ (1 + π²/4)^k` on the support. With
weight `n`, the kernel of `μ(D)` has every moment at scale `1 ≤ ϖ⁻¹`. Quantifier order: `C` after
`n, k, μ`; before `ϖ` and the field. -/
def CellLowPassMomentStatement : Prop :=
  ∀ (n k : ℕ) (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ ξ, μ (-ξ) = μ ξ) →
    (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) →
  ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ 1 → ∀ G : ∀ x, Vec 2 → h x, (∀ x, MemLp (G x) 2 volume) →
    momentNorm π n ϖ (fun x => fourierCutoff μ (G x)) ≤
      ENNReal.ofReal C * negJetNorm π (n : ℝ) k ϖ 1 G

/-- **Clause (3) of `SeamFutureKernelStatement` for `seamFutureKernel`**, for every regime
`(c₁, Q₁)` at least as strict as `(c₀, Q₀)`. -/
def SeamFutureFastStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ μ : Vec 2 → ℝ, ∀ hμ : IsSeamLowPass μ, ∀ σ : SeamShape, σ.K = K →
  ∃ (c₀ : ℝ) (Q₀ : ℕ), 0 < c₀ ∧ ∀ (c₁ : ℝ) (Q₁ : ℕ), 0 < c₁ → c₁ ≤ c₀ → Q₀ ≤ Q₁ →
  ∃ Q : ℕ, ∀ Cout : ℝ, 0 < Cout →
  ∃ (C c : ℝ), 0 ≤ C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ lettersF : Fin σ.Np → CycleLetter ι h σ.D,
    (∀ i, (lettersF i).order = σ.dF i ∧ (lettersF i).slow = σ.KsF i ∧
      (lettersF i).positive = σ.posF i) →
  ∀ η S ηg rstar ϖ δ : ℝ, 0 < η → η ≤ 1 → 1 ≤ S → 0 < ηg → ηg ≤ 1 → 0 < rstar →
    rstar ≤ Cout → ϖ = Real.sqrt (η / S) → δ = ϖ * ηg →
  ∀ (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ),
    IsCellMetric (fun t _ => GF t) → IsCellDrift vF →
    (∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0) →
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t)) →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ σ.K.Cw) →
    (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ σ.K.Cvj j) →
    0 ≤ gF → gF ≤ σ.K.g0 → gF ≤ g₁ → IsMetricNearIdentity (fun t _ => GF t) gF →
  ∀ (regF : BlockRegions), ScalarPackage σ.K η GF vF tF S ϖ regF →
    (∀ i, IsCycleLetter π (lettersF i) (Set.Icc tF (tF + S) ×ˢ Set.univ) σ.Jstar σ.H) →
    (∀ i, IsTransverseOnPulses (lettersF i).edge
      (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p)) regF.orient) →
    (∀ i, IsQuietOn (lettersF i).edge vF (regF.quiet ∩ Set.Icc tF (tF + S))) →
    (∀ i x y o, ∀ γ ∈ (lettersF i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) →
  ∀ a : ℝ, 0 ≤ a → a ≤ S → Set.Icc tF (tF + a) ⊆ regF.quiet →
  ∀ X₀F : Vec 2,
  ∀ (κF : Fin (σ.Np + 1) → ι → ℕ) (Kout : ι → ℕ), (∀ x, Kout x ≤ σ.Kmax) →
  (∀ x, Kout x ≤ κF (Fin.last σ.Np) x) →
  (∀ (j : Fin σ.Np) x y (o : Finset.Icc 2 σ.D), (lettersF j).edge x y o ≠ [] →
    κF j.succ x + o.1 ≤ κF j.castSucc y + 2) →
  (∀ (fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x))
    (uF : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x))
    (wF : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x)),
    momentNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ)) ϖ (fun x => planeValue (fF x)) < ⊤ →
    seamChain GF lettersF X₀F δ κF tF (tF + S) vF fF uF wF →
    weightedJetNorm π (σ.pout : ℝ) σ.Kmax ϖ rstar
        (fun x a wd z => if a ≤ Kout x then planeJetOrder (uF (Fin.last σ.Np) x (tF + S)) a wd z -
          orderedDerivative wd (seamFutureKernel K χlo (σ.pout + ∑ i, σ.KsF i) hμ π lettersF η S
            ηg tF ϖ GF vF X₀F c₁ Q₁ regF (fun x' => planeValue (fF x')) x) z else 0) ≤
      ENNReal.ofReal (C * wordTheta ηg lettersF * peFactor η ^ Q * (1 + S) ^ Q *
          (Real.exp (-c * S) + (1 + regF.joins) * Real.exp (-c * regF.buffer) +
            Real.exp (-c * a))) *
        negJetNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ) : ℝ) σ.k ϖ 1
          (fun x => planeValue (fF x)))

/-- **Assembly of the fast remainder** (its proof also uses `retainedMapExists`, `compactDensity`,
`chainCombination`, `exists_compactChain_capped`, the lower semicontinuity of the output norm, the
window regions, and a smooth cutoff `μ₂` with `μ₂(1 − μ) = 0` (`radialCutoff_exists`)). -/
def SeamFutureFastAssembly : Prop :=
  ChainDiscardStatement.{u, v} → ChainWeakContinuityStatement.{u, v} →
    BlochOutputStatement.{u, v} → QuietMarginFibreStatement.{u, v} → QuietMarginDatumStatement.{u, v} →
    CellLowPassMomentStatement.{u, v} → SeamFutureFastStatement.{u, v}

end AVRegularity.CycleWords.Seam
end
end

section
/-! # The seam future kernel from its parts

`seamFutureKernel_of_parts`: `SeamFutureKernelStatement` from the kernel clauses and the
fast remainder, with the cutoffs of `radialCutoff_exists` (the low cutoff `ξ_lo, 2ξ_lo` and
the cell low pass `3π/8, π/2`). The kernel is `seamFutureKernel` at the regime
`c₁ = min c₀ᵃ c₀ᵇ`, `Q₁ = max Q₀ᵃ Q₀ᵇ`; `p_in = p_out + ∑K_s^F + 2`; `g₁` is the minimum of the two
thresholds. When `ξ_lo ≤ 0` there is no scalar package and the statement is vacuous. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleWords.Seam

open AVRegularity.CycleWords.Assembly

universe u v

/-- The cell low pass of the seam exists. -/
theorem seamLowPass_exists : ∃ μ : Vec 2 → ℝ, IsSeamLowPass μ := by
  obtain ⟨μ, hs, hc, he, h1, h0⟩ := radialCutoff_exists (by positivity : 0 < 3 * Real.pi / 8)
    (by linarith [Real.pi_pos] : 3 * Real.pi / 8 < Real.pi / 2)
  exact ⟨μ, ⟨hs, hc, he, h1, h0⟩⟩

/-- **The seam future kernel from its two parts.** -/
theorem seamFutureKernel_of_parts (hA : SeamFutureKernelClausesStatement.{u, v})
    (hB : SeamFutureFastStatement.{u, v}) : SeamFutureKernelStatement.{u, v} := by
  intro K
  obtain ⟨μ, hμ⟩ := seamLowPass_exists
  by_cases hξ : 0 < K.ξlo
  · obtain ⟨χlo, hχ⟩ := lowCutoffExists K hξ
    obtain ⟨gA, hgA, hA'⟩ := hA K
    obtain ⟨gB, hgB, hB'⟩ := hB K
    refine ⟨min gA gB, lt_min hgA hgB, fun σ hσ => ?_⟩
    obtain ⟨cA, QA, hcA, hA''⟩ := hA' χlo hχ μ hμ σ hσ
    obtain ⟨cB, QB, hcB, hB''⟩ := hB' χlo hχ μ hμ σ hσ
    obtain ⟨Q, hBQ⟩ := hB'' (min cA cB) (max QA QB) (lt_min hcA hcB) (min_le_right _ _)
      (le_max_right _ _)
    have hAc := hA'' (min cA cB) (max QA QB) (lt_min hcA hcB) (min_le_left _ _)
      (le_max_left _ _)
    refine ⟨σ.pout + ∑ i, σ.KsF i + 2, Q, le_rfl, fun Cout hCout => ?_⟩
    obtain ⟨CK, hCK0, hAK⟩ := hAc Cout hCout
    obtain ⟨C, c, hC0, hc0, hBK⟩ := hBQ Cout hCout
    refine ⟨C, c, CK, hC0, hc0, hCK0, ?_⟩
    intro ι _ h _ _ _ _ _ _ π hπ lettersF hlet η S ηg rstar ϖ δ hη hη1 hS hηg hηg1 hr0 hrC hϖ hδ
      tF GF vF gF hGm hv hv0 hvs hvw hvj hg0 hg hg1 hGn regF hpkg hLt hT hQ hM a ha0 haS haq X₀F
    obtain ⟨h1, h2⟩ := hAK π hπ lettersF hlet η S ηg ϖ δ hη hη1 hS hηg hηg1 hϖ hδ tF GF vF gF hGm
      hv hv0 hvs hvw hvj hg0 hg (hg1.trans (min_le_left _ _)) hGn regF hpkg hLt hT hQ hM X₀F
    exact ⟨_, h1, h2, hBK π hπ lettersF hlet η S ηg rstar ϖ δ hη hη1 hS hηg hηg1 hr0 hrC hϖ hδ
      tF GF vF gF hGm hv hv0 hvs hvw hvj hg0 hg (hg1.trans (min_le_right _ _)) hGn regF hpkg hLt
      hT hQ hM a ha0 haS haq X₀F⟩
  · refine ⟨1, one_pos, fun σ hσ => ⟨σ.pout + ∑ i, σ.KsF i + 2, 0, le_rfl, fun Cout _ =>
      ⟨0, 1, fun _ _ => 0, le_rfl, one_pos, fun _ _ => le_rfl, ?_⟩⟩⟩
    intro ι _ h _ _ _ _ _ _ π hπ lettersF hlet η S ηg rstar ϖ δ hη hη1 hS hηg hηg1 hr0 hrC hϖ hδ
      tF GF vF gF hGm hv hv0 hvs hvw hvj hg0 hg hg1 hGn regF hpkg
    have hpos : 0 < σ.K.ξlo := hpkg.consts_pos.2.1
    rw [hσ] at hpos
    exact absurd hpos hξ

end AVRegularity.CycleWords.Seam
end
end

section
/-! # Quiet margin fibre bound: the cell pairing against the negative norm

`b1_pair_hasSum`: Parseval for the cell pairing, `⟨u, z⟩ = ∑_n conj ẑ(n) û(n)` (Mathlib's
`UnitAddTorus.hasSum_prod_mFourierCoeff` through the cell representative of the torus).
`b1_pair_le_neg`: with the shifted Fourier weights of the tests (the band bound with `ρ = 0`),
`|⟨u, φ⟩| ≤ C^{1/2} (∑_n (1 + |2πn + θ|²)^{-k} |û(n)|²)^{1/2} ‖φ‖_{H^N}`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.EntryWeakProofs
open AVRegularity.Analysis.Convolution
open scoped ENNReal ComplexConjugate

local instance b1NegPairMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance b1NegPairIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance b1NegPairIsProb :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.CycleWords.Seam

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

/-- The torus Fourier coefficient of the cell class is the cell Fourier coefficient. -/
theorem b1_mFourierCoeff_cell (w : ComplexCellL2) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (cellToTorus w) n = cellFourierCoeff (w : Vec 2 → ℂ) n := by
  rw [cellCoeff_eq_clm, cellFourierCoeffCLM_apply]

/-- The torus integral of the cell classes is the cell integral. -/
theorem b1_torus_integral_eq (u z : ComplexCellL2) :
    ∫ t, conj ((cellToTorus z : UnitAddTorus (Fin 2) → ℂ) t) *
        (cellToTorus u : UnitAddTorus (Fin 2) → ℂ) t ∂torusMeasure =
      cellComplexPair u z := by
  have hmp := measurePreserving_unitTorusRepresentative_cell
  calc ∫ t, conj ((cellToTorus z : UnitAddTorus (Fin 2) → ℂ) t) *
        (cellToTorus u : UnitAddTorus (Fin 2) → ℂ) t ∂torusMeasure
      = ∫ t, (fun x => conj (z x) * u x) (AVenhance.Infra.Torus.unitTorusRepresentative 2 t)
          ∂torusMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [cellToTorus_ae z, cellToTorus_ae u] with t h1 h2
        rw [h1, h2]
        rfl
    _ = ∫ x, conj (z x) * u x ∂(volume.restrict AVenhance.unitCube) := by
        have hG : AEStronglyMeasurable (fun x => conj (z x) * u x)
            (Measure.map (AVenhance.Infra.Torus.unitTorusRepresentative 2) torusMeasure) := by
          rw [hmp.map_eq]
          exact (Lp.aestronglyMeasurable z).star.mul (Lp.aestronglyMeasurable u)
        have h := integral_map hmp.measurable.aemeasurable hG
        rw [hmp.map_eq] at h
        exact h.symm
    _ = cellComplexPair u z := by
        unfold cellComplexPair
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact mul_comm _ _

/-- **Parseval for the cell pairing.** -/
theorem b1_pair_hasSum (u z : ComplexCellL2) :
    HasSum (fun n : Fin 2 → ℤ => conj (cellFourierCoeff (z : Vec 2 → ℂ) n) *
      cellFourierCoeff (u : Vec 2 → ℂ) n) (cellComplexPair u z) := by
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (cellToTorus z) (cellToTorus u)
  have e : (fun n : Fin 2 → ℤ => conj (cellFourierCoeff (z : Vec 2 → ℂ) n) *
      cellFourierCoeff (u : Vec 2 → ℂ) n) = fun n =>
      conj (UnitAddTorus.mFourierCoeff (cellToTorus z) n) *
        UnitAddTorus.mFourierCoeff (cellToTorus u) n :=
    funext fun n => by rw [b1_mFourierCoeff_cell, b1_mFourierCoeff_cell]
  rw [e, ← b1_torus_integral_eq]
  exact h

/-- The weights of the shifted frequencies are at least one. -/
theorem b1_one_le_weight (k : ℕ) (θ : Vec 2) (n : Fin 2 → ℤ) :
    1 ≤ (1 + vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n)) ^ k := by
  refine one_le_pow₀ ?_
  have : 0 ≤ vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) := by
    unfold vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

/-- **The cell pairing against the negative norm.** -/
theorem b1_pair_le_neg {k N : ℕ} {θ : Vec 2} {C : ℝ} (hC : 0 ≤ C)
    (hband : ∀ w : TorusHk N ℂ,
      cellBandSq k 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (C * ‖w‖ ^ 2))
    (u : ComplexCellL2) (hu : cellNegSq k θ (u : Vec 2 → ℂ) ≠ ⊤) (φ : TorusHk N ℂ) :
    ‖cellComplexPair u (torusHkValueCLM φ)‖ ≤
      Real.sqrt C * Real.sqrt (cellNegSq k θ (u : Vec 2 → ℂ)).toReal * ‖φ‖ := by
  classical
  set w : (Fin 2 → ℤ) → ℝ := fun n =>
    (1 + vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n)) ^ k with hw
  have hw1 : ∀ n, 1 ≤ w n := b1_one_le_weight k θ
  have hw0 : ∀ n, 0 < w n := fun n => lt_of_lt_of_le one_pos (hw1 n)
  set a : (Fin 2 → ℤ) → ℝ := fun n => ‖cellFourierCoeff (u : Vec 2 → ℂ) n‖ with ha
  set b : (Fin 2 → ℤ) → ℝ := fun n =>
    ‖cellFourierCoeff (torusHkValueCLM φ : Vec 2 → ℂ) n‖ with hb
  -- the two weighted sums on finite sets
  have hB : ∀ Λ : Finset (Fin 2 → ℤ), ∑ n ∈ Λ, w n * b n ^ 2 ≤ C * ‖φ‖ ^ 2 := by
    intro Λ
    have h1 : ENNReal.ofReal (∑ n ∈ Λ, w n * b n ^ 2) ≤ ENNReal.ofReal (C * ‖φ‖ ^ 2) := by
      refine le_trans ?_ (hband φ)
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hw0 n).le (sq_nonneg _))]
      refine le_trans ?_ (ENNReal.sum_le_tsum Λ)
      refine Finset.sum_le_sum fun n _ => ?_
      have hv : (0 : ℝ) ^ 2 ≤
          vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) := by
        have := hw1 n
        rw [zero_pow two_ne_zero]
        unfold vecDot
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      simp only [hv, ↓reduceIte]
      exact le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).1 h1
  have hA : ∀ Λ : Finset (Fin 2 → ℤ), ∑ n ∈ Λ, (w n)⁻¹ * a n ^ 2 ≤
      (cellNegSq k θ (u : Vec 2 → ℂ)).toReal := by
    intro Λ
    refine (ENNReal.ofReal_le_iff_le_toReal hu).1 ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (inv_nonneg.2 (hw0 n).le)
      (sq_nonneg _))]
    exact ENNReal.sum_le_tsum Λ
  -- Cauchy-Schwarz on finite sets, then the limit
  have hfin : ∀ Λ : Finset (Fin 2 → ℤ), ‖∑ n ∈ Λ, conj (cellFourierCoeff
      (torusHkValueCLM φ : Vec 2 → ℂ) n) * cellFourierCoeff (u : Vec 2 → ℂ) n‖ ≤
      Real.sqrt C * Real.sqrt (cellNegSq k θ (u : Vec 2 → ℂ)).toReal * ‖φ‖ := by
    intro Λ
    have hsq : ∀ n, Real.sqrt (w n) ^ 2 = w n := fun n => Real.sq_sqrt (hw0 n).le
    have hs0 : ∀ n, 0 < Real.sqrt (w n) := fun n => Real.sqrt_pos.2 (hw0 n)
    calc ‖∑ n ∈ Λ, conj (cellFourierCoeff (torusHkValueCLM φ : Vec 2 → ℂ) n) *
          cellFourierCoeff (u : Vec 2 → ℂ) n‖
        ≤ ∑ n ∈ Λ, (b n * Real.sqrt (w n)) * (a n / Real.sqrt (w n)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_mul, Complex.norm_conj]
          refine le_of_eq ?_
          change b n * a n = _
          have := (hs0 n).ne'
          field_simp
      _ ≤ Real.sqrt (∑ n ∈ Λ, (b n * Real.sqrt (w n)) ^ 2) *
          Real.sqrt (∑ n ∈ Λ, (a n / Real.sqrt (w n)) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (C * ‖φ‖ ^ 2) * Real.sqrt (cellNegSq k θ (u : Vec 2 → ℂ)).toReal := by
          refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
          · refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) (hB Λ)
            rw [mul_pow, hsq, mul_comm]
          · refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) (hA Λ)
            rw [div_pow, hsq, div_eq_inv_mul]
      _ = Real.sqrt C * Real.sqrt (cellNegSq k θ (u : Vec 2 → ℂ)).toReal * ‖φ‖ := by
          rw [Real.sqrt_mul hC, Real.sqrt_sq (norm_nonneg _)]
          ring
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp
    (b1_pair_hasSum u (torusHkValueCLM φ))) hfin

end AVRegularity.CycleWords.Seam
end
end
end
