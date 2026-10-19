-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncGDecomp
public import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Finite.TerminalLift.CovarianceIdentification

section
section
/-! **The polynomial in the covariance operator on torus trajectories**.

* `covTruncOp_meas`: `CovTruncOpStatement` with the window assumed measurable
  (`MeasurableSet I`): `G - 𝖯_p 𝖰_p G` has a realization of order `k` with mass
  `C_op ω^{p+1}` times that of `G`, `C_op = cqpBig ((k+4p)²) p`.
* `filterPOp_meas`: `FilterPOpStatement` with the window assumed measurable: `𝖯_p G` has a
  realization of order `k` with mass `covPolyConst ((k+2p)²) p` times that of `G`.

Route: `TorusAdj.qpRem`, `TorusAdj.covPolyP` for the matrices `H(t)`, their adjoint maps applied
to the given realization (`covOp_fluxBound_of_adj`); the adjoint maps are continuous in `H`
(`covOp_adjCont_qpRem`), which gives the measurability in time on a measurable window; the value
is identified by the duality `⟨g, φ - 𝖰_p𝖯_pφ⟩ = ⟨g - 𝖯_p𝖰_p g, φ⟩` (`covOp_truncation_duality`).

Special cases:
- `ω = 0`: the constant is `0` for `p ≥ 0` (`ω^{p+1} = 0`), the flux is `0`.
- `p = 0`: `cqpBig` is the empty-degree sum, `G - G = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.CovOp

/-! ### Commutation with a constant linear map -/

section Commute

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

theorem covOp_polynomial_clm (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (a : ℕ → ℝ)
    (L : V →L[ℝ] W) (u : Vec 2 → V) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) (x : Vec 2) :
    L (covariancePolynomial H p a u x) = covariancePolynomial H p a (fun y => L (u y)) x := by
  unfold covariancePolynomial
  rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [map_smul, AVRegularity.Finite.TerminalLift.terminal_covariance_iterate_clm H L l u
    (hu.of_le (by exact_mod_cast Nat.mul_le_mul_left 2 hlp))]

theorem covOp_P_clm (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (L : V →L[ℝ] W) (u : Vec 2 → V)
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) :
    (fun x => L (covPolyP H p u x)) = covPolyP H p (fun y => L (u y)) := by
  funext x
  rw [← covariancePolynomial_eq_P, ← covariancePolynomial_eq_P]
  exact covOp_polynomial_clm H p _ L u hu x

theorem covOp_Q_clm (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (L : V →L[ℝ] W) (u : Vec 2 → V)
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) :
    (fun x => L (covPolyQ H p u x)) = covPolyQ H p (fun y => L (u y)) := by
  funext x
  rw [← covariancePolynomial_eq_Q, ← covariancePolynomial_eq_Q]
  exact covOp_polynomial_clm H p _ L u hu x

theorem covOp_PQ_clm (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (L : V →L[ℝ] W) (u : Vec 2 → V)
    (hu : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) u) :
    (fun x => L (covPolyP H p (covPolyQ H p u) x)) =
      covPolyP H p (covPolyQ H p (fun y => L (u y))) := by
  have hQ : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (covPolyQ H p u) := by
    rw [← covariancePolynomial_eq_Q]
    exact covariancePolynomial_contDiff H p (2 * p) _ u (by
      rw [show 2 * p + 2 * p = 4 * p by omega]; exact hu)
  rw [covOp_P_clm H p L _ hQ, ← covOp_Q_clm H p L u
    (hu.of_le (by exact_mod_cast (by omega : 2 * p ≤ 4 * p)))]

end Commute

/-! ### The dual of the truncation and of `𝖯_p` for inner product space valued fields -/

section Dual

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem covOp_dual_trunc (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {g φ : Vec 2 → W}
    (hg : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) g) (hpg : AVenhance.IsZ2Periodic g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hpφ : AVenhance.IsZ2Periodic φ) :
    cellInner g (-qpRem H p φ) = cellInner (g - covPolyP H p (covPolyQ H p g)) φ := by
  rw [← sub_covPolyQ_covPolyP_eq H p hφ]
  exact covOp_truncation_duality H p hg hpg hφ hpφ

theorem covOp_continuous_trunc (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {g : Vec 2 → W}
    (hg : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) g) :
    Continuous (g - covPolyP H p (covPolyQ H p g)) := by
  have hQ : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (covPolyQ H p g) := by
    rw [← covariancePolynomial_eq_Q]
    exact covariancePolynomial_contDiff H p (2 * p) _ g (by
      rw [show 2 * p + 2 * p = 4 * p by omega]; exact hg)
  have hP : ContDiff ℝ (0 : ℕ∞) (covPolyP H p (covPolyQ H p g)) := by
    rw [← covariancePolynomial_eq_P]
    exact covariancePolynomial_contDiff H p 0 _ _ (by simpa using hQ)
  exact hg.continuous.sub hP.continuous

end Dual

/-! ### Weakening a factorial-norm bound -/

theorem covOp_FBound_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {T : (Vec 2 → E) → Vec 2 → E}
    {m R Kc : ℕ} {C : ℝ} (A : TorusAdj T m R Kc C) {ρ C₁ C₂ : ℝ} (hA : A.FBound ρ C₁)
    (h12 : C₁ ≤ C₂) : A.FBound ρ C₂ := fun K hK U =>
  (hA K hK U).trans (mul_le_mul_of_nonneg_right h12 (Real.sqrt_nonneg _))

theorem covOp_fbCovConst_le {ρ ω : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc : ℕ)
    (hb : covBound Hc ≤ ω * ρ ^ 2) : fbCovConst ρ Hc Kc ≤ (Kc : ℝ) ^ 2 * ω := by
  unfold fbCovConst
  have h2 : ((Kc : ℝ) / ρ) ^ 2 * ρ ^ 2 = (Kc : ℝ) ^ 2 := by field_simp
  calc covBound Hc * ((Kc : ℝ) / ρ) ^ 2 ≤ (ω * ρ ^ 2) * ((Kc : ℝ) / ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ = (Kc : ℝ) ^ 2 * ω := by
        rw [show ω * ρ ^ 2 * ((Kc : ℝ) / ρ) ^ 2 = ω * (((Kc : ℝ) / ρ) ^ 2 * ρ ^ 2) by ring, h2]
        ring

theorem covOp_covPolyConst_mono {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) (p : ℕ) :
    covPolyConst X p ≤ covPolyConst Y p :=
  Finset.sum_le_sum fun l _ =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hX hXY l) (by positivity)

/-! ### The flux statements -/

section Terminal

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The flux map `(Fin 2 → h v) → PiLp 2 (Fin 2 → h v)` as a continuous linear map. -/
def fluxL (v : ι) : (Fin 2 → h v) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h v)).symm.toContinuousLinearMap

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem fluxL_apply (v : ι) (F : Fin 2 → h v) : fluxL v F = toFluxL F := rfl

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_target_trunc (v : ι) (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (u : Vec 2 → Fin 2 → h v) (hu : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) u) :
    (fun x => toFluxL (u x - covPolyP H p (covPolyQ H p u) x)) =
      (fun x => fluxL v (u x)) - covPolyP H p (covPolyQ H p (fun x => fluxL v (u x))) := by
  have := covOp_PQ_clm H p (fluxL v) u hu
  funext x
  have hx := congrFun this x
  simp only [Pi.sub_apply, fluxL_apply] at hx ⊢
  rw [← hx]
  exact map_sub (fluxL v) _ _

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_target_P (v : ι) (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (u : Vec 2 → Fin 2 → h v) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) :
    (fun x => toFluxL (covPolyP H p u x)) = covPolyP H p (fun x => fluxL v (u x)) :=
  covOp_P_clm H p (fluxL v) u hu

section FluxDual

variable (v : ι) (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (u : Vec 2 → Fin 2 → h v)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_g_contDiff {n : ℕ} (hu : ContDiff ℝ (n : ℕ∞) u) :
    ContDiff ℝ (n : ℕ∞) (fun x => fluxL v (u x)) := by
  have := (fluxL v).contDiff.comp hu
  exact this

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_g_periodic (hpu : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (fun x => fluxL v (u x)) := fun n x => congrArg (fluxL v) (hpu n x)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_dual_trunc (hu : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) u)
    (hpu : AVenhance.IsZ2Periodic u) (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hpφ : AVenhance.IsZ2Periodic φ) :
    cellInner (fun x => toFluxL (u x)) (-qpRem H p φ) =
      cellInner (fun x => toFluxL (u x - covPolyP H p (covPolyQ H p u) x)) φ := by
  rw [covOp_flux_target_trunc v H p u hu]
  exact covOp_dual_trunc H p (covOp_flux_g_contDiff v u hu) (covOp_flux_g_periodic v u hpu) hφ hpφ

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_cont_trunc (hu : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) u) :
    Continuous (fun x => toFluxL (u x - covPolyP H p (covPolyQ H p u) x)) := by
  rw [covOp_flux_target_trunc v H p u hu]
  exact covOp_continuous_trunc H p (covOp_flux_g_contDiff v u hu)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_dual_P (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u)
    (hpu : AVenhance.IsZ2Periodic u) (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hpφ : AVenhance.IsZ2Periodic φ) :
    cellInner (fun x => toFluxL (u x)) (covPolyP H p φ) =
      cellInner (fun x => toFluxL (covPolyP H p u x)) φ := by
  rw [covOp_flux_target_P v H p u hu]
  exact (covOp_P_adjoint H p _ φ (covOp_flux_g_contDiff v u hu)
    (hφ.of_le (by exact_mod_cast le_top)) (covOp_flux_g_periodic v u hpu) hpφ).symm

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem covOp_flux_cont_P (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) :
    Continuous (fun x => toFluxL (covPolyP H p u x)) := by
  rw [covOp_flux_target_P v H p u hu]
  have hg := covOp_flux_g_contDiff v u hu
  have h0 : ContDiff ℝ (((0 + 2 * p : ℕ)) : ℕ∞) (fun x => fluxL v (u x)) := by
    simpa [Nat.zero_add] using hg
  exact (covOp_contDiff_P H p 0 h0).continuous

end FluxDual

section Main

variable (k p : ℕ) {I : Set ℝ}

/-- **The truncation operator at the flux level**: `G - 𝖯_p𝖰_p G` has a realization of order `k`. -/
theorem covOp_trunc_flux (hI : MeasurableSet I) (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν)
    (hρ : 0 < ρ) (hπ : ∀ v, 0 < π v) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ)
    (hHc : ContinuousOn Hc I) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hb : ∀ t ∈ I, covBound (Hc t) ≤ ω * ρ ^ 2) (Gf : ∀ v : ι, ℝ → Vec 2 → Fin 2 → h v) (Y : ℝ)
    (hreg : ∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 4 * p : ℕ) : ℕ∞) (Gf v t) ∧
      AVenhance.IsZ2Periodic (Gf v t))
    (hF : HasFluxBound (k + 4 * p) I ν ρ π (fun v t x => toFluxL (Gf v t x)) Y) :
    HasFluxBound k I ν ρ π (fun v t x => toFluxL
      (Gf v t x - covPolyP (Hc t) p (covPolyQ (Hc t) p (Gf v t)) x))
      (cqpBig (((k + 4 * p : ℕ) : ℝ) ^ 2) p * ω ^ (p + 1) * Y) := by
  have hM : ∀ s : ↥I, covBound (Hc s.1) ≤ ω * ρ ^ 2 := fun s => hb s.1 s.2
  have hcont : Continuous (fun s : ↥I => Hc s.1) := hHc.domRestrict
  have hCb : 0 ≤ cqpBig (((k + 4 * p : ℕ) : ℝ) ^ 2) p * ω ^ (p + 1) :=
    mul_nonneg (cqpBig_nonneg (by positivity) p) (pow_nonneg hω0 _)
  refine covOp_fluxBound_of_adj (m := 4 * p) hI ν ρ π hν hπ
    (fun v s => TorusAdj.qpRem (E := PiLp 2 (fun _ : Fin 2 => h v)) (Hc s.1) (hM s) p k
      (k + 4 * p))
    (fun v => covOp_adjCont_qpRem (H := fun s : ↥I => Hc s.1) hcont hM p k (k + 4 * p)) _ hCb
    ?_ _ _ Y hF ?_ ?_
  · intro v s
    refine covOp_FBound_mono _ (TorusAdj.FBound.qpRem hρ (Hc s.1) (hM s) p k (k + 4 * p)) ?_
    exact cqp_le (fbCovConst_nonneg hρ _ _) (by positivity) hω0 hω1
      (covOp_fbCovConst_le hρ _ _ (hb s.1 s.2)) p
  · intro v t ht
    exact covOp_flux_cont_trunc v (Hc t) p (Gf v t)
      ((hreg v t ht).1.of_le (by exact_mod_cast Nat.le_add_left _ _))
  · intro v t ht φ hφ hpφ
    exact covOp_flux_dual_trunc v (Hc t) p (Gf v t)
      ((hreg v t ht).1.of_le (by exact_mod_cast Nat.le_add_left _ _)) (hreg v t ht).2 φ hφ hpφ

/-- **At the flux level**: `𝖯_p G` has a realization of order `k`. -/
theorem covOp_P_flux (hI : MeasurableSet I) (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν)
    (hρ : 0 < ρ) (hπ : ∀ v, 0 < π v) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ)
    (hHc : ContinuousOn Hc I) (_hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hb : ∀ t ∈ I, covBound (Hc t) ≤ ω * ρ ^ 2) (Gf : ∀ v : ι, ℝ → Vec 2 → Fin 2 → h v) (Y : ℝ)
    (hreg : ∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 2 * p : ℕ) : ℕ∞) (Gf v t) ∧
      AVenhance.IsZ2Periodic (Gf v t))
    (hF : HasFluxBound (k + 2 * p) I ν ρ π (fun v t x => toFluxL (Gf v t x)) Y) :
    HasFluxBound k I ν ρ π (fun v t x => toFluxL (covPolyP (Hc t) p (Gf v t) x))
      (covPolyConst (((k + 2 * p : ℕ) : ℝ) ^ 2) p * Y) := by
  have hM : ∀ s : ↥I, covBound (Hc s.1) ≤ ω * ρ ^ 2 := fun s => hb s.1 s.2
  have hcont : Continuous (fun s : ↥I => Hc s.1) := hHc.domRestrict
  have hCb : 0 ≤ covPolyConst (((k + 2 * p : ℕ) : ℝ) ^ 2) p :=
    Finset.sum_nonneg fun l _ => by positivity
  refine covOp_fluxBound_of_adj (m := 2 * p) hI ν ρ π hν hπ
    (fun v s => TorusAdj.covPolyP (E := PiLp 2 (fun _ : Fin 2 => h v)) (Hc s.1) (hM s) p k
      (k + 2 * p))
    (fun v => covOp_adjCont_covPolyP (H := fun s : ↥I => Hc s.1) hcont hM p k (k + 2 * p)) _ hCb
    ?_ _ _ Y hF ?_ ?_
  · intro v s
    refine covOp_FBound_mono _ (TorusAdj.FBound.covPolyP hρ (Hc s.1) (hM s) p k (k + 2 * p)) ?_
    refine covOp_covPolyConst_mono (fbCovConst_nonneg hρ _ _) ?_ p
    exact (covOp_fbCovConst_le hρ _ _ (hb s.1 s.2)).trans
      (mul_le_of_le_one_right (by positivity) hω1)
  · intro v t ht
    exact covOp_flux_cont_P v (Hc t) p (Gf v t)
      ((hreg v t ht).1.of_le (by exact_mod_cast Nat.le_add_left _ _))
  · intro v t ht φ hφ hpφ
    exact covOp_flux_dual_P v (Hc t) p (Gf v t)
      ((hreg v t ht).1.of_le (by exact_mod_cast Nat.le_add_left _ _)) (hreg v t ht).2 φ hφ hpφ

end Main

end Terminal

end AVRegularity.EntryTerminal.CovOp

namespace AVRegularity.Construction.Residual.Presentation

open AVRegularity.EntryTerminal.CovOp

/-- `CovTruncOpStatement` with the window assumed measurable (the only change). -/
def CovTruncOpMeasStatement : Prop :=
  ∀ (k p : ℕ), ∃ Cop : ℝ, 0 ≤ Cop ∧
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (I : Set ℝ), MeasurableSet I → ∀ (ν ρ : ℝ) (π : ι → ℝ), 0 < ν → 0 < ρ → (∀ v, 0 < π v) →
    ∀ (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ), ContinuousOn Hc I → 0 ≤ ω → ω ≤ 1 →
    (∀ t ∈ I, AVRegularity.CycleComparison.Coarse.covBound (Hc t) ≤ ω * ρ ^ 2) →
    ∀ (Gf : ∀ v : ι, ℝ → Vec 2 → Fin 2 → h v) (Y : ℝ),
      (∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 4 * p : ℕ) : ℕ∞) (Gf v t) ∧ AVenhance.IsZ2Periodic (Gf v t)) →
      HasFluxBound (k + 4 * p) I ν ρ π (fun v t x => toFluxL (Gf v t x)) Y →
      HasFluxBound k I ν ρ π
        (fun v t x => toFluxL (Gf v t x - covPolyP (Hc t) p (covPolyQ (Hc t) p (Gf v t)) x))
        (Cop * ω ^ (p + 1) * Y)

/-- **The truncation operator (measurable window).** -/
theorem covTruncOp_meas : CovTruncOpMeasStatement := by
  intro k p
  refine ⟨cqpBig (((k + 4 * p : ℕ) : ℝ) ^ 2) p, cqpBig_nonneg (by positivity) p, ?_⟩
  intro ι _ h _ _ _ _ _ _ I hI ν ρ π hν hρ hπ Hc ω hHc hω0 hω1 hb Gf Y hreg hF
  exact covOp_trunc_flux k p hI ν ρ π hν hρ hπ Hc ω hHc hω0 hω1 hb Gf Y hreg hF

/-- `FilterPOpStatement` with the window assumed measurable (the only change). -/
def FilterPOpMeasStatement : Prop :=
  ∀ (k p : ℕ), ∃ Cp : ℝ, 0 ≤ Cp ∧
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (I : Set ℝ), MeasurableSet I → ∀ (ν ρ : ℝ) (π : ι → ℝ), 0 < ν → 0 < ρ → (∀ v, 0 < π v) →
    ∀ (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ), ContinuousOn Hc I → 0 ≤ ω → ω ≤ 1 →
    (∀ t ∈ I, AVRegularity.CycleComparison.Coarse.covBound (Hc t) ≤ ω * ρ ^ 2) →
    ∀ (Gf : ∀ v : ι, ℝ → Vec 2 → Fin 2 → h v) (Y : ℝ),
      (∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 2 * p : ℕ) : ℕ∞) (Gf v t) ∧ AVenhance.IsZ2Periodic (Gf v t)) →
      HasFluxBound (k + 2 * p) I ν ρ π (fun v t x => toFluxL (Gf v t x)) Y →
      HasFluxBound k I ν ρ π (fun v t x => toFluxL (covPolyP (Hc t) p (Gf v t) x)) (Cp * Y)

/-- **Measurable window.** -/
theorem filterPOp_meas : FilterPOpMeasStatement := by
  intro k p
  refine ⟨AVRegularity.CycleComparison.Coarse.covPolyConst (((k + 2 * p : ℕ) : ℝ) ^ 2) p,
    Finset.sum_nonneg fun l _ => by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ I hI ν ρ π hν hρ hπ Hc ω hHc hω0 hω1 hb Gf Y hreg hF
  exact covOp_P_flux k p hI ν ρ π hν hρ hπ Hc ω hHc hω0 hω1 hb Gf Y hreg hF

/-- **The truncation operator.** -/
theorem covTruncOp : CovTruncOpStatement := covTruncOp_meas

/-- **Realization of the covariance operator flux.** -/
theorem filterPOp : FilterPOpStatement := filterPOp_meas

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The dual identity for the gradient term of the covariance truncation**.

For `u` of class `C^{2p+1}` and `ℤ²`-periodic, the gradient flux `∇u` (as a field with values in
`PiLp 2 (Fin 2 → h)`) satisfies
`cov^p ∇u = ∇ cov^p u` (`covGrad_commute`) and, for smooth periodic `φ`,
`⟨∇u, (p!)⁻¹ cov^p (Nᵀ φ)⟩ = ⟨N (p!)⁻¹ cov^p ∇u, φ⟩` (`covGrad_dual`), where `N` acts on the
gradient index. The right side is `covTruncGrad`'s flux (`covGrad_target_eq`).

Special cases:
- `p = 0`, `N = I`: `⟨∇u, φ⟩ = ⟨∇u, φ⟩`.
- `N = 0`: both sides vanish. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.CovGrad

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℝ h] [MeasurableSpace h]
  [BorelSpace h] [CompleteSpace h] [FiniteDimensional ℝ h]

/-- The matrix action as a continuous linear map. -/
def matCLM (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PiLp 2 (fun _ : Fin 2 => h) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h) :=
  LinearMap.toContinuousLinearMap
    { toFun := matAct M
      map_add' := fun v w => by
        ext j
        simp [matAct, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext j
        simp [matAct, smul_comm c] }

theorem matAct_smul (M : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (w : PiLp 2 (fun _ : Fin 2 => h)) :
    matAct M (c • w) = c • matAct M w := (matCLM M).map_smul c w

/-- The gradient flux of a scalar-type field. -/
def gradFlux (u : Vec 2 → h) : Vec 2 → PiLp 2 (fun _ : Fin 2 => h) :=
  fun x => toFluxL (gradE u x)

theorem gradFlux_eq (u : Vec 2 → h) (x : Vec 2) :
    gradFlux u x = WithLp.toLp 2 (fun j => partialOp j u x) := rfl

theorem contDiff_gradFlux {n : ℕ} {u : Vec 2 → h} (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u) :
    ContDiff ℝ (n : WithTop ℕ∞) (gradFlux u) := by
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fun x => fun j : Fin 2 => partialOp j u x) :=
    contDiff_pi.2 fun j => contDiff_partialOp hu j
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h)).symm.contDiff.comp h1

theorem periodic_gradFlux {u : Vec 2 → h} (hu : ContDiff ℝ 1 u) (hp : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (gradFlux u) := fun n x => by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hj : ∀ j, AVenhance.IsZ2Periodic (partialOp j u) := fun j => isZ2Periodic_partialOp hd hp j
  rw [gradFlux_eq, gradFlux_eq]
  exact congrArg (WithLp.toLp 2) (funext fun j => hj j n x)

theorem covGrad_commute (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {u : Vec 2 → h}
    (hu : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) u) :
    (covOperator H)^[p] (gradFlux u) = gradFlux ((covOperator H)^[p] u) := by
  funext x
  ext j
  have hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (gradFlux u) := contDiff_gradFlux hu
  have h1 := Finite.TerminalLift.terminal_covariance_iterate_clm H
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h) j) p (gradFlux u) hf x
  have hu' : ContDiff ℝ ((p * 2 + 1 : ℕ) : WithTop ℕ∞) u := by
    rwa [Nat.mul_comm]
  have h2 := (ConstCoefOp.covIter (E := h) H p).comm j u hu'
  have h3 : (fun y => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h) j) (gradFlux u y)) = partialOp j u := rfl
  rw [h3] at h1
  rw [gradFlux_eq]
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h) j) _ = _
  rw [h1]
  exact congrFun h2 x

theorem inner_matAct (N : Matrix (Fin 2) (Fin 2) ℝ) (v w : PiLp 2 (fun _ : Fin 2 => h)) :
    inner ℝ (matAct N v) w = inner ℝ v (matAct N.transpose w) := by
  simp only [matAct, PiLp.inner_apply, Fin.sum_univ_two, real_inner_smul_left,
    real_inner_smul_right, Matrix.transpose_apply, inner_add_left, inner_add_right]
  ring

theorem covGrad_pow_eq_poly (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Vec 2 → E) :
    covariancePolynomial H p (fun l => if l = p then 1 else 0) g = (covOperator H)^[p] g := by
  funext x
  unfold covariancePolynomial
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hp
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self p)) hp

theorem cellInner_smul_right' (c : ℝ) (g q : Vec 2 → PiLp 2 (fun _ : Fin 2 => h)) :
    cellInner g (fun x => c • q x) = c * cellInner g q := by
  unfold cellInner
  simp_rw [real_inner_smul_right]
  exact MeasureTheory.integral_const_mul c _

theorem covGrad_dual (H N : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {u : Vec 2 → h}
    (hu : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) u) (hpu : AVenhance.IsZ2Periodic u)
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hpφ : AVenhance.IsZ2Periodic φ) :
    cellInner (gradFlux u) (fun x => ((p.factorial : ℝ)⁻¹) •
        (covOperator H)^[p] (fun y => matAct N.transpose (φ y)) x) =
      cellInner (fun x => matAct N (((p.factorial : ℝ)⁻¹) • gradFlux ((covOperator H)^[p] u) x)) φ := by
  have hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (gradFlux u) := contDiff_gradFlux hu
  have hpf : AVenhance.IsZ2Periodic (gradFlux u) :=
    periodic_gradFlux (hu.of_le (by exact_mod_cast Nat.le_add_left 1 (2 * p))) hpu
  have hψ : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fun y => matAct N.transpose (φ y)) :=
    (matCLM N.transpose).contDiff.comp (hφ.of_le (by exact_mod_cast le_top))
  have hpψ : AVenhance.IsZ2Periodic (fun y => matAct N.transpose (φ y)) :=
    fun n x => congrArg (matAct N.transpose) (hpφ n x)
  rw [cellInner_smul_right']
  have hadj := covOp_polynomial_adjoint H p (fun l => if l = p then 1 else 0) (gradFlux u)
    (fun y => matAct N.transpose (φ y)) hf hψ hpf hpψ
  rw [covGrad_pow_eq_poly, covGrad_pow_eq_poly] at hadj
  rw [← hadj, covGrad_commute H p hu]
  have : cellInner (fun x => matAct N (((p.factorial : ℝ)⁻¹) •
      gradFlux ((covOperator H)^[p] u) x)) φ =
      ((p.factorial : ℝ)⁻¹) * cellInner (gradFlux ((covOperator H)^[p] u))
        (fun y => matAct N.transpose (φ y)) := by
    unfold cellInner
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [matAct_smul, real_inner_smul_left, inner_matAct]
  rw [this]

theorem covGrad_target_eq (H N : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {u : Vec 2 → h}
    (hu : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) u) :
    (fun x => toFluxL (fun j => ∑ l : Fin 2, N j l •
        gradE (fun y => ((p.factorial : ℝ)⁻¹) • (covOperator H)^[p] u y) x l)) =
      fun x => matAct N (((p.factorial : ℝ)⁻¹) • gradFlux ((covOperator H)^[p] u) x) := by
  have hd : Differentiable ℝ ((covOperator H)^[p] u) := by
    have := covOperator_iterate_contDiff H p 1 u (by
      simpa [Nat.add_comm, Nat.mul_comm] using hu)
    exact this.differentiable (by norm_num)
  funext x
  ext j
  simp only [toFluxL, matAct, gradFlux_eq, gradE, partialOp_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : (fun y => ((p.factorial : ℝ)⁻¹) • (covOperator H)^[p] u y) =
      ((p.factorial : ℝ)⁻¹) • (covOperator H)^[p] u := rfl
  rw [e, fderiv_const_smul (hd x)]
  simp [smul_comm (N j l)]

end AVRegularity.EntryTerminal.CovGrad
end
end

section
/-! **The gradient term of the covariance truncation at the flux level** (engine).

Let `F = ∇u` be a gradient flux with a realization of order `k + 2p` and mass `Y`. Then
`(N_t) (p!)⁻¹ 𝒞(H_t)^p ∇u` (the matrix acts on the gradient index) has a realization of order `k`
with mass `aN ((k+2p)² ω)^p / p! · Y` (`covGrad_flux`), where `covBound (H_t) ≤ ω ρ²` and
`∑ |N_t i j| ≤ aN`. The realization is by the formal adjoint
`φ ↦ (p!)⁻¹ 𝒞^p (Nᵀ φ)` (`covGradAdj`), continuous in `t`.

Special cases:
- `p = 0`: the statement is that `N ∇u` is realized with the mass `aN Y`.
- `ω = 0`, `p ≥ 1`: the bound is `0` (and indeed `𝒞 = 0` when `H = 0`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.CovGrad

section Adj

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℝ h] [MeasurableSpace h]
  [BorelSpace h] [CompleteSpace h] [FiniteDimensional ℝ h]

/-- The formal adjoint `φ ↦ (p!)⁻¹ 𝒞^p (Nᵀ φ)` of order `2p`. -/
def covGradAdj (H N : Matrix (Fin 2) (Fin 2) ℝ) {M aN : ℝ} (hM : covBound H ≤ M)
    (hN : ∑ jl : Fin 2 × Fin 2, |N jl.1 jl.2| ≤ aN) (hM0 : 0 ≤ M) (p k : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h)) =>
      ((p.factorial : ℝ)⁻¹) • (covOperator H)^[p] (fun x => matAct N.transpose (ψ x)))
      (2 * p) k (k + 2 * p)
      (|((p.factorial : ℝ)⁻¹)| * (M ^ p * (aN * (((k + 2 * p).factorial : ℝ) * 1 *
        (((k + 2 * p).factorial : ℝ) * 1))))) :=
  ((((TorusAdj.covIter (E := PiLp 2 (fun _ : Fin 2 => h)) H hM p k (k + 2 * p)).comp
    (matOp (h := h) N.transpose (k + 2 * p) (k + 2 * p)) le_rfl (by omega)).ofOrder
      (by omega : 2 * p + 0 = 2 * p)).smul ((p.factorial : ℝ)⁻¹)).mono le_rfl le_rfl (by
      have hq : 0 ≤ ((k + 2 * p).factorial : ℝ) * 1 * (((k + 2 * p).factorial : ℝ) * 1) := by
        positivity
      have hT : ∑ jl : Fin 2 × Fin 2, |N.transpose jl.1 jl.2| ≤ aN := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.transpose_apply] at hN ⊢
        linarith
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hT hq) (pow_nonneg hM0 p)) (abs_nonneg _))

theorem covGradAdj_fbound {ρ : ℝ} (hρ : 0 < ρ) (H N : Matrix (Fin 2) (Fin 2) ℝ) {M aN : ℝ}
    (hM : covBound H ≤ M) (hN : ∑ jl : Fin 2 × Fin 2, |N jl.1 jl.2| ≤ aN) (hM0 : 0 ≤ M)
    (haN : 0 ≤ aN) (p k : ℕ) :
    (covGradAdj (h := h) H N hM hN hM0 p k).FBound ρ
      (|((p.factorial : ℝ)⁻¹)| * (fbCovConst ρ H (k + 2 * p) ^ p * aN)) := by
  have hT : ∑ jl : Fin 2 × Fin 2, |N.transpose jl.1 jl.2| ≤ aN := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.transpose_apply] at hN ⊢
    linarith
  unfold covGradAdj
  exact TorusAdj.FBound.mono (TorusAdj.FBound.smul _ (TorusAdj.FBound.ofOrder _
    (TorusAdj.FBound.comp (TorusAdj.FBound.covIter (E := PiLp 2 (fun _ : Fin 2 => h)) hρ H hM p k
      (k + 2 * p)) (fbound_matOp_le ρ hρ.le N.transpose aN hT _ _) haN le_rfl (by omega))))
    le_rfl le_rfl _

theorem covGradAdj_cont {S : Type*} [TopologicalSpace S] {H N : S → Matrix (Fin 2) (Fin 2) ℝ}
    {M aN : ℝ} (hH : Continuous H) (hNc : Continuous N) (hM : ∀ s, covBound (H s) ≤ M)
    (hN : ∀ s, ∑ jl : Fin 2 × Fin 2, |N s jl.1 jl.2| ≤ aN) (hM0 : 0 ≤ M) (p k : ℕ) :
    AdjCont (fun s => covGradAdj (h := h) (H s) (N s) (hM s) (hN s) hM0 p k) := by
  unfold covGradAdj
  exact AdjCont.mono _ _ _ (AdjCont.smul (fun _ => _) continuous_const
    (AdjCont.ofOrder _ (AdjCont.comp (covOp_adjCont_covIter hH hM p k (k + 2 * p))
      (covGrad_adjCont_matOp hNc.matrix_transpose _ _) _ _)))

end Adj

section Main

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The gradient term at the flux level.** -/
theorem covGrad_flux (k p : ℕ) {I : Set ℝ} (hI : MeasurableSet I) (ν ρ : ℝ) (π : ι → ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hπ : ∀ v, 0 < π v) (Hc Nc : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (ω aN : ℝ) (hHc : ContinuousOn Hc I) (hNc : ContinuousOn Nc I) (hω0 : 0 ≤ ω)
    (hb : ∀ t ∈ I, covBound (Hc t) ≤ ω * ρ ^ 2)
    (hN : ∀ t ∈ I, ∑ jl : Fin 2 × Fin 2, |Nc t jl.1 jl.2| ≤ aN) (haN : 0 ≤ aN)
    (u : ∀ v : ι, ℝ → Vec 2 → h v) (Y : ℝ)
    (hreg : ∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 2 * p + 1 : ℕ) : WithTop ℕ∞) (u v t) ∧
      AVenhance.IsZ2Periodic (u v t))
    (hF : HasFluxBound (k + 2 * p) I ν ρ π (fun v t x => toFluxL (gradE (u v t) x)) Y) :
    HasFluxBound k I ν ρ π (fun v t x => toFluxL (fun j => ∑ l : Fin 2, Nc t j l •
      gradE (fun y => ((p.factorial : ℝ)⁻¹) • (covOperator (Hc t))^[p] (u v t) y) x l))
      (((p.factorial : ℝ)⁻¹) * ((((k + 2 * p : ℕ) : ℝ) ^ 2 * ω) ^ p * aN) * Y) := by
  have hM : ∀ s : ↥I, covBound (Hc s.1) ≤ ω * ρ ^ 2 := fun s => hb s.1 s.2
  have hNs : ∀ s : ↥I, ∑ jl : Fin 2 × Fin 2, |Nc s.1 jl.1 jl.2| ≤ aN := fun s => hN s.1 s.2
  have hcH : Continuous (fun s : ↥I => Hc s.1) := hHc.domRestrict
  have hcN : Continuous (fun s : ↥I => Nc s.1) := hNc.domRestrict
  have hM0 : 0 ≤ ω * ρ ^ 2 := by positivity
  have hCb : 0 ≤ ((p.factorial : ℝ)⁻¹) * ((((k + 2 * p : ℕ) : ℝ) ^ 2 * ω) ^ p * aN) := by
    positivity
  refine covOp_fluxBound_of_adj (m := 2 * p) hI ν ρ π hν hπ
    (fun v s => covGradAdj (h := h v) (Hc s.1) (Nc s.1) (hM s) (hNs s) hM0 p k)
    (fun v => covGradAdj_cont hcH hcN hM hNs hM0 p k) _ hCb ?_ _ _ Y hF ?_ ?_
  · intro v s
    refine covOp_FBound_mono _ (covGradAdj_fbound hρ (Hc s.1) (Nc s.1) (hM s) (hNs s) hM0 haN p k)
      ?_
    rw [abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ haN) (inv_nonneg.2 (Nat.cast_nonneg _))
    exact pow_le_pow_left₀ (fbCovConst_nonneg hρ _ _) (covOp_fbCovConst_le hρ _ _ (hb s.1 s.2)) p
  · intro v t ht
    have hu : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) (u v t) :=
      (hreg v t ht).1.of_le (by exact_mod_cast (by omega : 2 * p + 1 ≤ k + 2 * p + 1))
    have h1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) ((covOperator (Hc t))^[p] (u v t)) :=
      Construction.Preservation.FullLift.covOperator_iterate_contDiff (Hc t) p 1 (u v t) (by simpa [Nat.add_comm] using hu)
    rw [covGrad_target_eq (Hc t) (Nc t) p hu]
    exact (matCLM (Nc t)).continuous.comp
      ((continuous_const_smul _).comp (contDiff_gradFlux (n := 0) h1).continuous)
  · intro v t ht φ hφ hpφ
    have hu : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) (u v t) :=
      (hreg v t ht).1.of_le (by exact_mod_cast (by omega : 2 * p + 1 ≤ k + 2 * p + 1))
    rw [covGrad_target_eq (Hc t) (Nc t) p hu]
    exact covGrad_dual (Hc t) (Nc t) p hu (hreg v t ht).2 φ hφ hpφ

end Main

end AVRegularity.EntryTerminal.CovGrad
end
end
end

section
section
/-! **The commutator adjoint of the commutator term, and the statements it rests on**.

The commutator part `commGen` of the pre-truncation flux `G` is
`∑_{l=1}^p (l!)⁻¹ ∑_{a<l} 𝒞^a 𝒥_H 𝒞^{l-1-a} u`, `𝒥_H g = -(Db H + H Dbᵀ) ∇g` (`commFluxE`).
Its formal adjoint against the gradient flux `∇u` is the vector operator `commVecOp`,
`φ ↦ (-(∑_{l,a} (l!)⁻¹ 𝒞^{l-1-a}(𝔑_j 𝒞^a φ)))_j`, assembled in `commVec` from the fixed-time
`TorusAdj.commStep` of the coarse theory, as an operator of order `2p`.

Five statements are used by the engine `covComm_flux`:
* `MulLipStatement`: operator-norm Lipschitz bound of coefficient multiplication;
* `StreamArrayContStatement`: uniform-in-space continuity in time of the derivative arrays of a
  jointly smooth, spatially periodic family;
* `CommAdjContStatement`: the family `s ↦ commVec h s` is continuous in operator norm;
* `CommPriceStatement`: its factorial-norm price is `κ · commPriceConst`;
* `CommDualStatement`: the duality `⟨∇u, S φ⟩ = ⟨target, φ⟩` and continuity of the target.

Special cases:
- `p = 0`: `commGen = 0` and `commVec` is the zero operator.
- `Hc = 0`: both sides of the duality vanish. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.EntryTerminal.CovGrad AVRegularity

namespace AVRegularity.EntryTerminal.CovComm

/-- Hypotheses on the data of the commutator adjoint on a window. -/
structure CommHyp (b : ℝ → Vec 2 → Vec 2) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (I : Set ℝ)
    (k p : ℕ) (M : ℝ) (Bb : ℕ → ℝ) : Prop where
  smooth : ∀ s ∈ I, ContDiff ℝ ((k + 2 * p + 3 : ℕ) : WithTop ℕ∞) (b s)
  periodic : ∀ s ∈ I, AVenhance.IsZ2Periodic (b s)
  cov : ∀ s ∈ I, covBound (Hc s) ≤ M
  drift : ∀ s ∈ I, ∀ l ≤ k + 2 * p, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The constant of `commComp`. -/
def commCompConst (M : ℝ) (Bb : ℕ → ℝ) (Kc p : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 p, |((l.factorial : ℝ)⁻¹)| *
    ∑ a ∈ Finset.range l, M ^ (l - 1 - a) * (mulConst (commBound M Bb) Kc * M ^ a)

/-- The `j`-th component of the (unsigned) commutator adjoint, an operator of order `2p`. -/
def commComp {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ} {k p : ℕ}
    {M : ℝ} {Bb : ℕ → ℝ} (h : CommHyp b Hc I k p M Bb) (s : ↥I) (j : Fin 2) :
    TorusAdj (fun (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (x : Vec 2) =>
      ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
        commStepOp (E := E) b s.1 (Hc s.1) j (l - 1 - a) a φ x) (2 * p) k (k + 2 * p)
      (commCompConst M Bb (k + 2 * p) p) :=
  ((TorusAdj.sumMem (Finset.Icc 1 p) fun l hl =>
    (TorusAdj.sumMem (Finset.range l) fun a ha =>
      (TorusAdj.commStep (E := E) (Hc s.1) (h.cov s.1 s.2) b s.1 j k (k + 2 * p) (k + 2 * p + 3) p 1
        l a (Finset.mem_range.mp ha) (Finset.mem_Icc.mp hl).2 (by omega) (by omega)
        (h.smooth s.1 s.2) (h.periodic s.1 s.2) Bb (h.drift s.1 s.2)).ofOrder
        (by omega : 2 * p + 1 - 1 = 2 * p)).smul ((l.factorial : ℝ)⁻¹)).mono le_rfl le_rfl
    (le_of_eq (by unfold commCompConst; rfl))).ofOp (by funext φ x; rfl)

/-- The vector commutator adjoint operator `φ ↦ (-(∑_{l,a} (l!)⁻¹ 𝒞^{l-1-a}(𝔑_j 𝒞^a φ)))_j`. -/
def commVecOp (b : ℝ → Vec 2 → Vec 2) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (s : ℝ)
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => E) :=
  WithLp.toLp 2 (fun j => -(∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
    commStepOp (E := E) b s (Hc s) j (l - 1 - a) a φ x))

/-- The vector commutator adjoint, a formal adjoint of order `2p`. -/
def commVec {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ} {k p : ℕ}
    {M : ℝ} {Bb : ℕ → ℝ} (h : CommHyp b Hc I k p M Bb) (s : ↥I) :
    TorusAdj (commVecOp (E := E) b Hc p s.1) (2 * p) k (k + 2 * p)
      (∑ _j : Fin 2, (((k + 2 * p).factorial : ℝ) * 1) * commCompConst M Bb (k + 2 * p) p) :=
  (TorusAdj.sum (Finset.univ : Finset (Fin 2)) fun j =>
    ((singleOp (h := E) j k (k + 2 * p)).comp (commComp (E := E) h s j).neg le_rfl
      (by omega)).ofOrder (by omega : 0 + 2 * p = 2 * p)).ofOp (by
    funext φ x
    ext j
    fin_cases j <;> simp [commVecOp, piSingleCLM_apply])


/-- The commutator part of the flux, for general data (`gCommTerm` is the case
`b = streamVel (Φ (m-1))`, `Hc = menuCovPrimitive`). -/
def commGen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ℝ → Vec 2 → Vec 2)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (t : ℝ) (u : Vec 2 → E) (x : Vec 2) :
    Fin 2 → E :=
  ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
    (covOperator (Hc t))^[a'] (commFluxE (b t) (Hc t) ((covOperator (Hc t))^[l - 1 - a'] u)) x

/-- Uniform continuity in time of the derivative arrays of order `≤ n + 1`. -/
def TimeCont (b : ℝ → Vec 2 → Vec 2) (I : Set ℝ) (n : ℕ) : Prop :=
  ∀ s₀ ∈ I, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ I, |s - s₀| < δ → ∀ l ≤ n, ∀ x,
    ‖iteratedFDeriv ℝ (l + 1) (b s) x - iteratedFDeriv ℝ (l + 1) (b s₀) x‖ ≤ ε

/-- The constant of the price: `fbCovConst ≤ Kc² ω`, `fbMulConst ≤ 4 (Kc+1)² 4^Kc ω κ`. -/
def commPriceConst (Kc p : ℕ) (ω : ℝ) : ℝ :=
  (2 : ℝ) * ∑ l ∈ Finset.Icc 1 p, (l.factorial : ℝ)⁻¹ * ∑ a ∈ Finset.range l,
    (((Kc : ℝ) ^ 2 * ω) ^ (l - 1 - a) * ((4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) *
      ((Kc : ℝ) ^ 2 * ω) ^ a))

/-- **(A)** Operator-norm Lipschitz bound of coefficient multiplication in its coefficient. -/
def MulLipStatement : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [MeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y] [CompleteSpace Y]
    [FiniteDimensional ℝ Y] {K : ℕ} (N N' : Vec 2 → X →L[ℝ] Y)
    (hN : ContDiff ℝ (K : ℕ) N) (hN' : ContDiff ℝ (K : ℕ) N') (hp : AVenhance.IsZ2Periodic N)
    (hp' : AVenhance.IsZ2Periodic N') {A A' : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l)
    (hb' : ∀ l x, ‖coefficientDerivativeArray N' l.val x‖ ≤ A' l) (Δ : Fin (K + 1) → ℝ)
    (_ : ∀ l : Fin (K + 1), ∀ x, ‖coefficientDerivativeArray (fun y => N y - N' y) l.val x‖ ≤ Δ l),
    ‖torusMulCLM N hN hp hb - torusMulCLM N' hN' hp' hb'‖ ≤ mulConstK K Δ

/-- **(B)** Uniform-in-space continuity in time of the derivative arrays of a jointly smooth,
spatially periodic family. -/
def StreamArrayContStatement : Prop :=
  ∀ (G : ℝ → Vec 2 → Vec 2), ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => G q.1 q.2) →
    (∀ s, AVenhance.IsZ2Periodic (G s)) → ∀ (n : ℕ) (s₀ ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s, |s - s₀| < δ → ∀ x,
        ‖iteratedFDeriv ℝ n (G s) x - iteratedFDeriv ℝ n (G s₀) x‖ ≤ ε

/-- **(C)** The adjoint maps of the vector commutator adjoint depend continuously on time. -/
def CommAdjContStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ} {k p : ℕ} {M : ℝ}
    {Bb : ℕ → ℝ} (h : CommHyp b Hc I k p M Bb), ContinuousOn Hc I → TimeCont b I (k + 2 * p) →
      AdjCont (fun s : ↥I => commVec (E := E) h s)

/-- **(D)** The factorial-norm price of the vector commutator adjoint. -/
def CommPriceStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ} {k p : ℕ}
    {ρ ω a B₀ lam κ : ℝ}
    (h : CommHyp b Hc I k p (ω * ρ ^ 2) (driftB a B₀ lam)), 0 < ρ → 0 ≤ ω → 0 ≤ a → 1 ≤ B₀ →
      0 < lam → B₀ * ρ / lam ≤ 1 / 2 → a * B₀ * ρ ^ 2 ≤ κ / 8 → 0 ≤ κ → ∀ s : ↥I,
        (commVec (E := E) h s).FBound ρ (κ * commPriceConst (k + 2 * p) p ω)

/-- **(E)** The duality of the commutator flux with the vector adjoint, and continuity of the
flux. -/
def CommDualStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (b : ℝ → Vec 2 → Vec 2) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (s : ℝ)
    (u : Vec 2 → E), ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) (b s) →
      AVenhance.IsZ2Periodic (b s) → ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) u →
      AVenhance.IsZ2Periodic u →
      Continuous (fun x => toFluxL (commGen b Hc p s u x)) ∧
        ∀ φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E), ContDiff ℝ (⊤ : ℕ∞) φ →
          AVenhance.IsZ2Periodic φ →
          cellInner (gradFlux u) (commVecOp b Hc p s φ) =
            cellInner (fun x => toFluxL (commGen b Hc p s u x)) φ

end AVRegularity.EntryTerminal.CovComm
end
end

section
/-! **The commutator term at the flux level** (engine).

Let `∇u` be a gradient flux with a realization of order `k + 2p` and mass `Y`. Given the data of a
commutator adjoint on the window `I` (`CommHyp`), continuous in time (`TimeCont`), the flux
`commGen b Hc p t (u t)` has a realization of order `k` with mass `κ · commPriceConst · Y`
(`covComm_flux`). The realization is by the formal adjoint `commVec`; the proof is
`covOp_fluxBound_of_adj` with the statements `CommAdjContStatement`, `CommPriceStatement`,
`CommDualStatement`.

Special cases:
- `κ = 0`: the bound is `0`.
- `p = 0`: `commPriceConst = 0` and the flux `commGen` vanishes. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.EntryTerminal.CovGrad AVRegularity
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.CovComm

theorem commPriceConst_nonneg (Kc p : ℕ) {ω : ℝ} (hω : 0 ≤ ω) : 0 ≤ commPriceConst Kc p ω := by
  unfold commPriceConst
  positivity

section Main

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The commutator term at the flux level.** -/
theorem covComm_flux (hC : CommAdjContStatement) (hD : CommPriceStatement)
    (hE : CommDualStatement) (k p : ℕ) {I : Set ℝ} (hI : MeasurableSet I) (ν ρ : ℝ) (π : ι → ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hπ : ∀ v, 0 < π v) (b : ℝ → Vec 2 → Vec 2)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω a B₀ lam κ : ℝ) (hHc : ContinuousOn Hc I)
    (hbc : TimeCont b I (k + 2 * p))
    (hhyp : CommHyp b Hc I k p (ω * ρ ^ 2) (driftB a B₀ lam)) (hω : 0 ≤ ω) (ha : 0 ≤ a)
    (hB₀ : 1 ≤ B₀) (hlam : 0 < lam) (hu : B₀ * ρ / lam ≤ 1 / 2) (hst : a * B₀ * ρ ^ 2 ≤ κ / 8)
    (hκ : 0 ≤ κ) (u : ∀ v : ι, ℝ → Vec 2 → h v) (Y : ℝ)
    (hreg : ∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 2 * p + 1 : ℕ) : WithTop ℕ∞) (u v t) ∧
      AVenhance.IsZ2Periodic (u v t))
    (hF : HasFluxBound (k + 2 * p) I ν ρ π (fun v t x => toFluxL (gradE (u v t) x)) Y) :
    HasFluxBound k I ν ρ π (fun v t x => toFluxL (commGen b Hc p t (u v t) x))
      ((κ * commPriceConst (k + 2 * p) p ω) * Y) := by
  have hCb : 0 ≤ κ * commPriceConst (k + 2 * p) p ω :=
    mul_nonneg hκ (commPriceConst_nonneg _ _ hω)
  have hdat : ∀ v t (ht : t ∈ I), ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) (b t) ∧
      ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) (u v t) := fun v t ht =>
    ⟨(hhyp.smooth t ht).of_le (by exact_mod_cast (by omega : 2 * p + 1 ≤ k + 2 * p + 3)),
      (hreg v t ht).1.of_le (by exact_mod_cast (by omega : 2 * p + 1 ≤ k + 2 * p + 1))⟩
  refine covOp_fluxBound_of_adj (m := 2 * p) hI ν ρ π hν hπ
    (fun v s => commVec (E := h v) hhyp s) (fun v => hC hhyp hHc hbc) _ hCb
    (fun v s => hD hhyp hρ hω ha hB₀ hlam hu hst hκ s) _ _ Y hF ?_ ?_
  · intro v t ht
    exact (hE b Hc p t (u v t) (hdat v t ht).1 (hhyp.periodic t ht) (hdat v t ht).2
      (hreg v t ht).2).1
  · intro v t ht φ hφ hpφ
    exact (hE b Hc p t (u v t) (hdat v t ht).1 (hhyp.periodic t ht) (hdat v t ht).2
      (hreg v t ht).2).2 φ hφ hpφ

end Main

end AVRegularity.EntryTerminal.CovComm
end
end

section
/-! **Coefficient multiplication is Lipschitz in its coefficient** (statement (A)).

`torusMulCLM` is additive in the coefficient: for `C^K` coefficients `N`, `N'` the difference of the
multiplication operators is the multiplication operator of `N - N'`, because every term of the
ordered Leibniz formula is linear in the coefficient (`multiplicationRawJet_sub`). The operator-norm
bound of the difference is then the existing bound `norm_torusMulCLM_le` for `N - N'`
(`mulLip : MulLipStatement`).

Special cases:
- `N = N'`: the difference is `0`, the bound is `mulConstK K Δ` with `Δ = 0`.
- `K = 0`: the bound is the sup-norm of `N - N'`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.CovComm

section Linear

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The ordered coefficient derivatives are additive in the coefficient (up to order `K`). -/
theorem orderedCoeff_sub (C C' : Vec 2 → X →L[ℝ] Y) :
    ∀ (j : ℕ), ContDiff ℝ (j : ℕ) C → ContDiff ℝ (j : ℕ) C' → ∀ (w : DerivativeWord2 j) (x : Vec 2),
      orderedCoefficientDerivative (fun y => C y - C' y) j w x =
        orderedCoefficientDerivative C j w x - orderedCoefficientDerivative C' j w x
  | 0, _, _, _, _ => rfl
  | j + 1, hC, hC', w, x => by
    have ih : orderedCoefficientDerivative (fun y => C y - C' y) j (Fin.init w) =
        fun y => orderedCoefficientDerivative C j (Fin.init w) y -
          orderedCoefficientDerivative C' j (Fin.init w) y :=
      funext fun y => orderedCoeff_sub C C' j (hC.of_le (by exact_mod_cast Nat.le_succ j))
        (hC'.of_le (by exact_mod_cast Nat.le_succ j)) (Fin.init w) y
    have hd : DifferentiableAt ℝ (orderedCoefficientDerivative C j (Fin.init w)) x :=
      (orderedCoefficientDerivative_contDiff C j 1 (by simpa using hC) (Fin.init w)).differentiable
        (by simp) x
    have hd' : DifferentiableAt ℝ (orderedCoefficientDerivative C' j (Fin.init w)) x :=
      (orderedCoefficientDerivative_contDiff C' j 1 (by simpa using hC') (Fin.init w)).differentiable
        (by simp) x
    change fderiv ℝ (orderedCoefficientDerivative (fun y => C y - C' y) j (Fin.init w)) x
        (basisVec (w (Fin.last j))) =
      fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x (basisVec (w (Fin.last j))) -
      fderiv ℝ (orderedCoefficientDerivative C' j (Fin.init w)) x (basisVec (w (Fin.last j)))
    have hs : HasFDerivAt (fun y => orderedCoefficientDerivative C j (Fin.init w) y -
        orderedCoefficientDerivative C' j (Fin.init w) y)
        (fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x -
          fderiv ℝ (orderedCoefficientDerivative C' j (Fin.init w)) x) x :=
      hd.hasFDerivAt.sub hd'.hasFDerivAt
    rw [ih, hs.fderiv]
    rfl

/-- The ordered Leibniz jet is additive in the coefficient. -/
theorem multiplicationRawJet_sub {K : ℕ} (C C' : Vec 2 → X →L[ℝ] Y) (hC : ContDiff ℝ (K : ℕ) C)
    (hC' : ContDiff ℝ (K : ℕ) C') (D : RawJet2 K X) (a : JetIndex2 K) (x : Vec 2) :
    multiplicationRawJet C D a x =
      multiplicationRawJet (fun y => C y - C' y) D a x + multiplicationRawJet C' D a x := by
  unfold multiplicationRawJet multiplicationTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hle : maskLeftLength a.1.val m ≤ K :=
    (maskLeftLength_le a.1.val m).trans (Nat.le_of_lt_succ a.1.isLt)
  rw [orderedCoeff_sub C C' _ (hC.of_le (by exact_mod_cast hle)) (hC'.of_le (by exact_mod_cast hle))]
  simp

end Linear

section Mul

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [MeasurableSpace X]
  [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {K : ℕ}

omit [FiniteDimensional ℝ Y] in
/-- Coefficient multiplication is additive in the coefficient. -/
theorem torusMulCLM_sub (N N' : Vec 2 → X →L[ℝ] Y)
    (hN : ContDiff ℝ (K : ℕ) N) (hN' : ContDiff ℝ (K : ℕ) N') (hp : AVenhance.IsZ2Periodic N)
    (hp' : AVenhance.IsZ2Periodic N') {A A' Δ : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l)
    (hb' : ∀ l x, ‖coefficientDerivativeArray N' l.val x‖ ≤ A' l)
    (hD : ContDiff ℝ (K : ℕ) (fun y => N y - N' y))
    (hpD : AVenhance.IsZ2Periodic (fun y => N y - N' y))
    (hbD : ∀ l : Fin (K + 1), ∀ x, ‖coefficientDerivativeArray (fun y => N y - N' y) l.val x‖ ≤ Δ l) :
    torusMulCLM N hN hp hb - torusMulCLM N' hN' hp' hb' =
      torusMulCLM (fun y => N y - N' y) hD hpD hbD := by
  ext1 U
  rw [sub_apply, sub_eq_iff_eq_add]
  simp only [torusMulCLM_apply]
  apply torusHk_ext_of_jet_ae
  filter_upwards [mulCoefficient_jet_ae (N := N) (hN := hN) (hp := hp) (hb := hb) U,
    mulCoefficient_jet_ae (N := fun y => N y - N' y) (hN := hD) (hp := hpD) (hb := hbD) U,
    mulCoefficient_jet_ae (N := N') (hN := hN') (hp := hp') (hb := hb') U,
    jet_add_ae (U.mulCoefficient (fun y => N y - N' y) hD hpD hbD)
      (U.mulCoefficient N' hN' hp' hb')] with x h1 h2 h3 h4 a
  rw [h4 a, h1 a, h2 a, h3 a]
  exact multiplicationRawJet_sub N N' hN hN' _ a x

/-- **(A)** The Lipschitz bound of coefficient multiplication in its coefficient. -/
theorem mulLip : MulLipStatement := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ K N N' hN hN' hp hp' A A' hb hb' Δ hΔ
  have hD : ContDiff ℝ (K : ℕ) (fun y => N y - N' y) := hN.sub hN'
  have hpD : AVenhance.IsZ2Periodic (fun y => N y - N' y) := fun n x => by
    change N (x + AVenhance.latticeShift n) - N' (x + AVenhance.latticeShift n) = N x - N' x
    rw [hp n x, hp' n x]
  rw [torusMulCLM_sub N N' hN hN' hp hp' hb hb' hD hpD hΔ]
  exact norm_torusMulCLM_le

end Mul

end AVRegularity.EntryTerminal.CovComm
end
end

section
/-! **Uniform continuity in time of the spatial derivative arrays** (statement (B)).

A function `G : ℝ → Vec 2 → Vec 2` that is `C^∞` jointly in `(s, x)` and `ℤ²`-periodic in `x` has
spatial derivatives `∂ₓⁿ G (s, x)` that are jointly continuous (the slice derivative is the
joint derivative composed with the inclusion of the space factor), periodic in `x`, hence
determined on the compact unit cell, where the tube lemma gives the uniform convergence
`sup_x ‖∂ₓⁿ G (s, x) - ∂ₓⁿ G (s₀, x)‖ → 0` as `s → s₀` (`streamArrayCont`).

Special cases:
- `G` independent of `s`: the difference vanishes.
- `n = 0`: this is the uniform continuity in time of `G` itself. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.EntryTerminal.CovComm

/-- The spatial slice derivative is the joint derivative composed with the space inclusion. -/
theorem iteratedFDeriv_slice (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ)
    (s : ℝ) (x : Vec 2) :
    iteratedFDeriv ℝ n (fun y => F (s, y)) x =
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (Vec 2))) (iteratedFDeriv ℝ n F (s, x)) := by
  have h1 : (fun y => F (s, y)) =
      (fun z => F ((s, (0 : Vec 2)) + z)) ∘ (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) := by
    funext y
    simp
  have h2 : ContDiff ℝ (n : WithTop ℕ∞) (fun z => F ((s, (0 : Vec 2)) + z)) :=
    (hF.of_le (by exact_mod_cast le_top)).comp (contDiff_const.add contDiff_id)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 x le_rfl,
    iteratedFDeriv_comp_add_left]
  simp

/-- Spatial derivatives of a periodic function are periodic. -/
theorem iteratedFDeriv_periodic (f : Vec 2 → Vec 2) (hp : AVenhance.IsZ2Periodic f) (n : ℕ)
    (m : Fin 2 → ℤ) (x : Vec 2) :
    iteratedFDeriv ℝ n f (x + AVenhance.latticeShift m) = iteratedFDeriv ℝ n f x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext z
  exact hp m z

/-- Every point is a lattice translate of a point of the unit cell. -/
theorem exists_cell_shift (x : Vec 2) :
    ∃ y ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1), ∃ m : Fin 2 → ℤ,
      x = y + AVenhance.latticeShift m := by
  refine ⟨fun i => Int.fract (x i), ?_, fun i => ⌊x i⌋, ?_⟩
  · intro i _
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · funext i
    exact (Int.fract_add_floor (x i)).symm

/-- **(B)** -/
theorem streamArrayCont : StreamArrayContStatement := by
  intro G hG hper n s₀ ε hε
  set F : ℝ × Vec 2 → Vec 2 := fun q => G q.1 q.2 with hFdef
  have hH : Continuous (fun q : ℝ × Vec 2 => iteratedFDeriv ℝ n (G q.1) q.2) := by
    have e : (fun q : ℝ × Vec 2 => iteratedFDeriv ℝ n (G q.1) q.2) = fun q =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (Vec 2))) (iteratedFDeriv ℝ n F q) := by
      funext q
      exact iteratedFDeriv_slice F hG n q.1 q.2
    rw [e]
    exact (ContinuousLinearMap.continuous _).comp
      (hG.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hg : Continuous (fun q : ℝ × Vec 2 =>
      ‖iteratedFDeriv ℝ n (G q.1) q.2 - iteratedFDeriv ℝ n (G s₀) q.2‖) := by
    refine Continuous.norm (hH.sub ?_)
    exact hH.comp (continuous_const.prodMk continuous_snd)
  set cell : Set (Vec 2) := Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) with hcell
  have hcc : IsCompact cell := isCompact_univ_pi fun _ => isCompact_Icc
  have hopen : IsOpen {q : ℝ × Vec 2 |
      ‖iteratedFDeriv ℝ n (G q.1) q.2 - iteratedFDeriv ℝ n (G s₀) q.2‖ < ε} :=
    isOpen_lt hg continuous_const
  obtain ⟨u, v, hu, hv, hs, hc, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := s₀))
    hcc hopen (by
      rintro ⟨s, y⟩ ⟨hs1, hy⟩
      simp only [Set.mem_singleton_iff] at hs1
      subst hs1
      simpa using hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hu s₀ (hs rfl)
  refine ⟨δ, hδ, fun s hsd x => ?_⟩
  obtain ⟨y, hy, m, rfl⟩ := exists_cell_shift x
  rw [iteratedFDeriv_periodic (G s) (hper s) n m y, iteratedFDeriv_periodic (G s₀) (hper s₀) n m y]
  have hsu : s ∈ u := hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hsd)
  exact (huv (Set.mk_mem_prod hsu (hc hy))).le

end AVRegularity.EntryTerminal.CovComm
end
end
end
