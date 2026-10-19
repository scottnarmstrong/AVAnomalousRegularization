-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.OldNegative
public import AVRegularity.CycleWords.Seam.B1NegFullField
import AVRegularity.CycleWords.MixedWords.Discard.WeakContStatements
import AVRegularity.CycleWords.Seam.S3bRoughCore
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleWords.MixedWords.Discard.MarksBand
import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage

@[expose] public noncomputable section

section
namespace AVRegularity.CycleWords.Seam

/-! # The Gaussian negative bound and the low-pass moment bound

`seamGaussianNeg : SeamGaussianNegStatement` from the assemblies
(`seamGaussianNeg_of_key`, `fibreKey_of_parts`) and the three proved parts:
`seamLowPassMoment`, `lowPassFibre`, `transformBound`; with the assembly
`seamFutureKernelClausesAssembly`, clauses (1) and (2) of the future kernel statement
(`SeamFutureKernelClausesStatement`). -/

universe u v

/-- **The Gaussian negative bound of the seam.** -/
theorem seamGaussianNeg : SeamGaussianNegStatement.{u, v} :=
  seamGaussianNeg_of_key (fibreKey_of_parts seamLowPassMoment lowPassFibre
    transformBound)

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The quiet margin fibre bound (`QuietMarginFibreStatement`), assembled

`b1_quietMarginFibre_of_parts`: the quiet margin fibre bound from the full field with negative input from any start
(`B1NegFullFieldStatement`) and the quiet entrance quiet margin (`B1QuietMarginStatement`), split on the
length `a'` of the quiet entrance, with `c = ρ/2`, `ρ = (π/8)²/2`:

* `a' < 2` or `b − a < 3` (then `a' < 3`): the full field from `a` in `H^{-k}`, and
  `1 ≤ e^{3ρ} e^{−ρa'}`.
* otherwise: `a₁ = a + min(a', b − a − 1)` (quiet margin of length `≥ 2`, `a₁ + 1 ≤ b`). The quiet margin gives
  the `L²` norms of all stages at `a₁` by `C (1 + (a₁ − a))^Q (e^{−ρ(a₁ − a)} N_k + L)`, the full
  field from `a₁` in `L²` (order `0`) gives the terminal band, and `a₁ − a ≥ a' − 1`.

`b1_quietMarginFibre : QuietMarginFibreStatement`: assembled from `CellAdjointKernelHsStatement`,
`StageSourceHsStatement`, the band bound, the family forms of `CellForcedHsFamilyStatement` and
`CellNegativeSmoothingFamilyStatement`, and `QuietModeStatement`. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- The reserve is monotone in the order. -/
theorem b1_reserve_mono {Nw : ℕ} (Kf k m : ℕ) (d Ks : Fin Nw → ℕ) :
    wordReserveJstar (wordReserveKstar (Kf + 0) (wordReserveN m Ks) d) d ≤
      wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d := by
  unfold wordReserveJstar wordReserveKstar
  omega

/-- Constants and exponents are monotone. -/
theorem b1_const_le {C C₁ P T : ℝ} {Q Q₁ : ℕ} (hC₁ : 0 ≤ C₁) (hP : 1 ≤ P) (hT : 1 ≤ T)
    (hQ : Q₁ ≤ Q) (hC : C₁ ≤ C) : C₁ * P ^ Q₁ * T ^ Q₁ ≤ C * P ^ Q * T ^ Q := by
  have hP0 : 0 ≤ P := by linarith
  have hT0 : 0 ≤ T := by linarith
  exact mul_le_mul (mul_le_mul hC (pow_le_pow_right₀ hP hQ) (by positivity) (hC₁.trans hC))
    (pow_le_pow_right₀ hT hQ) (by positivity) (by have := hC₁.trans hC; positivity)

/-- The constant of the short quiet margins. -/
theorem b1_caseA_le {C C₁ e E P T : ℝ} {Q Q₁ : ℕ} (hC₁ : 0 ≤ C₁) (he0 : 0 ≤ e) (hE : 0 ≤ E)
    (he : 1 ≤ e ^ 2 * E) (hP : 1 ≤ P) (hT : 1 ≤ T) (hQ : Q₁ ≤ Q) (hC : C₁ * e ≤ C) :
    (C₁ * P ^ Q₁ * T ^ Q₁) ^ 2 ≤ (C * P ^ Q * T ^ Q) ^ 2 * E := by
  have hX : 0 ≤ C₁ * P ^ Q₁ * T ^ Q₁ := by
    have : 0 ≤ P := by linarith
    have : 0 ≤ T := by linarith
    positivity
  have h1 := b1_const_le (mul_nonneg hC₁ he0) hP hT hQ hC
  calc (C₁ * P ^ Q₁ * T ^ Q₁) ^ 2 ≤ (C₁ * P ^ Q₁ * T ^ Q₁) ^ 2 * (e ^ 2 * E) :=
        le_mul_of_one_le_right (sq_nonneg _) he
    _ = (C₁ * e * P ^ Q₁ * T ^ Q₁) ^ 2 * E := by ring
    _ ≤ (C * P ^ Q * T ^ Q) ^ 2 * E :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) hE

/-- The constant of the long quiet margins. -/
theorem b1_caseB_le {C C₂ C₃ e P T U : ℝ} {Q Q₂ Q₃ : ℕ} (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (he : 0 ≤ e) (hP : 1 ≤ P) (hT : 1 ≤ T) (hU0 : 0 ≤ U) (hU : U ≤ T) (hQ : Q₃ + Q₂ ≤ Q)
    (hC : C₃ * Real.sqrt C₂ * e ≤ C) :
    (C₃ * P ^ Q₃ * T ^ Q₃) ^ 2 * (C₂ * U ^ Q₂) * e ^ 2 ≤ (C * P ^ Q * T ^ Q) ^ 2 := by
  have hP0 : 0 ≤ P := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTQ : 1 ≤ T ^ Q₂ := one_le_pow₀ hT
  have hUT : U ^ Q₂ ≤ (T ^ Q₂) ^ 2 :=
    (pow_le_pow_left₀ hU0 hU Q₂).trans (le_self_pow₀ hTQ two_ne_zero)
  have h0 : 0 ≤ C₃ * Real.sqrt C₂ * e := by positivity
  have hPQ : P ^ Q₃ ≤ P ^ (Q₃ + Q₂) := pow_le_pow_right₀ hP (Nat.le_add_right _ _)
  have h1 : C₃ * Real.sqrt C₂ * e * P ^ Q₃ * T ^ (Q₃ + Q₂) ≤ C * P ^ Q * T ^ Q :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQ h0) (by positivity)).trans
      (b1_const_le h0 hP hT hQ hC)
  calc (C₃ * P ^ Q₃ * T ^ Q₃) ^ 2 * (C₂ * U ^ Q₂) * e ^ 2
      = (C₃ * Real.sqrt C₂ * e * P ^ Q₃ * T ^ Q₃) ^ 2 * U ^ Q₂ := by
        rw [mul_pow (C₃ * Real.sqrt C₂ * e * P ^ Q₃) _, mul_pow (C₃ * Real.sqrt C₂ * e) _,
          mul_pow (C₃ * Real.sqrt C₂) e, mul_pow C₃ (Real.sqrt C₂), Real.sq_sqrt hC₂]
        ring
    _ ≤ (C₃ * Real.sqrt C₂ * e * P ^ Q₃ * T ^ Q₃) ^ 2 * (T ^ Q₂) ^ 2 :=
        mul_le_mul_of_nonneg_left hUT (sq_nonneg _)
    _ = (C₃ * Real.sqrt C₂ * e * P ^ Q₃ * T ^ (Q₃ + Q₂)) ^ 2 := by
        rw [pow_add]
        ring
    _ ≤ (C * P ^ Q * T ^ Q) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2

/-- The decay of the long quiet margins: `e^{−ρ(a₁ − a)} ≤ e^{ρ} e^{−ρa'}` when `a₁ − a ≥ a' − 1`. -/
theorem b1_decay_le {ρ a' D : ℝ} (hρ : 0 ≤ ρ) (hD : a' - 1 ≤ D) :
    Real.exp (-ρ * D) ≤ Real.exp (ρ / 2) ^ 2 * Real.exp (-2 * (ρ / 2) * a') := by
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hD hρ])

/-- **The quiet margin fibre bound from its parts.** -/
theorem b1_quietMarginFibre_of_parts (hFF : B1NegFullFieldStatement.{u, v})
    (hCo : B1QuietMarginStatement.{u, v}) : QuietMarginFibreStatement.{u, v} := by
  intro K
  obtain ⟨gF, hgF, hFK⟩ := hFF K
  obtain ⟨gC, hgC, hCK⟩ := hCo K
  refine ⟨min gF gC, lt_min hgF hgC, ?_⟩
  intro Nw D m Kf k d Ks pos
  obtain ⟨C₁, Q₁, hC₁, hI⟩ := hFK Nw D m Kf k d Ks pos
  obtain ⟨C₃, Q₃, hC₃, hIII⟩ := hFK Nw D m Kf 0 d Ks pos
  obtain ⟨C₂, Q₂, hC₂, hII⟩ := hCK Nw D m Kf k d Ks pos
  set ρ : ℝ := (Real.pi / 8) ^ 2 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  refine ⟨C₁ * Real.exp (3 * ρ / 2) + C₃ * Real.sqrt C₂ * Real.exp (ρ / 2) + 1, ρ / 2,
    Q₁ + Q₃ + Q₂, by positivity, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hab hθ a' ha' ha'b hqu hv0
  have hF := min_le_left gF gC
  have hG := min_le_right gF gC
  have hP := one_le_peFactor F.η
  have hT : 1 ≤ 1 + (F.b - F.a) := by linarith
  set E : ℝ := Real.exp (-2 * (ρ / 2) * a') with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  by_cases hcase : a' < 2 ∨ F.b - F.a < 3
  · -- a short quiet margin: the full field from `a`
    have ha3 : a' ≤ 3 := by rcases hcase with h | h <;> linarith
    have h1 : stageTerminalBandSq F m Ks Kf 0 θ ≤
        ENNReal.ofReal ((C₁ * peFactor F.η ^ Q₁ * (1 + (F.b - F.a)) ^ Q₁) ^ 2) *
          stageDatumNegSq F m Ks k θ :=
      hI (F.mono hF) θ hlet hJ hθ F.a le_rfl hab
    have he : 1 ≤ Real.exp (3 * ρ / 2) ^ 2 * E := by
      rw [hEdef, sq, ← Real.exp_add, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_le_mul_of_nonneg_left ha3 hρ0.le])
    have hreal := b1_caseA_le (C := C₁ * Real.exp (3 * ρ / 2) +
      C₃ * Real.sqrt C₂ * Real.exp (ρ / 2) + 1) (Q := Q₁ + Q₃ + Q₂) (Q₁ := Q₁)
      (e := Real.exp (3 * ρ / 2)) hC₁.le
      (Real.exp_pos _).le hE0 he hP hT (by omega)
      (by have : 0 ≤ C₃ * Real.sqrt C₂ * Real.exp (ρ / 2) := by positivity
          linarith)
    refine h1.trans ?_
    calc ENNReal.ofReal ((C₁ * peFactor F.η ^ Q₁ * (1 + (F.b - F.a)) ^ Q₁) ^ 2) *
          stageDatumNegSq F m Ks k θ
        ≤ ENNReal.ofReal (((C₁ * Real.exp (3 * ρ / 2) + C₃ * Real.sqrt C₂ * Real.exp (ρ / 2) +
            1) * peFactor F.η ^ (Q₁ + Q₃ + Q₂) * (1 + (F.b - F.a)) ^ (Q₁ + Q₃ + Q₂)) ^ 2 * E) *
          stageDatumNegSq F m Ks k θ := by gcongr
      _ = ENNReal.ofReal (((C₁ * Real.exp (3 * ρ / 2) + C₃ * Real.sqrt C₂ * Real.exp (ρ / 2) +
            1) * peFactor F.η ^ (Q₁ + Q₃ + Q₂) * (1 + (F.b - F.a)) ^ (Q₁ + Q₃ + Q₂)) ^ 2) *
          (ENNReal.ofReal E * stageDatumNegSq F m Ks k θ) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
      _ ≤ _ := by gcongr; exact le_self_add
  · -- a long quiet margin: the quiet margin to `a₁`, then the full field from `a₁` in `L²`
    have ha2 : 2 ≤ a' := by by_contra h'; exact hcase (Or.inl (not_le.1 h'))
    have hba : 3 ≤ F.b - F.a := by by_contra h'; exact hcase (Or.inr (not_le.1 h'))
    set Dq : ℝ := min a' (F.b - F.a - 1) with hDqdef
    have hDq2 : 2 ≤ Dq := le_min ha2 (by linarith)
    have hDqa : Dq ≤ a' := min_le_left _ _
    have hDqb : Dq ≤ F.b - F.a - 1 := min_le_right _ _
    have hDq1 : a' - 1 ≤ Dq := by
      rcases le_total a' (F.b - F.a - 1) with h' | h'
      · rw [hDqdef, min_eq_left h']; linarith
      · rw [hDqdef, min_eq_right h']; linarith
    have hqu' : Icc F.a (F.a + Dq) ⊆ F.reg.quiet :=
      (Icc_subset_Icc le_rfl (by linarith)).trans hqu
    have hv0' : ∀ t ∈ Icc F.a (F.a + Dq), ∀ z, F.v t z = 0 := fun t ht =>
      hv0 t ⟨ht.1, by linarith [ht.2]⟩
    have h3 : stageTerminalBandSq F m Ks Kf 0 θ ≤
        ENNReal.ofReal ((C₃ * peFactor F.η ^ Q₃ * (1 + (F.b - F.a)) ^ Q₃) ^ 2) *
          ∑ i : B1WIndex ι h Nw m Ks, cellNegSq 0 θ (stageScaled F θ i (F.a + Dq)) :=
      hIII (F.mono hF) θ hlet ((b1_reserve_mono Kf k m d Ks).trans hJ) hθ (F.a + Dq)
        (show F.a ≤ F.a + Dq by linarith) (show F.a + Dq + 1 ≤ F.b by linarith)
    have h2 : ∑ i : B1WIndex ι h Nw m Ks, cellNegSq 0 θ (stageScaled F θ i (F.a + Dq)) ≤
        ENNReal.ofReal (C₂ * (1 + (F.a + Dq - F.a)) ^ Q₂) *
          (ENNReal.ofReal (Real.exp (-((Real.pi / 8) ^ 2 / 2) * (F.a + Dq - F.a))) *
              stageDatumNegSq F m Ks k θ +
            stageDatumLowSq F m Ks (Real.pi / 8) θ) :=
      hII (F.mono hG) θ hlet hJ hθ (F.a + Dq) (show F.a + 1 ≤ F.a + Dq by linarith)
        (show F.a + Dq ≤ F.b by linarith) hqu' hv0'
    have hsimp : F.a + Dq - F.a = Dq := by ring
    rw [hsimp] at h2
    have hdec : Real.exp (-((Real.pi / 8) ^ 2 / 2) * Dq) ≤ Real.exp (ρ / 2) ^ 2 * E :=
      b1_decay_le hρ0.le hDq1
    have he1 : 1 ≤ Real.exp (ρ / 2) ^ 2 := one_le_pow₀ (Real.one_le_exp (by positivity))
    have hmix : ENNReal.ofReal (Real.exp (-((Real.pi / 8) ^ 2 / 2) * Dq)) *
          stageDatumNegSq F m Ks k θ + stageDatumLowSq F m Ks (Real.pi / 8) θ ≤
        ENNReal.ofReal (Real.exp (ρ / 2) ^ 2) *
          (ENNReal.ofReal E * stageDatumNegSq F m Ks k θ +
            stageDatumLowSq F m Ks (Real.pi / 8) θ) := by
      rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 he1)
    have hreal := b1_caseB_le (C := C₁ * Real.exp (3 * ρ / 2) +
      C₃ * Real.sqrt C₂ * Real.exp (ρ / 2) + 1) (Q := Q₁ + Q₃ + Q₂) (P := peFactor F.η)
      (T := 1 + (F.b - F.a)) (U := 1 + Dq) (Q₂ := Q₂) (Q₃ := Q₃) (e := Real.exp (ρ / 2))
      hC₂.le hC₃.le (Real.exp_pos _).le hP hT
      (by linarith) (by linarith) (by omega)
      (by have : 0 ≤ C₁ * Real.exp (3 * ρ / 2) := by positivity
          linarith)
    calc stageTerminalBandSq F m Ks Kf 0 θ
        ≤ ENNReal.ofReal ((C₃ * peFactor F.η ^ Q₃ * (1 + (F.b - F.a)) ^ Q₃) ^ 2) *
          (ENNReal.ofReal (C₂ * (1 + Dq) ^ Q₂) *
            (ENNReal.ofReal (Real.exp (ρ / 2) ^ 2) *
              (ENNReal.ofReal E * stageDatumNegSq F m Ks k θ +
                stageDatumLowSq F m Ks (Real.pi / 8) θ))) :=
          h3.trans (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl hmix)))
      _ = ENNReal.ofReal ((C₃ * peFactor F.η ^ Q₃ * (1 + (F.b - F.a)) ^ Q₃) ^ 2 *
            (C₂ * (1 + Dq) ^ Q₂) * Real.exp (ρ / 2) ^ 2) *
          (ENNReal.ofReal E * stageDatumNegSq F m Ks k θ +
            stageDatumLowSq F m Ks (Real.pi / 8) θ) := by
          have h0 : 0 ≤ 1 + Dq := by linarith
          have hA2 : (0 : ℝ) ≤ (C₃ * peFactor F.η ^ Q₃ * (1 + (F.b - F.a)) ^ Q₃) ^ 2 :=
            sq_nonneg _
          have hB2 : (0 : ℝ) ≤ C₂ * (1 + Dq) ^ Q₂ := by positivity
          rw [ENNReal.ofReal_mul (mul_nonneg hA2 hB2), ENNReal.ofReal_mul hA2]
          ring
      _ ≤ _ := by gcongr

/-- **The quiet margin fibre bound.** -/
theorem b1_quietMarginFibre : QuietMarginFibreStatement.{u, v} :=
  b1_quietMarginFibre_of_parts
    (b1_negFullField_of_parts torusHkBandBound cellForcedHsFamily.{u}
      cellNegativeSmoothingFamily.{u}
      (b1_plainStageNeg_of_adjointKernel cellAdjointKernelHs) stageSourceHs')
    b1_quiet_margin

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The fast remainder on rough data

`s3b_rough_core`: the weighted output norm of `Z(f) − K₊f`, truncated at the orders `K_out x`, for
a chain from a datum with finite moment norm, from the bound on compactly supported data,
the full-field bound on compact data and weak continuity. The route is in the module
`CycleWords.Seam.S3bRoughCore`; the
steps are separate declarations: two compact chains (`s3b_rough_diff`), Cauchy
(`s3b_rough_cauchy`), the pairing with a test at the orders `K_out x` (`s3b_rough_pair`), Fatou
and the weighted norm (`s3b_rough_final`). -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

section Rough

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw Kmax pout : ℕ} {Ks : Fin Nw → ℕ} {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D}
  {S t₀ ϖ δ r : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
  {κc : Fin (Nw + 1) → ι → ℕ}

/-- **Two compact chains**: the difference of their endpoints, at order `K_max`, by the full-field
bound on the difference chain. -/
theorem s3b_rough_diff (hD : 2 ≤ D) (hκc : IsWordSlots letters κc)
    (hκcl : ∀ x, Kmax ≤ κc (Fin.last Nw) x) {A : ℝ≥0∞}
    (hFF : ∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        A * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    {φ₁ φ₂ : ∀ x, Vec 2 → h x} (hφ₁ : IsCompactFamily φ₁) (hφ₂ : IsCompactFamily φ₂)
    {f₁ f₂ : ∀ x, PlaneHk Set.univ (κc 0 x) (h x)}
    {u₁ u₂ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x)}
    {w₁ w₂ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)}
    (hf₁ : ∀ x, planeValue (f₁ x) =ᵐ[volume] φ₁ x) (hf₂ : ∀ x, planeValue (f₂ x) =ᵐ[volume] φ₂ x)
    (hc₁ : IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v f₁ (fun _ _ _ => 0) u₁ w₁)
    (hc₂ : IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v f₂ (fun _ _ _ => 0) u₂ w₂) :
    jetOutputNorm π pout Kmax ϖ r (fun x a wd z =>
        planeJetOrder (truncatePlaneHk (hκcl x) (u₁ (Fin.last Nw) x (t₀ + S)) -
          truncatePlaneHk (hκcl x) (u₂ (Fin.last Nw) x (t₀ + S))) a wd z) ≤
      A * momentNorm π (wordReserveN pout Ks) ϖ (fun x z => φ₁ x z - φ₂ x z) := by
  have hch := isPlaneChain_trunc_sub hD G letters X₀ δ t₀ (t₀ + S) v κc κc
    (fun _ _ => le_rfl) hκc hκc f₁ u₁ w₁ f₂ u₂ w₂ hc₁ hc₂
  have hval : ∀ x, planeValue ((1 : ℝ) • truncatePlaneHk (le_refl _) (f₁ x) + (-1 : ℝ) • f₂ x)
      =ᵐ[volume] fun z => φ₁ x z - φ₂ x z := by
    intro x
    filter_upwards [planeJetOrder_trunc_sub_ae (le_refl _) (f₁ x) (f₂ x) (Nat.zero_le _)
      (fun i => i.elim0), hf₁ x, hf₂ x] with z h1 h2 h3
    rw [planeValue, h1]
    change planeValue (f₁ x) z - planeValue (f₂ x) z = _
    rw [h2, h3]
  have hcd : IsCompactDatum (fun x => (1 : ℝ) • truncatePlaneHk (le_refl _) (f₁ x) +
      (-1 : ℝ) • f₂ x) := fun x =>
    ⟨fun z => φ₁ x z - φ₂ x z, (hφ₁ x).1.sub (hφ₂ x).1, (hφ₁ x).2.sub (hφ₂ x).2, hval x⟩
  have hb := hFF _ _ _ hcd hch
  rw [momentNorm_congr_ae' _ _ _ hval] at hb
  refine le_trans (le_of_eq ?_) hb
  refine jetOutputNorm_congr_ae π pout Kmax ϖ r fun x a wd ha => ?_
  have haK : a ≤ κc (Fin.last Nw) x := ha.trans (hκcl x)
  filter_upwards [planeJetOrder_sub_ae ha (truncatePlaneHk (hκcl x) (u₁ (Fin.last Nw) x (t₀ + S)))
      (truncatePlaneHk (hκcl x) (u₂ (Fin.last Nw) x (t₀ + S))) wd,
    planeJetOrder_trunc_sub_ae (le_refl _) (u₁ (Fin.last Nw) x (t₀ + S))
      (u₂ (Fin.last Nw) x (t₀ + S)) haK wd] with z h1 h2
  rw [h1, h2, planeJetOrder_truncate (hκcl x) ha, planeJetOrder_truncate (hκcl x) ha]

/-- **Cauchy**: the endpoints of the compact chains, at order `K_max`. -/
theorem s3b_rough_cauchy (hD : 2 ≤ D) (hκc : IsWordSlots letters κc)
    (hκcl : ∀ x, Kmax ≤ κc (Fin.last Nw) x) (hπ : ∀ x, 0 < π x) (hr : 0 < r) {A : ℝ≥0∞}
    (hA : A ≠ ⊤)
    (hFF : ∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        A * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    (F : ∀ x, Vec 2 → h x) {φs : ℕ → ∀ x, Vec 2 → h x} (hφs : ∀ j, IsCompactFamily (φs j))
    {fk : ℕ → ∀ x, PlaneHk Set.univ (κc 0 x) (h x)}
    {uk : ℕ → ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x)}
    {wk : ℕ → ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)}
    (hfk : ∀ j x, planeValue (fk j x) =ᵐ[volume] φs j x)
    (huk : ∀ j, IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v (fk j)
      (fun _ _ _ => 0) (uk j) (wk j))
    (he : Tendsto (fun j => momentNorm π (wordReserveN pout Ks) ϖ
      (fun x z => F x z - φs j x z)) atTop (𝓝 0)) (x : ι) :
    CauchySeq fun j => truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S)) := by
  set e : ℕ → ℝ≥0∞ := fun j => momentNorm π (wordReserveN pout Ks) ϖ
    (fun x z => F x z - φs j x z) with hedef
  have hmn : ∀ j l, momentNorm π (wordReserveN pout Ks) ϖ (fun x z => φs j x z - φs l x z) ≤
      e j + e l := by
    intro j l
    have hsplit : (fun x z => φs j x z - φs l x z) = fun x z =>
        (F x z - φs l x z) + (φs j x z - F x z) := by
      funext x z
      abel
    rw [hsplit, add_comm (e j)]
    refine (momentNorm_add_le π _ ϖ _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    exact momentNorm_sub_comm π _ ϖ (φs j) F
  refine rff_cauchySeq (fun j => truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S)))
    (fun i => ENNReal.ofReal (i.1.val.factorial * Real.sqrt (π x) / r ^ i.1.val) * A)
    (fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) e he fun j l i => ?_
  have hi : i.1.val ≤ Kmax := Nat.lt_succ_iff.1 i.1.isLt
  refine (rff_eLpNorm_jet_le π pout Kmax ϖ r hr
    (fun x a wd z => planeJetOrder (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S)) -
      truncatePlaneHk (hκcl x) (uk l (Fin.last Nw) x (t₀ + S))) a wd z) x (hπ x) hi i.2
    (planeJetOrder_aestronglyMeasurable _ _ _)).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_right ((s3b_rough_diff hD hκc hκcl hFF (hφs j) (hφs l) (hfk j) (hfk l)
    (huk j) (huk l)).trans (mul_le_mul_right (hmn j l) _)) _

/-- **The pairing with a test** at the orders `K_out x`: weak continuity on the difference of the
rough chain and the compact chains. -/
theorem s3b_rough_pair (hD : 2 ≤ D) (hκc : IsWordSlots letters κc)
    (hκcl : ∀ x, Kmax ≤ κc (Fin.last Nw) x) (hπ : ∀ x, 0 < π x)
    {κF κm : Fin (Nw + 1) → ι → ℕ} (hκF : IsWordSlots letters κF)
    (hκm : IsWordSlots letters κm) (hmF : ∀ j x, κm j x ≤ κF j x)
    (hmc : ∀ j x, κm j x ≤ κc j x) {Kout : ι → ℕ}
    (hKoutF : ∀ x, Kout x ≤ κF (Fin.last Nw) x) (hKoutM : ∀ x, Kout x ≤ Kmax)
    (hWb : ∀ Φ : ∀ x, Vec 2 → h x,
      (∀ x, ContDiff ℝ (⊤ : ℕ∞) (Φ x) ∧ HasCompactSupport (Φ x)) →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : ∀ x, PlaneHk Set.univ (κm 0 x) (h x))
        (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κm j x) (h x))
        (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κm j x + 1) (h x)),
        momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (f' x)) < ⊤ →
        IsPlaneChain (wordChainData G letters X₀ δ) κm t₀ (t₀ + S) v f' (fun _ _ _ => 0) u' w' →
        ENNReal.ofReal |∑ x, (π x)⁻¹ *
            ∫ z, inner ℝ (planeValue (u' (Fin.last Nw) x (t₀ + S)) z) (Φ x z)| ≤
          ENNReal.ofReal C * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (f' x)))
    {fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x)}
    {uF : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x)}
    {wF : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x)}
    (hch : IsPlaneChain (wordChainData G letters X₀ δ) κF t₀ (t₀ + S) v fF (fun _ _ _ => 0) uF wF)
    {φs : ℕ → ∀ x, Vec 2 → h x}
    {fk : ℕ → ∀ x, PlaneHk Set.univ (κc 0 x) (h x)}
    {uk : ℕ → ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x)}
    {wk : ℕ → ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)}
    (hfk : ∀ j x, planeValue (fk j x) =ᵐ[volume] φs j x)
    (huk : ∀ j, IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v (fk j)
      (fun _ _ _ => 0) (uk j) (wk j))
    (he : Tendsto (fun j => momentNorm π (wordReserveN pout Ks) ϖ
      (fun x z => planeValue (fF x) z - φs j x z)) atTop (𝓝 0))
    (x : ι) (Φ : Vec 2 → h x) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    Tendsto (fun j => ∫ z, inner ℝ (planeValue (truncatePlaneHk (hKoutM x)
      (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))) -
        truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S))) z) (Φ z)) atTop (𝓝 0) := by
  classical
  let Φ' : ∀ x', Vec 2 → h x' := Pi.single x Φ
  have hΦ' : ∀ x', ContDiff ℝ (⊤ : ℕ∞) (Φ' x') ∧ HasCompactSupport (Φ' x') := by
    intro x'
    by_cases hx : x' = x
    · subst hx
      simp only [Φ', Pi.single_eq_same]
      exact ⟨hΦ, hΦc⟩
    · simp only [Φ', Pi.single_eq_of_ne hx]
      exact ⟨contDiff_zero_fun, HasCompactSupport.zero⟩
  obtain ⟨CΦ, hCΦ, hWΦ⟩ := hWb Φ' hΦ'
  set e : ℕ → ℝ≥0∞ := fun j => momentNorm π (wordReserveN pout Ks) ϖ
    (fun x z => planeValue (fF x) z - φs j x z) with hedef
  have hsum : ∀ Q : ∀ x', Vec 2 → h x', ∑ x', (π x')⁻¹ * ∫ z, inner ℝ (Q x' z) (Φ' x' z) =
      (π x)⁻¹ * ∫ z, inner ℝ (Q x z) (Φ z) := by
    intro Q
    rw [Finset.sum_eq_single x]
    · simp only [Φ', Pi.single_eq_same]
    · intro x' _ hx
      simp only [Φ', Pi.single_eq_of_ne hx, Pi.zero_apply, inner_zero_right, integral_zero,
        mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have hk : ∀ j, e j < ⊤ → |(π x)⁻¹ * ∫ z, inner ℝ (planeValue (truncatePlaneHk (hKoutM x)
      (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))) -
        truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S))) z) (Φ z)| ≤
      CΦ * (e j).toReal := by
    intro j hj
    have hb := s3b_pair_le hD hκF hκc hκm hmF hmc hch (huk j) (hfk j) hj Φ' hWΦ
    rw [hsum (fun x' z => planeValue (uF (Fin.last Nw) x' (t₀ + S)) z -
      planeValue (uk j (Fin.last Nw) x' (t₀ + S)) z)] at hb
    have hint : ∫ z, inner ℝ (planeValue (truncatePlaneHk (hKoutM x)
        (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))) -
          truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S))) z) (Φ z) =
        -∫ z, inner ℝ (planeValue (uF (Fin.last Nw) x (t₀ + S)) z -
          planeValue (uk j (Fin.last Nw) x (t₀ + S)) z) (Φ z) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [planeJetOrder_sub_ae (Nat.zero_le _) (truncatePlaneHk (hKoutM x)
          (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))))
          (truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S))) (fun i => i.elim0)]
        with z h1
      change inner ℝ (planeJetOrder (truncatePlaneHk (hKoutM x)
        (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))) -
          truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S))) 0 (fun i => i.elim0) z)
        (Φ z) = _
      rw [h1]
      change inner ℝ (planeValue (truncatePlaneHk (hKoutM x)
        (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S)))) z -
        planeValue (truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S))) z) (Φ z) = _
      rw [planeValue_truncate, planeValue_truncate, planeValue_truncate, ← inner_neg_left,
        neg_sub]
    rw [hint, mul_neg, abs_neg]
    have hne : ENNReal.ofReal CΦ * e j ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hj.ne
    rw [ENNReal.ofReal_le_iff_le_toReal hne, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCΦ] at hb
    exact hb
  have he0 : Tendsto (fun j => CΦ * (e j).toReal) atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he).const_mul CΦ
  have habs := squeeze_zero' (Filter.Eventually.of_forall fun j => abs_nonneg _)
    (by
      filter_upwards [he.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with j hj
      exact hk j hj) he0
  have h1 := ((tendsto_zero_iff_abs_tendsto_zero _).2 habs).const_mul (π x)
  simp only [mul_zero, ← mul_assoc, mul_inv_cancel₀ (hπ x).ne', one_mul] at h1
  exact h1

/-- **Fatou and the weighted norm**: the weighted output norm of the limit, truncated at the orders
`K_out x` where its jets are those of the rough endpoint. -/
theorem s3b_rough_final (hr : 0 < r) (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hKs : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      ∀ x (M : ℕ), ContDiff ℝ M (Kp g x))
    (F : ∀ x, Vec 2 → h x) (hF2 : ∀ x, MemLp (F x) 2 volume) {φs : ℕ → ∀ x, Vec 2 → h x}
    (hφs2 : ∀ j x, MemLp (φs j x) 2 volume)
    (hKlim : ∀ x a (wd : DerivativeWord2 a) z, Tendsto
      (fun j => orderedDerivative wd (Kp (φs j) x) z) atTop (𝓝 (orderedDerivative wd (Kp F x) z)))
    (V : ℕ → ∀ x, PlaneHk Set.univ Kmax (h x)) (L : ∀ x, PlaneHk Set.univ Kmax (h x))
    (hL : ∀ x, Tendsto (fun j => V j x) atTop (𝓝 (L x))) {Kout : ι → ℕ}
    (J0 : ∀ x, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h x)
    (hJ0 : ∀ x a (wd : DerivativeWord2 a), a ≤ Kout x → planeJetOrder (L x) a wd = J0 x a wd)
    {B : ℕ → ℝ≥0∞} {B' : ℝ≥0∞} (hB : Tendsto B atTop (𝓝 B'))
    (hstep : ∀ j, jetOutputNorm π pout Kmax ϖ r (fun x a wd z =>
      planeJetOrder (V j x) a wd z - orderedDerivative wd (Kp (φs j) x) z) ≤ B j) :
    weightedJetNorm π (pout : ℝ) Kmax ϖ r (fun x a wd z => if a ≤ Kout x then
        J0 x a wd z - orderedDerivative wd (Kp F x) z else 0) ≤
      ENNReal.ofReal (3 ^ (pout + 1) * pout.factorial) * B' := by
  obtain ⟨ns, hns, hae⟩ := s3b_ae_subseq V L hL
  have hKjm : ∀ (g : ∀ x, Vec 2 → h x), (∀ x, MemLp (g x) 2 volume) →
      ∀ x a (wd : DerivativeWord2 a), AEStronglyMeasurable
        (fun z => orderedDerivative wd (Kp g x) z) volume :=
    fun g hg x a wd => (orderedDerivative_continuous wd (hKs g hg x a)).aestronglyMeasurable
  have hfat := rff_jetOutputNorm_le_liminf_ae π pout Kmax ϖ r
    (fun i x a wd z => planeJetOrder (V (ns i) x) a wd z -
      orderedDerivative wd (Kp (φs (ns i)) x) z)
    (fun x a wd z => planeJetOrder (L x) a wd z - orderedDerivative wd (Kp F x) z)
    (fun i x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub
      (hKjm _ (hφs2 (ns i)) x a wd))
    (fun x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub (hKjm F hF2 x a wd))
    (fun x a wd => by
      filter_upwards [hae x a wd] with z hz
      exact hz.sub ((hKlim x a wd z).comp hns.tendsto_atTop))
  have hLb : jetOutputNorm π pout Kmax ϖ r
      (fun x a wd z => planeJetOrder (L x) a wd z - orderedDerivative wd (Kp F x) z) ≤ B' :=
    hfat.trans (le_of_le_of_eq (liminf_le_liminf (Filter.Eventually.of_forall fun i =>
      hstep (ns i))) ((hB.comp hns.tendsto_atTop).liminf_eq))
  have hcongr : weightedJetNorm π (pout : ℝ) Kmax ϖ r (fun x a wd z => if a ≤ Kout x then
        J0 x a wd z - orderedDerivative wd (Kp F x) z else 0) =
      weightedJetNorm π (pout : ℝ) Kmax ϖ r (fun x a wd z => if a ≤ Kout x then
        planeJetOrder (L x) a wd z - orderedDerivative wd (Kp F x) z else 0) := by
    refine weightedJetNorm_congr_ae π _ Kmax ϖ r fun x a wd => ?_
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases ha : a ≤ Kout x
    · simp only [ha, ite_true, hJ0 x a wd ha]
    · simp only [ha, ite_false]
  rw [hcongr]
  exact (s3b_weightedJetNorm_le_jetOutputNorm π pout Kmax ϖ r hr.le Kout
    (fun x a wd z => planeJetOrder (L x) a wd z - orderedDerivative wd (Kp F x) z)
    (fun x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub (hKjm F hF2 x a wd))).trans
    (mul_le_mul_right hLb _)

/-- **The core**: the fast remainder on rough data. -/
theorem s3b_rough_core {k pin : ℕ} (hD : 2 ≤ D) (hπ : ∀ x, 0 < π x) (hr : 0 < r)
    (hnp : wordReserveN pout Ks ≤ pin)
    (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hKs : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      ∀ x (M : ℕ), ContDiff ℝ M (Kp g x))
    (hKc : ∀ g g' : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      (∀ x, MemLp (g' x) 2 volume) → (∀ x, g x =ᵐ[volume] g' x) → Kp g = Kp g')
    (hKlim : ∀ (F : ∀ x, Vec 2 → h x) (φs : ℕ → ∀ x, Vec 2 → h x),
      (∀ x, MemLp (F x) 2 volume) → (∀ j x, MemLp (φs j x) 2 volume) →
      Tendsto (fun j => momentNorm π pin ϖ (fun x z => F x z - φs j x z)) atTop (𝓝 0) →
      ∀ x a (wd : DerivativeWord2 a) z, Tendsto (fun j => orderedDerivative wd (Kp (φs j) x) z)
        atTop (𝓝 (orderedDerivative wd (Kp F x) z)))
    (hκc : IsWordSlots letters κc) (hκcl : ∀ x, Kmax ≤ κc (Fin.last Nw) x)
    (hEx : ∀ fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x), IsCompactDatum fk →
      ∃ (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
        (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk)
    {Bc A : ℝ≥0∞} (hBc : Bc ≠ ⊤) (hA : A ≠ ⊤) {C₁ : ℝ}
    (hComp : ∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (Kp (fun x' => planeValue (fk x')) x) z) ≤
        Bc * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (fk x)))
    (hFF : ∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        A * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    {κF κm : Fin (Nw + 1) → ι → ℕ} (hκF : IsWordSlots letters κF)
    (hκm : IsWordSlots letters κm) (hmF : ∀ j x, κm j x ≤ κF j x)
    (hmc : ∀ j x, κm j x ≤ κc j x) {Kout : ι → ℕ}
    (hKoutF : ∀ x, Kout x ≤ κF (Fin.last Nw) x) (hKoutM : ∀ x, Kout x ≤ Kmax)
    (hWb : ∀ Φ : ∀ x, Vec 2 → h x,
      (∀ x, ContDiff ℝ (⊤ : ℕ∞) (Φ x) ∧ HasCompactSupport (Φ x)) →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : ∀ x, PlaneHk Set.univ (κm 0 x) (h x))
        (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κm j x) (h x))
        (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κm j x + 1) (h x)),
        momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (f' x)) < ⊤ →
        IsPlaneChain (wordChainData G letters X₀ δ) κm t₀ (t₀ + S) v f' (fun _ _ _ => 0) u' w' →
        ENNReal.ofReal |∑ x, (π x)⁻¹ *
            ∫ z, inner ℝ (planeValue (u' (Fin.last Nw) x (t₀ + S)) z) (Φ x z)| ≤
          ENNReal.ofReal C * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (f' x)))
    (hP1 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (Gf x) volume) →
      negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ Gf)
    {fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x)}
    {uF : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x)}
    {wF : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x)}
    (hfin : momentNorm π pin ϖ (fun x => planeValue (fF x)) < ⊤)
    (hch : IsPlaneChain (wordChainData G letters X₀ δ) κF t₀ (t₀ + S) v fF (fun _ _ _ => 0) uF wF) :
    weightedJetNorm π (pout : ℝ) Kmax ϖ r
        (fun x a wd z => if a ≤ Kout x then planeJetOrder (uF (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z else 0) ≤
      ENNReal.ofReal (3 ^ (pout + 1) * pout.factorial) *
        (Bc * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
          (fun x => planeValue (fF x))) := by
  classical
  set F : ∀ x, Vec 2 → h x := fun x => planeValue (fF x) with hFdef
  have hFm : ∀ x, AEStronglyMeasurable (F x) volume :=
    fun x => planeJetOrder_aestronglyMeasurable (fF x) 0 _
  have hF2 : ∀ x, MemLp (F x) 2 volume := fun x => planeJetOrder_memLp (Nat.zero_le _) (fF x) _
  -- compact approximants and their chains
  obtain ⟨φs, hφs, hconv⟩ := compactDensity.{u, v}.2 F hFm
  have hconvP := hconv π pin ϖ hfin
  have he : Tendsto (fun j => momentNorm π (wordReserveN pout Ks) ϖ
      (fun x z => F x z - φs j x z)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconvP (fun j => zero_le)
      (fun j => momentNorm_mono hnp _ _ _)
  have hφs2 : ∀ j x, MemLp (φs j x) 2 volume :=
    fun j x => (hφs j x).1.continuous.memLp_of_hasCompactSupport (hφs j x).2
  have hφsm : ∀ j x, AEStronglyMeasurable (φs j x) volume :=
    fun j x => (hφs j x).1.continuous.aestronglyMeasurable
  have hlift : ∀ j x, ∃ fk : PlaneHk Set.univ (κc 0 x) (h x), planeValue fk =ᵐ[volume] φs j x :=
    fun j x => compactDensity.{u, v}.1 _ (φs j x) (hφs j x).1 (hφs j x).2
  choose fk hfk using hlift
  have hcdk : ∀ j, IsCompactDatum (fk j) :=
    fun j x => ⟨φs j x, (hφs j x).1, (hφs j x).2, hfk j x⟩
  choose uk wk huk using fun j => hEx (fk j) (hcdk j)
  -- the limit of the compact endpoints
  have hcauchy := fun x => s3b_rough_cauchy hD hκc hκcl hπ hr hA hFF F (fun j => hφs j) hfk huk
    he x
  choose L hL using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hLT : ∀ x, truncatePlaneHk (hKoutM x) (L x) =
      truncatePlaneHk (hKoutF x) (uF (Fin.last Nw) x (t₀ + S)) := fun x =>
    rff_eq_of_pairing_tendsto (((truncatePlaneHk (hKoutM x)).continuous.tendsto (L x)).comp
      (hL x)) (s3b_rough_pair hD hκc hκcl hπ hκF hκm hmF hmc hKoutF hKoutM hWb hch hfk huk he x)
  have hjetL : ∀ x a (wd : DerivativeWord2 a), a ≤ Kout x →
      planeJetOrder (L x) a wd = planeJetOrder (uF (Fin.last Nw) x (t₀ + S)) a wd := by
    intro x a wd ha
    rw [← planeJetOrder_truncate (hKoutM x) ha (L x) wd, hLT x,
      planeJetOrder_truncate (hKoutF x) ha _ wd]
  -- one approximant
  set NN := negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 F with hNN
  have hstep : ∀ j, jetOutputNorm π pout Kmax ϖ r (fun x a wd z =>
      planeJetOrder (truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))) a wd z -
        orderedDerivative wd (Kp (φs j) x) z) ≤
      Bc * (NN + ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ
        (fun x z => F x z - φs j x z)) := by
    intro j
    have hKk : Kp (fun x' => planeValue (fk j x')) = Kp (φs j) :=
      hKc (fun x' => planeValue (fk j x')) (φs j)
        (fun x => planeJetOrder_memLp (Nat.zero_le _) (fk j x) _) (hφs2 j) (hfk j)
    have hc := hComp (fk j) (uk j) (wk j) (hcdk j) (huk j)
    rw [hKk, negJetNorm_congr_ae π _ k ϖ 1 (hfk j)] at hc
    have hneg : negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (φs j) ≤
        NN + ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ
          (fun x z => F x z - φs j x z) := by
      have hφe : φs j = fun x z => F x z - (F x z - φs j x z) := by
        funext x z
        abel
      conv_lhs => rw [hφe]
      exact (s3b_negJetNorm_sub_le π _ k ϖ 1 F (fun x z => F x z - φs j x z) hF2
        fun x => (hF2 x).sub (hφs2 j x)).trans
        (add_le_add le_rfl (hP1 (fun x z => F x z - φs j x z) fun x => (hFm x).sub (hφsm j x)))
    refine le_trans (le_of_eq ?_) (hc.trans (mul_le_mul_right hneg _))
    refine jetOutputNorm_congr_ae π pout Kmax ϖ r fun x a wd ha => ?_
    exact Filter.Eventually.of_forall fun z => by
      simp only [planeJetOrder_truncate (hκcl x) ha]
  have hlimB : Tendsto (fun j => Bc * (NN + ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks)
      ϖ (fun x z => F x z - φs j x z))) atTop (𝓝 (Bc * NN)) := by
    have h0 : Tendsto (fun j => Bc * (NN + ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks)
        ϖ (fun x z => F x z - φs j x z))) atTop (𝓝 (Bc * (NN + ENNReal.ofReal C₁ * 0))) :=
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add (ENNReal.Tendsto.const_mul he
        (Or.inr ENNReal.ofReal_ne_top))) (Or.inr hBc)
    simpa using h0
  exact s3b_rough_final hr Kp hKs F hF2 hφs2 (hKlim F φs hF2 hφs2 hconvP)
    (fun j x => truncatePlaneHk (hκcl x) (uk j (Fin.last Nw) x (t₀ + S))) L hL
    (fun x a wd => planeJetOrder (uF (Fin.last Nw) x (t₀ + S)) a wd) hjetL hlimB hstep

end Rough

end AVRegularity.CycleWords.Seam
end
