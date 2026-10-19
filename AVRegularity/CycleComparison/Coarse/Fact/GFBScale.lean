-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The coarse response flux operators, `ψ ↦ -(F_p^* 𝖰_p ψ)` and `ψ ↦ 𝖯_p (F_E^* 𝖰_p ψ)_u`, have
formal adjoints in gradient form (`GAdj`) of order `4p + D`. Both are in divergence form,
`T = ∑ⱼ ∂ⱼ ∘ Sⱼ`, with the inner fluxes `Sⱼ` of order `4p + D - 1` (`TorusAdj.coarseFluxDiv`,
`TorusAdj.edgeFluxPairDiv`); the bound is `∑ⱼ Cⱼ` for any factorial bounds `Cⱼ` of the adjoints
of the `Sⱼ`. -/

section
section Coarse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The coarse flux `ψ ↦ -(F_p(s)^* 𝖰_p ψ)` has a gradient-form formal adjoint of order `4p + D`
(`D ≥ 1`), bounded by `∑ⱼ Cⱼ` times the factorial norm of the gradient, where `Cⱼ` are factorial
bounds of the adjoints of the inner fluxes `Sⱼ = TorusAdj.coarseFluxDiv ⋯ j`. The hypotheses are
those of `TorusAdj.coarseFlux`, with `1 ≤ R`. -/
def GAdj.coarseFlux (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (ρ : ℝ) {Cf : Fin 2 → ℝ}
    (hF : ∀ j, (TorusAdj.coarseFluxDiv (E := E) Hc hM b D p hD AD s j R Kc Q hQR hQK hb hbp Bb hBb
      hA hAp BA hBA).FBound ρ (Cf j)) (hCf : ∀ j, 0 ≤ Cf j) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      fun x => -(AVRegularity.coarseFluxAdjoint D b AD Hc p s
        (AVRegularity.covPolyQ Hc p ψ) x)) (4 * p + D - 1) Kc ρ (∑ j, Cf j) :=
  GAdj.ofDiv hR (fun j => TorusAdj.coarseFluxDiv (E := E) Hc hM b D p hD AD s j R Kc Q hQR hQK
    hb hbp Bb hBb hA hAp BA hBA) ρ hF hCf
    (fun ψ hs _ => (coarseFlux_divRep Hc b D p AD s Q (by omega) hb hA _
      (contDiff_covPolyQ_smooth Hc p hs)).2)

end Coarse

section Edge

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The `(v,u)` block of the edge flux `ψ ↦ 𝖯_p (F_E(s)^* 𝖰_p ψ)_u` has a gradient-form formal
adjoint of order `4p + D` (`D ≥ 1`), bounded by `∑ⱼ Cⱼ` times the factorial norm of the gradient,
where `Cⱼ` are factorial bounds of the adjoints of `Sⱼ = TorusAdj.edgeFluxPairDiv ⋯ j`. The
hypotheses are those of `TorusAdj.edgeFluxPair`, with `1 ≤ R`. -/
def GAdj.edgeFluxPair (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (D H p : ℕ) (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l)
    (ρ : ℝ) {Cf : Fin 2 → ℝ}
    (hF : ∀ j, (TorusAdj.edgeFluxPairDiv Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp BE
      hBE).FBound ρ (Cf j)) (hCf : ∀ j, 0 ≤ Cf j) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y)
            (AVRegularity.covPolyQ Hc p ψ y)) x)) (4 * p + D - 1) Kc ρ (∑ j, Cf j) :=
  GAdj.ofDiv hR (fun j => TorusAdj.edgeFluxPairDiv Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp
    BE hBE) ρ hF hCf
    (fun ψ hs _ => (edgeFlux_divRep Hc D H p CE v u s Q (by omega) hC _
      (contDiff_covPolyQ_smooth Hc p hs)).2)

end Edge
end

/-! Factorial-norm bounds for the divergence-form inner operators of the coarse fluxes: the word
`wordDiv`, the commutator coefficient `commInner`, one commutator term `commStep`, the diagonal
flux `diagFluxDiv` and the edge flux block `edgeFluxBlockDiv`, with explicit constants. -/

section
/-- The factorial-norm constant of `wordDivTerm m j`: `2^(m-1) (Kc/ρ)^(m-1)`. -/
def gfbWordConst (ρ : ℝ) (Kc m : ℕ) : ℝ := 2 ^ (m - 1) * ((Kc : ℝ) / ρ) ^ (m - 1)

/-- The factorial-norm constant of the divergence-form diagonal flux. -/
def gfbDiagConst (ρ : ℝ) (D Kc : ℕ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  ∑ d : Finset.Icc 2 D,
    gfbWordConst ρ Kc (d.1 - 1) * fbMulConst ρ (tensorBound (d.1 - 1) (BA d.1)) Kc

/-- The factorial-norm constant of the divergence-form edge flux block. -/
def gfbEdgeConst (ρ : ℝ) (D H Kc : ℕ) (BE : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
    gfbWordConst ρ Kc (d.1 - 1) * fbMulConst ρ (BE r d.1) Kc

theorem gfbWordConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Kc m : ℕ) : 0 ≤ gfbWordConst ρ Kc m := by
  unfold gfbWordConst; positivity

theorem gfbDiagConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) {D Kc : ℕ} {BA : ℕ → ℕ → ℝ}
    (hB : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BA d.1 l) : 0 ≤ gfbDiagConst ρ D Kc BA :=
  Finset.sum_nonneg fun d _ => mul_nonneg (gfbWordConst_nonneg hρ _ _)
    (fbMulConst_nonneg hρ.le fun l hl => by
      have := hB d l hl
      unfold tensorBound; positivity)

theorem gfbEdgeConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) {D H Kc : ℕ} {BE : ℕ → ℕ → ℕ → ℝ}
    (hB : ∀ r, ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BE r d.1 l) :
    0 ≤ gfbEdgeConst ρ D H Kc BE :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun d _ =>
    mul_nonneg (gfbWordConst_nonneg hρ _ _) (fbMulConst_nonneg hρ.le (hB r d))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {ρ : ℝ}

namespace TorusAdj.FBound

/-- The word flux `wordDivTerm m j` costs `2^(m-1) (Kc/ρ)^(m-1)`. -/
theorem wordDiv (hρ : 0 < ρ) (m : ℕ) (j : Fin 2) (R Kc : ℕ) :
    (TorusAdj.wordDiv (E := E) m j R Kc).FBound ρ (gfbWordConst ρ Kc m) := by
  cases m with
  | zero =>
    refine FBound.mono_const (Cf := 0) ?_ (gfbWordConst_nonneg hρ _ _)
    unfold TorusAdj.wordDiv
    exact FBound.ofOp _ (FBound.mono (FBound.zero (E := E) 0 R Kc ρ) le_rfl le_rfl _)
  | succ n =>
    have h := FBound.sumMem (Finset.univ : Finset (DerivativeWord2 n)) (fun α _ =>
      FBound.ofOrder (Nat.add_zero n) (FBound.comp (orderedDerivativeRev (E := E) hρ α R Kc)
        (componentOp (E := E) hρ.le (Fin.cons j α : Fin (n + 1) → Fin 2) (R + n) Kc)
        zero_le_one le_rfl le_rfl))
    unfold TorusAdj.wordDiv
    exact FBound.ofOp _ (((h.smul ((-1 : ℝ) ^ (n + 1))).mono le_rfl le_rfl _).mono_const
      (le_of_eq (by
        unfold gfbWordConst
        rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
        simp [Finset.sum_const, Finset.card_univ, mul_comm])))

/-- The inner commutator coefficient. -/
theorem commInner (hρ : 0 < ρ) (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 1 ≤ Q)
    (hQK : Kc + 1 ≤ Q) (hb : ContDiff ℝ (Q : ℕ) (b s)) (hp : AVenhance.IsZ2Periodic (b s))
    (Bb : ℕ → ℝ) (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    (TorusAdj.commInner (E := E) b Hc hM s j R Kc Q hQR hQK hb hp Bb hBb).FBound ρ
      (fbMulConst ρ (commBound M Bb) Kc) := by
  unfold TorusAdj.commInner
  exact FBound.mulOp hρ.le

/-- One inner commutator term. -/
theorem commStep (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (b : ℝ → Vec 2 → Vec 2) (s : ℝ) (j : Fin 2) (R Kc Q p D l a : ℕ)
    (hal : a < l) (hlp : l ≤ p) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    (TorusAdj.commStep (E := E) Hc hM b s j R Kc Q p D l a hal hlp hQR hQK hb hbp Bb
      hBb).FBound ρ
      (fbCovConst ρ Hc Kc ^ (l - 1 - a) *
        (fbMulConst ρ (commBound M Bb) Kc * fbCovConst ρ Hc Kc ^ a)) := by
  have hc := fbCovConst_nonneg hρ Hc Kc
  have hBb0 : ∀ l ≤ Kc, 0 ≤ Bb l := fun l hl => (norm_nonneg _).trans (hBb l hl 0)
  have hcomm := fbMulConst_nonneg hρ.le (commBound_nonneg ((covBound_nonneg Hc).trans hM) hBb0)
  have h2 : 0 ≤ fbMulConst ρ (commBound M Bb) Kc * fbCovConst ρ Hc Kc ^ a :=
    mul_nonneg hcomm (pow_nonneg hc a)
  unfold TorusAdj.commStep
  exact FBound.ofOp _ (FBound.liftOrder (FBound.comp
    (FBound.covIter (E := E) hρ Hc hM _ R Kc)
    (FBound.comp (FBound.commInner (E := E) hρ b Hc hM s j _ Kc Q (by omega) hQK hb hbp Bb hBb)
      (FBound.covIter (E := PiLp 2 (fun _ : Fin 2 => E)) hρ Hc hM a _ Kc)
      (pow_nonneg hc a) le_rfl le_rfl) h2 le_rfl le_rfl)
    (mul_nonneg (pow_nonneg hc _) h2) _)

/-- The divergence-form diagonal flux. -/
theorem diagFluxDiv (hρ : 0 < ρ) (D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    (TorusAdj.diagFluxDiv (E := E) D AD s j R Kc Q hQR hQK hA hp BA hBA).FBound ρ
      (gfbDiagConst ρ D Kc BA) := by
  unfold TorusAdj.diagFluxDiv
  refine FBound.ofOp _ (FBound.sum _ (fun d => FBound.liftOrder
    (FBound.comp (FBound.wordDiv (E := E) hρ (d.1 - 1) j R Kc) (FBound.tensorFlux hρ.le)
      (fbMulConst_nonneg hρ.le (fun l hl => ?_)) le_rfl (by omega))
    (mul_nonneg (gfbWordConst_nonneg hρ _ _) (fbMulConst_nonneg hρ.le (fun l hl => ?_))) _))
  all_goals
    have := coefficient_bound_nonneg (hBA d) l hl
    unfold tensorBound; positivity

/-- The divergence-form edge flux block. -/
theorem edgeFluxBlockDiv (hρ : 0 < ρ) {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y]
    [BorelSpace Y] [CompleteSpace Y] [FiniteDimensional ℝ Y] (D H : ℕ)
    (C : ℕ → ∀ d : Finset.Icc 2 D, Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => Y)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => X)))
    (j : Fin 2) (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (C r d)) (hp : ∀ r d, AVenhance.IsZ2Periodic (C r d))
    (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (C r d) l x‖ ≤ BE r d.1 l) :
    (TorusAdj.edgeFluxBlockDiv D H C j R Kc Q hQR hQK hC hp BE hBE).FBound ρ
      (gfbEdgeConst ρ D H Kc BE) := by
  unfold TorusAdj.edgeFluxBlockDiv
  refine FBound.sumMem _ (fun r _ => FBound.sum _ (fun d => FBound.liftOrder
    (FBound.comp (FBound.wordDiv (E := Y) hρ (d.1 - 1) j R Kc) (FBound.adjointCoeffOp hρ.le)
      (fbMulConst_nonneg hρ.le (coefficient_bound_nonneg (hBE r d))) le_rfl (by omega))
    (mul_nonneg (gfbWordConst_nonneg hρ _ _)
      (fbMulConst_nonneg hρ.le (coefficient_bound_nonneg (hBE r d)))) _))

end TorusAdj.FBound
end

/-! Factorial-norm bounds for the divergence-form inner fluxes `fluxDiv`, `coarseFluxDiv`,
`edgeFluxPairDiv`, and the resulting gradient-form adjoints `GAdj.coarseFluxF`,
`GAdj.edgeFluxPairF` with no remaining bound hypotheses. -/

section
/-- The constant of the inner flux `Sⱼ` of the coarse flux (before `𝖰_p`):
`fluxConstA c cc p + κ_p(c) * dg`. -/
def gfbFluxDivConst (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (M : ℝ) (Kc p D : ℕ)
    (Bb : ℕ → ℝ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  fluxConstA (fbCovConst ρ Hc Kc) (fbMulConst ρ (commBound M Bb) Kc) p +
    covPolyConst (fbCovConst ρ Hc Kc) p * gfbDiagConst ρ D Kc BA

/-- The factorial-norm constant of the inner flux of the coarse response flux. -/
def gfbCoarseDivConst (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (M : ℝ) (Kc p D : ℕ)
    (Bb : ℕ → ℝ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  coarseFluxConst (fbCovConst ρ Hc Kc) (fbMulConst ρ (commBound M Bb) Kc)
    (gfbDiagConst ρ D Kc BA) p

/-- The factorial-norm constant of the inner flux of the edge flux pair. -/
def gfbEdgeDivConst (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc p D H : ℕ)
    (BE : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  edgeFluxPairConst (fbCovConst ρ Hc Kc) p (gfbEdgeConst ρ D H Kc BE)

/-- The gradient constant of the coarse flux: `∑ⱼ` of the inner flux constants. -/
def gfbCoarseCg (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (M : ℝ) (Kc p D : ℕ)
    (Bb : ℕ → ℝ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  ∑ _j : Fin 2, gfbCoarseDivConst ρ Hc M Kc p D Bb BA

/-- The gradient constant of the edge flux pair. -/
def gfbEdgeCg (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc p D H : ℕ)
    (BE : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ _j : Fin 2, gfbEdgeDivConst ρ Hc Kc p D H BE

theorem gfbCoarseCg_eq (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (M : ℝ) (Kc p D : ℕ)
    (Bb : ℕ → ℝ) (BA : ℕ → ℕ → ℝ) :
    gfbCoarseCg ρ Hc M Kc p D Bb BA = 2 * gfbCoarseDivConst ρ Hc M Kc p D Bb BA := by
  simp [gfbCoarseCg]

theorem gfbEdgeCg_eq (ρ : ℝ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc p D H : ℕ)
    (BE : ℕ → ℕ → ℕ → ℝ) :
    gfbEdgeCg ρ Hc Kc p D H BE = 2 * gfbEdgeDivConst ρ Hc Kc p D H BE := by
  simp [gfbEdgeCg]

theorem gfbFluxDivConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (Kc p D : ℕ) {Bb : ℕ → ℝ} {BA : ℕ → ℕ → ℝ}
    (hB : ∀ l ≤ Kc, 0 ≤ Bb l) (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BA d.1 l) :
    0 ≤ gfbFluxDivConst ρ Hc M Kc p D Bb BA := by
  have hc := fbCovConst_nonneg hρ Hc Kc
  have hcc := fbMulConst_nonneg hρ.le (commBound_nonneg hM hB)
  have hdg := gfbDiagConst_nonneg hρ hBA
  have hk := covPolyConst_nonneg hρ Hc p Kc
  have hA : 0 ≤ fluxConstA (fbCovConst ρ Hc Kc) (fbMulConst ρ (commBound M Bb) Kc) p :=
    Finset.sum_nonneg fun l _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun a _ => mul_nonneg (pow_nonneg hc _) (mul_nonneg hcc (pow_nonneg hc _)))
  unfold gfbFluxDivConst
  positivity

theorem gfbCoarseDivConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (Kc p D : ℕ) {Bb : ℕ → ℝ} {BA : ℕ → ℕ → ℝ}
    (hB : ∀ l ≤ Kc, 0 ≤ Bb l) (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BA d.1 l) :
    0 ≤ gfbCoarseDivConst ρ Hc M Kc p D Bb BA :=
  mul_nonneg (gfbFluxDivConst_nonneg hρ Hc hM Kc p D hB hBA) (covPolyConst_nonneg hρ Hc p Kc)

theorem gfbEdgeDivConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (Kc p D H : ℕ) {BE : ℕ → ℕ → ℕ → ℝ}
    (hB : ∀ r, ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BE r d.1 l) :
    0 ≤ gfbEdgeDivConst ρ Hc Kc p D H BE := by
  have hk := covPolyConst_nonneg hρ Hc p Kc
  have he := gfbEdgeConst_nonneg (H := H) hρ hB
  unfold gfbEdgeDivConst edgeFluxPairConst
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {ρ : ℝ}

namespace TorusAdj.FBound

/-- The inner flux `Sⱼ` of the coarse flux, before `𝖰_p`. -/
theorem fluxDiv (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    (TorusAdj.fluxDiv (E := E) Hc hM b D p hD AD s j R Kc Q hQR hQK hb hbp Bb hBb hA hAp BA
      hBA).FBound ρ (gfbFluxDivConst ρ Hc M Kc p D Bb BA) := by
  have hdg : 0 ≤ gfbDiagConst ρ D Kc BA :=
    gfbDiagConst_nonneg hρ (fun d l hl => coefficient_bound_nonneg (hBA d) l hl)
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  have h1 : (TorusAdj.sumMem (Finset.Icc 1 p) fun l hl =>
        (TorusAdj.sumMem (Finset.range l) fun a ha =>
          TorusAdj.commStep (E := E) Hc hM b s j R Kc Q p D l a (Finset.mem_range.mp ha)
            (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb).smul ((l.factorial : ℝ)⁻¹)).FBound ρ
      (fluxConstA (fbCovConst ρ Hc Kc) (fbMulConst ρ (commBound M Bb) Kc) p) := by
    refine FBound.mono_const (Cf := ∑ l ∈ Finset.Icc 1 p, |((l.factorial : ℝ)⁻¹)| *
      ∑ a ∈ Finset.range l, fbCovConst ρ Hc Kc ^ (l - 1 - a) *
        (fbMulConst ρ (commBound M Bb) Kc * fbCovConst ρ Hc Kc ^ a)) ?_ (le_of_eq ?_)
    · exact FBound.sumMem _ (fun l hl => FBound.smul _
        (FBound.sumMem _ (fun a ha => FBound.commStep hρ Hc hM b s j R Kc Q p D l a
          (Finset.mem_range.mp ha) (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb)))
    · unfold fluxConstA
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have h2 := FBound.liftOrder (FBound.comp (FBound.covPolyP (E := E) hρ Hc hM p R Kc)
      (FBound.diagFluxDiv (E := E) hρ D AD s j (R + 2 * p) Kc Q (by omega) (by omega) hA hAp BA
        hBA) hdg le_rfl le_rfl) (mul_nonneg hkap hdg) (by omega : 2 * p + (D - 2) ≤ 2 * p + D - 1)
  unfold TorusAdj.fluxDiv
  exact FBound.mono (FBound.ofOp _ (FBound.sub (FBound.mono h1 le_rfl le_rfl _) h2))
    le_rfl le_rfl _

/-- The inner flux `Sⱼ` of the coarse response flux. -/
theorem coarseFluxDiv (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    (TorusAdj.coarseFluxDiv (E := E) Hc hM b D p hD AD s j R Kc Q hQR hQK hb hbp Bb hBb hA hAp
      BA hBA).FBound ρ (gfbCoarseDivConst ρ Hc M Kc p D Bb BA) := by
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  have h1 := FBound.fluxDiv (E := E) hρ Hc hM b D p hD AD s j R Kc Q hQR hQK hb hbp Bb hBb hA hAp
    BA hBA
  have h3 := FBound.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => E)) hρ Hc hM p
    (R + (2 * p + D - 1)) Kc
  unfold TorusAdj.coarseFluxDiv
  exact FBound.mono (FBound.ofOrder _ (FBound.neg (FBound.comp h1 h3 hkap le_rfl le_rfl)))
    le_rfl le_rfl _

/-- The inner flux `Sⱼ` of the edge flux pair. -/
theorem edgeFluxPairDiv {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D H p : ℕ)
    (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l) :
    (TorusAdj.edgeFluxPairDiv Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp BE hBE).FBound ρ
      (gfbEdgeDivConst ρ Hc Kc p D H BE) := by
  have hec : 0 ≤ gfbEdgeConst ρ D H Kc BE :=
    gfbEdgeConst_nonneg hρ (fun r d l hl => coefficient_bound_nonneg (hBE r d) l hl)
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  unfold TorusAdj.edgeFluxPairDiv
  exact FBound.liftOrder (FBound.comp (FBound.covPolyP (E := h u) hρ Hc hM p R Kc)
    (FBound.comp (FBound.edgeFluxBlockDiv (X := h v) (Y := h u) hρ D H (fun r d => CE r v u d s)
      j (R + 2 * p) Kc Q (by omega) hQK hC hp BE hBE)
      (FBound.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => h v)) hρ Hc hM p _ Kc)
      hkap le_rfl le_rfl) (mul_nonneg hec hkap) le_rfl le_rfl)
    (mul_nonneg hkap (mul_nonneg hec hkap)) _

end TorusAdj.FBound

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The coarse flux `ψ ↦ -(F_p(s)^* 𝖰_p ψ)` has a gradient-form adjoint with the explicit
constant `gfbCoarseCg = ∑ⱼ gfbCoarseDivConst = 2 * gfbCoarseDivConst`. -/
def GAdj.coarseFluxF (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      fun x => -(AVRegularity.coarseFluxAdjoint D b AD Hc p s
        (AVRegularity.covPolyQ Hc p ψ) x)) (4 * p + D - 1) Kc ρ
      (gfbCoarseCg ρ Hc M Kc p D Bb BA) :=
  GAdj.coarseFlux (E := E) Hc hM b D p hD AD s R Kc Q hR hQR hQK hb hbp Bb hBb hA hAp BA hBA ρ
    (Cf := fun _ => gfbCoarseDivConst ρ Hc M Kc p D Bb BA)
    (fun j => TorusAdj.FBound.coarseFluxDiv (E := E) hρ Hc hM b D p hD AD s j R Kc Q hQR hQK hb
      hbp Bb hBb hA hAp BA hBA)
    (fun _ => gfbCoarseDivConst_nonneg hρ Hc ((covBound_nonneg Hc).trans hM) Kc p D
      (fun l hl => (norm_nonneg _).trans (hBb l hl 0))
      (fun d l hl => coefficient_bound_nonneg (hBA d) l hl))

/-- The `(v,u)` block of the edge flux has a gradient-form adjoint with the explicit constant
`gfbEdgeCg = ∑ⱼ gfbEdgeDivConst = 2 * gfbEdgeDivConst`. -/
def GAdj.edgeFluxPairF {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (D H p : ℕ) (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l)
    (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y)
            (AVRegularity.covPolyQ Hc p ψ y)) x)) (4 * p + D - 1) Kc ρ
      (gfbEdgeCg ρ Hc Kc p D H BE) :=
  GAdj.edgeFluxPair Hc hM D H p hD CE v u s R Kc Q hR hQR hQK hC hp BE hBE ρ
    (Cf := fun _ => gfbEdgeDivConst ρ Hc Kc p D H BE)
    (fun j => TorusAdj.FBound.edgeFluxPairDiv hρ Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp BE
      hBE)
    (fun _ => gfbEdgeDivConst_nonneg hρ Hc Kc p D H
      (fun r d l hl => coefficient_bound_nonneg (hBE r d) l hl))

end Main
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Abstract-real algebra for the scale bounds of the coarse flux constants: monotonicity of the
covariance polynomial constants, the commutator coefficient, and the word and tensor factors. -/

theorem gfbCovPoly_mono {c c' : ℝ} (hc : 0 ≤ c) (h : c ≤ c') (p : ℕ) :
    covPolyConst c p ≤ covPolyConst c' p :=
  Finset.sum_le_sum fun l _ =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hc h l) (Nat.cast_nonneg _)

theorem gfbFluxA_mul (M cc : ℝ) (p : ℕ) : fluxConstA M cc p = cc * fluxConstA M 1 p := by
  unfold fluxConstA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : ∑ a ∈ Finset.range l, M ^ (l - 1 - a) * (cc * M ^ a) =
      cc * ∑ a ∈ Finset.range l, M ^ (l - 1 - a) * (1 * M ^ a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this]; ring

theorem gfbFluxA_nonneg {M : ℝ} (hM : 0 ≤ M) (p : ℕ) : 0 ≤ fluxConstA M 1 p :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hM _)
      (mul_nonneg zero_le_one (pow_nonneg hM _)))

theorem gfbFluxA_mono {M M' : ℝ} (hM : 0 ≤ M) (h : M ≤ M') (p : ℕ) :
    fluxConstA M 1 p ≤ fluxConstA M' 1 p := by
  have hM' : 0 ≤ M' := hM.trans h
  unfold fluxConstA
  refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum fun a _ => mul_le_mul (pow_le_pow_left₀ hM h _)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM h _) zero_le_one)
    (mul_nonneg zero_le_one (pow_nonneg hM _)) (pow_nonneg hM' _)

/-- `fbCovConst ≤ 4 Kc²` when `covBound ≤ 4 ρ²`. -/
theorem gfbCovConst_le {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc : ℕ)
    (h : covBound Hc ≤ 4 * ρ ^ 2) : fbCovConst ρ Hc Kc ≤ 4 * (Kc : ℝ) ^ 2 := by
  unfold fbCovConst
  calc covBound Hc * ((Kc : ℝ) / ρ) ^ 2 ≤ 4 * ρ ^ 2 * ((Kc : ℝ) / ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 4 * (Kc : ℝ) ^ 2 := by field_simp

/-- One term of the commutator coefficient constant. -/
theorem gfbCommTerm {ρ lam a B₀ M : ℝ} {Bb : ℕ → ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hB0 : 1 ≤ B₀) (hlam : 0 < lam) (hu : B₀ * ρ / lam ≤ 1 / 2)
    (hBb : ∀ l : ℕ, Bb l = 4 * 2 ^ (l + 1) * (a * B₀ ^ (l + 1) * ((l + 1).factorial : ℝ) *
      lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)))) {l Kc : ℕ} (hl : l ≤ Kc) :
    ρ ^ l / (l.factorial : ℝ) * commBound M Bb l ≤
      32 * ((Kc : ℝ) + 1) * 4 ^ Kc * (M * a * B₀) := by
  have hB : 0 ≤ B₀ := zero_le_one.trans hB0
  have hz : lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)) = (lam ^ l)⁻¹ := by
    rw [show (1 : ℤ) - ((l + 1 : ℕ) : ℤ) = -(l : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hfac : ((l + 1).factorial : ℝ) = ((l : ℝ) + 1) * (l.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hlf : (l.factorial : ℝ) ≠ 0 := by positivity
  have hlam' : lam ≠ 0 := hlam.ne'
  have heq : ρ ^ l / (l.factorial : ℝ) * commBound M Bb l =
      32 * (M * a * B₀) * ((l : ℝ) + 1) * (2 ^ l * 2 ^ l * 2 ^ l * (B₀ * ρ / lam) ^ l) := by
    unfold commBound
    rw [hBb l, hz, hfac, div_pow, mul_pow]
    field_simp
    ring
  rw [heq]
  have hu0 : 0 ≤ B₀ * ρ / lam := by positivity
  have h8 : 2 ^ l * 2 ^ l * 2 ^ l * (B₀ * ρ / lam) ^ l ≤ (4 : ℝ) ^ Kc := by
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    calc (2 * 2 * 2 * (B₀ * ρ / lam)) ^ l ≤ (4 : ℝ) ^ l :=
          pow_le_pow_left₀ (by positivity) (by linarith) l
      _ ≤ 4 ^ Kc := pow_le_pow_right₀ (by norm_num) hl
  have hl1 : (l : ℝ) + 1 ≤ (Kc : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hl
  have hX : 0 ≤ M * a * B₀ := by positivity
  calc 32 * (M * a * B₀) * ((l : ℝ) + 1) * (2 ^ l * 2 ^ l * 2 ^ l * (B₀ * ρ / lam) ^ l)
      ≤ 32 * (M * a * B₀) * ((Kc : ℝ) + 1) * (4 : ℝ) ^ Kc :=
        mul_le_mul (mul_le_mul_of_nonneg_left hl1 (by positivity)) h8 (by positivity)
          (by positivity)
    _ = 32 * ((Kc : ℝ) + 1) * 4 ^ Kc * (M * a * B₀) := by ring

/-- The commutator coefficient constant. -/
theorem gfbComm_le {ρ lam a B₀ M : ℝ} {Bb : ℕ → ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hB0 : 1 ≤ B₀) (hlam : 0 < lam) (hu : B₀ * ρ / lam ≤ 1 / 2)
    (hBb : ∀ l : ℕ, Bb l = 4 * 2 ^ (l + 1) * (a * B₀ ^ (l + 1) * ((l + 1).factorial : ℝ) *
      lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)))) (Kc : ℕ) :
    fbMulConst ρ (commBound M Bb) Kc ≤
      (32 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc) * (M * a * B₀) := by
  unfold fbMulConst
  refine (Finset.sum_le_card_nsmul _ _ (32 * ((Kc : ℝ) + 1) * 4 ^ Kc * (M * a * B₀))
    fun l hl => gfbCommTerm hρ hM ha hB0 hlam hu hBb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))
    |>.trans (le_of_eq ?_)
  rw [Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Tensor factor: `fbMulConst (tensorBound m BA) ≤ 2^(m+1) 2^Kc fbMulConst BA`. -/
theorem gfbTensor_le {ρ : ℝ} (hρ : 0 < ρ) (m Kc : ℕ) {BA : ℕ → ℝ} (hB : ∀ l ≤ Kc, 0 ≤ BA l) :
    fbMulConst ρ (tensorBound m BA) Kc ≤ 2 ^ (m + 1) * 2 ^ Kc * fbMulConst ρ BA Kc := by
  unfold fbMulConst
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l hl => ?_
  have hl' : l ≤ Kc := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have h2 : (2 : ℝ) ^ l ≤ 2 ^ Kc := pow_le_pow_right₀ (by norm_num) hl'
  have hb := hB l hl'
  unfold tensorBound
  have hp : 0 ≤ ρ ^ l / (l.factorial : ℝ) := by positivity
  calc ρ ^ l / (l.factorial : ℝ) * (2 ^ l * (2 ^ m * 2 * BA l))
      = (2 ^ l * 2 ^ m * 2) * (ρ ^ l / (l.factorial : ℝ) * BA l) := by ring
    _ ≤ (2 ^ Kc * 2 ^ m * 2) * (ρ ^ l / (l.factorial : ℝ) * BA l) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (0 : ℝ) ≤ 2 ^ m * 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h2 this]
    _ = 2 ^ (m + 1) * 2 ^ Kc * (ρ ^ l / (l.factorial : ℝ) * BA l) := by ring

/-- One diagonal term. -/
theorem gfbDiagTerm {ρ : ℝ} (hρ : 0 < ρ) (Kc D d : ℕ) (hd2 : 2 ≤ d) (hdD : d ≤ D)
    {BA : ℕ → ℝ} (hB : ∀ l ≤ Kc, 0 ≤ BA l) :
    gfbWordConst ρ Kc (d - 1) * fbMulConst ρ (tensorBound (d - 1) BA) Kc ≤
      (4 ^ D * ((Kc : ℝ) + 1) ^ D * 2 ^ Kc) * (fbMulConst ρ BA Kc / ρ ^ (d - 2)) := by
  have e1 : d - 1 - 1 = d - 2 := by omega
  have e2 : d - 1 + 1 = d := by omega
  have hT := gfbTensor_le hρ (d - 1) Kc hB
  rw [e2] at hT
  have hS : 0 ≤ fbMulConst ρ BA Kc := fbMulConst_nonneg hρ.le hB
  have hw : gfbWordConst ρ Kc (d - 1) = 2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) / ρ ^ (d - 2) := by
    unfold gfbWordConst; rw [e1, div_pow]; ring
  have hwρ : (0 : ℝ) < ρ ^ (d - 2) := by positivity
  have h4 : (2 : ℝ) ^ (d - 2) * 2 ^ d ≤ 4 ^ D := by
    have : (4 : ℝ) ^ D = 2 ^ D * 2 ^ D := by rw [← mul_pow]; norm_num
    rw [this]
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
      (pow_le_pow_right₀ (by norm_num) hdD) (by positivity) (by positivity)
  have h5 : (Kc : ℝ) ^ (d - 2) ≤ ((Kc : ℝ) + 1) ^ D :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg Kc : (0 : ℝ) ≤ Kc)]) (by omega))
  have key : 2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) * fbMulConst ρ (tensorBound (d - 1) BA) Kc ≤
      4 ^ D * ((Kc : ℝ) + 1) ^ D * 2 ^ Kc * fbMulConst ρ BA Kc := by
    calc 2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) * fbMulConst ρ (tensorBound (d - 1) BA) Kc
      ≤ 2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) * (2 ^ d * 2 ^ Kc * fbMulConst ρ BA Kc) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = ((2 : ℝ) ^ (d - 2) * 2 ^ d) * (Kc : ℝ) ^ (d - 2) * 2 ^ Kc * fbMulConst ρ BA Kc := by
          ring
      _ ≤ 4 ^ D * ((Kc : ℝ) + 1) ^ D * 2 ^ Kc * fbMulConst ρ BA Kc := by gcongr
  calc gfbWordConst ρ Kc (d - 1) * fbMulConst ρ (tensorBound (d - 1) BA) Kc
      = (2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) * fbMulConst ρ (tensorBound (d - 1) BA) Kc) /
          ρ ^ (d - 2) := by rw [hw]; ring
    _ ≤ (4 ^ D * ((Kc : ℝ) + 1) ^ D * 2 ^ Kc * fbMulConst ρ BA Kc) / ρ ^ (d - 2) :=
        div_le_div_of_nonneg_right key hwρ.le
    _ = _ := by ring

/-! Explicit scale bounds for the gradient constants of the coarse flux and of the edge flux
pair, with constants depending only on the natural numbers `Kc`, `D`, `p`, `H`. -/

/-- `κ_p(4 Kc²)`. -/
def gfbKap (Kc p : ℕ) : ℝ := covPolyConst (4 * (Kc : ℝ) ^ 2) p

/-- Constant of the commutator coefficient: `32 (Kc+1)² 4^Kc`. -/
def gfbCommCoef (Kc : ℕ) : ℝ := 32 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc

/-- Constant of the diagonal flux: `4^D (Kc+1)^D 2^Kc`. -/
def gfbDiagCoef (Kc D : ℕ) : ℝ := 4 ^ D * ((Kc : ℝ) + 1) ^ D * 2 ^ Kc

/-- Constant of the edge flux: `2^D (Kc+1)^D`. -/
def gfbEdgeCoef (Kc D : ℕ) : ℝ := 2 ^ D * ((Kc : ℝ) + 1) ^ D

/-- The scale constant of the coarse flux. -/
def gfbD (Kc D p : ℕ) : ℝ :=
  2 * gfbKap Kc p * (fluxConstA (4 * (Kc : ℝ) ^ 2) 1 p * gfbCommCoef Kc +
    gfbKap Kc p * gfbDiagCoef Kc D)

/-- The scale constant of the edge flux pair. -/
def gfbE (Kc D _H p : ℕ) : ℝ := 2 * gfbKap Kc p ^ 2 * gfbEdgeCoef Kc D

theorem gfbKap_nonneg (Kc p : ℕ) : 0 ≤ gfbKap Kc p := by
  unfold gfbKap covPolyConst
  exact Finset.sum_nonneg fun l _ => by positivity

theorem gfbCommCoef_nonneg (Kc : ℕ) : 0 ≤ gfbCommCoef Kc := by unfold gfbCommCoef; positivity

theorem gfbDiagCoef_nonneg (Kc D : ℕ) : 0 ≤ gfbDiagCoef Kc D := by unfold gfbDiagCoef; positivity

theorem gfbEdgeCoef_nonneg (Kc D : ℕ) : 0 ≤ gfbEdgeCoef Kc D := by unfold gfbEdgeCoef; positivity

theorem gfbD_nonneg (Kc D p : ℕ) : 0 ≤ gfbD Kc D p := by
  have := gfbFluxA_nonneg (M := 4 * (Kc : ℝ) ^ 2) (by positivity) p
  have := gfbKap_nonneg Kc p
  have := gfbCommCoef_nonneg Kc
  have := gfbDiagCoef_nonneg Kc D
  unfold gfbD; positivity

theorem gfbE_nonneg (Kc D H p : ℕ) : 0 ≤ gfbE Kc D H p := by
  have := gfbKap_nonneg Kc p
  have := gfbEdgeCoef_nonneg Kc D
  unfold gfbE; positivity

/-- The final assembly inequality of the coarse flux constant. -/
theorem gfbAssemble {κ κ0 fa1 F1 cc CC X dg DC S : ℝ} (hκ : 0 ≤ κ) (hκκ : κ ≤ κ0)
    (hfa0 : 0 ≤ fa1) (hfa : fa1 ≤ F1) (hcc : cc ≤ CC * X) (hdg0 : 0 ≤ dg) (hdg : dg ≤ DC * S)
    (hCC : 0 ≤ CC) (hDC : 0 ≤ DC) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    2 * ((cc * fa1 + κ * dg) * κ) ≤ 2 * κ0 * (F1 * CC + κ0 * DC) * (X + S) := by
  have hκ0 : 0 ≤ κ0 := hκ.trans hκκ
  have hF1 : 0 ≤ F1 := hfa0.trans hfa
  have h1 : cc * fa1 ≤ CC * X * F1 := mul_le_mul hcc hfa hfa0 (mul_nonneg hCC hX)
  have h2 : κ * dg ≤ κ0 * (DC * S) := mul_le_mul hκκ hdg hdg0 hκ0
  have h3 : (cc * fa1 + κ * dg) * κ ≤ (CC * X * F1 + κ0 * (DC * S)) * κ0 :=
    mul_le_mul (add_le_add h1 h2) hκκ hκ (by positivity)
  have e : (F1 * CC + κ0 * DC) * (X + S) =
      (CC * X * F1 + κ0 * (DC * S)) + (F1 * CC * S + κ0 * DC * X) := by ring
  have h4 : 0 ≤ F1 * CC * S + κ0 * DC * X := by positivity
  have h5 : CC * X * F1 + κ0 * (DC * S) ≤ (F1 * CC + κ0 * DC) * (X + S) := by
    rw [e]; linarith
  calc 2 * ((cc * fa1 + κ * dg) * κ) ≤ 2 * ((CC * X * F1 + κ0 * (DC * S)) * κ0) := by linarith
    _ ≤ 2 * (((F1 * CC + κ0 * DC) * (X + S)) * κ0) := by
        have := mul_le_mul_of_nonneg_right h5 hκ0
        linarith
    _ = 2 * κ0 * (F1 * CC + κ0 * DC) * (X + S) := by ring

/-- The diagonal constant against the weighted sums. -/
theorem gfbDiag_le {ρ : ℝ} (hρ : 0 < ρ) (Kc D : ℕ) {BA : ℕ → ℕ → ℝ}
    (hB : ∀ d l, 0 ≤ BA d l) :
    gfbDiagConst ρ D Kc BA ≤ gfbDiagCoef Kc D *
      ∑ d : Finset.Icc 2 D, fbMulConst ρ (BA d.1) Kc / ρ ^ (d.1 - 2) := by
  unfold gfbDiagConst
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun d _ => gfbDiagTerm hρ Kc D d.1 (Finset.mem_Icc.mp d.2).1
    (Finset.mem_Icc.mp d.2).2 (fun l _ => hB _ l)

/-- One edge term. -/
theorem gfbEdgeTerm {ρ : ℝ} (hρ : 0 < ρ) (Kc D d : ℕ) (hd2 : 2 ≤ d) (hdD : d ≤ D)
    {B : ℕ → ℝ} (hB : ∀ l ≤ Kc, 0 ≤ B l) :
    gfbWordConst ρ Kc (d - 1) * fbMulConst ρ B Kc ≤
      gfbEdgeCoef Kc D * (fbMulConst ρ B Kc / ρ ^ (d - 2)) := by
  have e1 : d - 1 - 1 = d - 2 := by omega
  have hS : 0 ≤ fbMulConst ρ B Kc := fbMulConst_nonneg hρ.le hB
  have hw : gfbWordConst ρ Kc (d - 1) = 2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) / ρ ^ (d - 2) := by
    unfold gfbWordConst; rw [e1, div_pow]; ring
  have hwρ : (0 : ℝ) < ρ ^ (d - 2) := by positivity
  have h4 : (2 : ℝ) ^ (d - 2) ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : (Kc : ℝ) ^ (d - 2) ≤ ((Kc : ℝ) + 1) ^ D :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg Kc : (0 : ℝ) ≤ Kc)]) (by omega))
  have key : 2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) * fbMulConst ρ B Kc ≤
      gfbEdgeCoef Kc D * fbMulConst ρ B Kc := by
    unfold gfbEdgeCoef
    gcongr
  calc gfbWordConst ρ Kc (d - 1) * fbMulConst ρ B Kc
      = (2 ^ (d - 2) * (Kc : ℝ) ^ (d - 2) * fbMulConst ρ B Kc) / ρ ^ (d - 2) := by
        rw [hw]; ring
    _ ≤ (gfbEdgeCoef Kc D * fbMulConst ρ B Kc) / ρ ^ (d - 2) :=
        div_le_div_of_nonneg_right key hwρ.le
    _ = _ := by ring

theorem gfbEdge_le {ρ : ℝ} (hρ : 0 < ρ) (Kc D H : ℕ) {BE : ℕ → ℕ → ℕ → ℝ}
    (hB : ∀ r d l, 0 ≤ BE r d l) :
    gfbEdgeConst ρ D H Kc BE ≤ gfbEdgeCoef Kc D *
      ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, fbMulConst ρ (BE r d.1) Kc / ρ ^ (d.1 - 2) := by
  unfold gfbEdgeConst
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun d _ => gfbEdgeTerm hρ Kc D d.1 (Finset.mem_Icc.mp d.2).1
    (Finset.mem_Icc.mp d.2).2 (fun l _ => hB _ _ l)

/-- Scale bound (D) for the coarse flux gradient constant. -/
theorem gfbCoarseCg_le {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M a B₀ lam : ℝ}
    (Kc D p : ℕ) (hc4 : covBound Hc ≤ 4 * ρ ^ 2) (hM : covBound Hc ≤ M) (ha : 0 ≤ a)
    (hB0 : 1 ≤ B₀) (hlam : 0 < lam) (hu : B₀ * ρ / lam ≤ 1 / 2) {Bb : ℕ → ℝ}
    {BA : ℕ → ℕ → ℝ}
    (hBb : ∀ l : ℕ, Bb l = 4 * 2 ^ (l + 1) * (a * B₀ ^ (l + 1) * ((l + 1).factorial : ℝ) *
      lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)))) (hBA : ∀ d l, 0 ≤ BA d l) :
    gfbCoarseCg ρ Hc M Kc p D Bb BA ≤ gfbD Kc D p * (M * a * B₀ +
      ∑ d : Finset.Icc 2 D,
        (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) * BA d.1 l) / ρ ^ (d.1 - 2)) := by
  have hM0 : 0 ≤ M := (covBound_nonneg Hc).trans hM
  have hc0 := fbCovConst_nonneg hρ Hc Kc
  have hcle := gfbCovConst_le hρ Hc Kc hc4
  have hBb0 : ∀ l ≤ Kc, 0 ≤ Bb l := fun l _ => by
    rw [hBb l]; positivity
  have hcc0 := fbMulConst_nonneg hρ.le (commBound_nonneg hM0 hBb0)
  have hcc := gfbComm_le hρ hM0 ha hB0 hlam hu hBb Kc
  have hdg0 := gfbDiagConst_nonneg (D := D) (Kc := Kc) hρ (fun d l _ => hBA d.1 l)
  have hdg := gfbDiag_le hρ Kc D hBA
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  have hX : 0 ≤ M * a * B₀ := by
    have : 0 ≤ B₀ := zero_le_one.trans hB0
    positivity
  have hS : 0 ≤ ∑ d : Finset.Icc 2 D, fbMulConst ρ (BA d.1) Kc / ρ ^ (d.1 - 2) :=
    Finset.sum_nonneg fun d _ => div_nonneg (fbMulConst_nonneg hρ.le (fun l _ => hBA d.1 l))
      (by positivity)
  have hfa := gfbFluxA_mono hc0 hcle p
  have hmain := gfbAssemble (κ := covPolyConst (fbCovConst ρ Hc Kc) p)
    (κ0 := gfbKap Kc p) (fa1 := fluxConstA (fbCovConst ρ Hc Kc) 1 p)
    (F1 := fluxConstA (4 * (Kc : ℝ) ^ 2) 1 p) (cc := fbMulConst ρ (commBound M Bb) Kc)
    (CC := gfbCommCoef Kc) (X := M * a * B₀) (dg := gfbDiagConst ρ D Kc BA)
    (DC := gfbDiagCoef Kc D)
    (S := ∑ d : Finset.Icc 2 D, fbMulConst ρ (BA d.1) Kc / ρ ^ (d.1 - 2)) hkap
    (gfbCovPoly_mono hc0 hcle p) (gfbFluxA_nonneg hc0 p) hfa hcc hdg0 hdg
    (gfbCommCoef_nonneg Kc) (gfbDiagCoef_nonneg Kc D) hX hS
  rw [gfbCoarseCg_eq]
  unfold gfbCoarseDivConst coarseFluxConst fluxConstF gfbD
  rw [gfbFluxA_mul (fbCovConst ρ Hc Kc)]
  unfold fbMulConst at hmain ⊢
  exact hmain

/-- Scale bound (E) for the edge flux pair gradient constant. -/
theorem gfbEdgeCg_le {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc D H p : ℕ)
    (hc4 : covBound Hc ≤ 4 * ρ ^ 2) {BE : ℕ → ℕ → ℕ → ℝ} (hBE : ∀ r d l, 0 ≤ BE r d l) :
    gfbEdgeCg ρ Hc Kc p D H BE ≤ gfbE Kc D H p *
      ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) * BE r d.1 l) /
          ρ ^ (d.1 - 2) := by
  have hc0 := fbCovConst_nonneg hρ Hc Kc
  have hcle := gfbCovConst_le hρ Hc Kc hc4
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  have hk1 := gfbCovPoly_mono hc0 hcle p
  have hk0 := gfbKap_nonneg Kc p
  have he0 := gfbEdgeConst_nonneg (D := D) (Kc := Kc) (H := H) hρ (fun r d l _ => hBE r d.1 l)
  have he := gfbEdge_le hρ Kc D H hBE
  have hS : 0 ≤ ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
      fbMulConst ρ (BE r d.1) Kc / ρ ^ (d.1 - 2) :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun d _ =>
      div_nonneg (fbMulConst_nonneg hρ.le (fun l _ => hBE r d.1 l)) (by positivity)
  have h1 : edgeFluxPairConst (fbCovConst ρ Hc Kc) p (gfbEdgeConst ρ D H Kc BE) ≤
      gfbKap Kc p * ((gfbEdgeCoef Kc D * (∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, fbMulConst ρ (BE r d.1) Kc / ρ ^ (d.1 - 2))) * gfbKap Kc p) := by
    unfold edgeFluxPairConst
    exact mul_le_mul hk1 (mul_le_mul he hk1 hkap (mul_nonneg (gfbEdgeCoef_nonneg Kc D) hS))
      (mul_nonneg he0 hkap) hk0
  rw [gfbEdgeCg_eq]
  unfold gfbEdgeDivConst gfbE
  refine le_of_le_of_eq (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)) ?_
  unfold fbMulConst
  ring

end AVRegularity.CycleComparison.Coarse
end
