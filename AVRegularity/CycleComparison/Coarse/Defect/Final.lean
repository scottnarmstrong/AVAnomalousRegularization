-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Defect.ConjW
import AVRegularity.CycleComparison.Coarse.Energy.Cell
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseDefect
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The two sides of the conjugation identity at one time, written through pairings of the
response sums with test fields: the response side summed over the box of cells, and the retained
side of the witness. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem slot_ge_one {i j : ℕ} (hi : i ≤ J) (hj : j ≤ H) : 1 ≤ coarseSlot k J H L i j := by
  have := boxSlot_le (k := k) (L := L) hi hj
  have hL := P.L_eq
  omega

/-- **The response side summed over the box of cells.** -/
theorem conj_response_side {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (htr : ∀ ij ∈ cellBox J H, ∀ w,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 w s) = U ij.1 ij.2 w s)
    (v : ι) {χ : Vec 2 → h v} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hp : AVenhance.IsZ2Periodic χ) :
    ∑ ij ∈ cellBox J H, respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) χ s =
      cellInner (familyValueSum k J H L U (cellBox J H) v s) (driftDeriv (b s) χ)
        + B * cellInner (familyValueSum k J H L U (cellBox J H) v s) (lapField χ)
        + cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
          (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
            (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p (gradField χ)))
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
            (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p (gradField χ)))) := by
  have hb := P.drift_smooth s hs
  have hbp := P.drift_per s hs
  have hdiv := P.drift_div s hs
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradField χ) := contDiff_gradField_top hχ
  have hgp : AVenhance.IsZ2Periodic (gradField χ) := isZ2Periodic_gradField hχ hp
  have hQg : ContDiff ℝ (⊤ : ℕ∞)
      (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p (gradField χ)) :=
    contDiff_covPolyQ_top _ p hg
  have hQgp : AVenhance.IsZ2Periodic
      (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p (gradField χ)) :=
    isZ2Periodic_covPolyQ _ p hg hgp
  have hTc := (fluxAdj_regular P hs v hQg hQgp).1
  have hEc := fun u => (edgeAdj_regular P hs v u hQg hQgp).1
  have hdrc : Continuous (driftDeriv (b s) χ) := (contDiff_driftDeriv_top hb hχ).continuous
  have hlapc : Continuous (lapField χ) := by
    unfold lapField
    exact continuous_finsetSum _ fun k _ => (contDiff_partialOp_top (contDiff_partialOp_top hχ k)
      k).continuous
  -- one cell
  have hcell : ∀ ij ∈ cellBox J H, respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) χ s =
      cellInner (tval (U ij.1 ij.2 v s)) (driftDeriv (b s) χ)
        + B * cellInner (tval (U ij.1 ij.2 v s)) (lapField χ)
        - (cellInner ((if ij.1 = 0 then fun _ _ _ => 0
            else fun w s x => (U (ij.1 - 1) ij.2 w s).toFunction.jet
              (valueIndex2 (coarseSlot k J H L (ij.1 - 1) ij.2)) x) v s)
            (fun x => -(AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
              (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p (gradField χ)) x))
          + ∑ u, cellInner ((if ij.2 = 0 then fun _ _ _ => 0
            else fun w s x => (U ij.1 (ij.2 - 1) w s).toFunction.jet
              (valueIndex2 (coarseSlot k J H L ij.1 (ij.2 - 1))) x) u s)
            (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
              (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p (gradField χ))))) := by
    intro ij hij
    obtain ⟨hi, hj⟩ := mem_cellBox hij
    obtain ⟨_, _, _, hflux⟩ := hR ij.1 hi ij.2 hj
    rw [respRhs_eq_pairings (slot_ge_one P hi hj) (G ij.1 ij.2 v) (htr ij hij v) hb hbp hdiv hχ hp,
      responseFlux_component hflux hs v (gradField χ) hg hgp]
    rfl
  rw [Finset.sum_congr rfl hcell, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (s := cellBox J H),
    ← cellInner_familyValueSum U _ v s hdrc, ← cellInner_familyValueSum U _ v s hlapc,
    sum_cellInner_pred1 U v s (by
      exact (continuous_neg.comp hTc))]
  rw [Finset.sum_congr rfl fun u _ => sum_cellInner_pred2 U u s (hEc u)]
  rw [cellInner_neg_right]
  ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem retained_order : k + 1 + D + 2 * p ≤ k + 2 * L := by
  have := P.L_eq; omega

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] P in
theorem lapField_regular (v : ι) {ψ : Vec 2 → h v} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (lapField ψ) ∧ AVenhance.IsZ2Periodic (lapField ψ) := by
  have h1 : ∀ k : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (partialOp k ψ) := fun k => contDiff_partialOp_top hψ k
  have h2 : ∀ k : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (partialOp k (partialOp k ψ)) := fun k =>
    contDiff_partialOp_top (h1 k) k
  refine ⟨ContDiff.sum fun k _ => h2 k, fun n x => ?_⟩
  unfold lapField
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp1 := isZ2Periodic_partialOp (hψ.differentiable (by simp)) hp k
  exact isZ2Periodic_partialOp ((h1 k).differentiable (by simp)) hp1 k n x

/-- **The retained side, through the response sums.** -/
theorem conj_witness_side {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (_hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) {ψ : Vec 2 → h v} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v ψ s x =
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (driftDeriv (b s) ψ))
        + B * cellInner (familyValueSum k J H L U (cellBox J H) v s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (lapField ψ))
        + cellInner (familyValueSum k J H L U (cellBox J H) v s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (rateOp Jm B s ψ))
        - cellInner (familyValueSum k J H L U (cellBox J H) v s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
            (AVRegularity.diagonalFluxAdjoint D AD s (gradField ψ)))
        - ∑ u, cellInner (familyValueSum k J H L U (cellBox J H) u s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
            (edgeBlock D H CE s v u (gradField ψ)))
        - ((cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
            (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
              (gradField ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
                (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (gradField ψ))))
          - ∑ u, cellInner
            (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
            (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
              (gradField ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
                (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (gradField ψ))))))
          + (cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
              (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
                (gradField ψ))
            - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
              (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
                (edgeBlock D H CE s v u (gradField ψ))))
          + cellInner
            (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
            (taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s (gradField ψ))) := by
  have hb := P.drift_smooth s hs
  have hbp := P.drift_per s hs
  have hdiv := P.drift_div s hs
  have hD := P.D_ge
  have hNL : D ≤ N := by have := P.L_eq; have := P.N_eq; nlinarith
  have hord := retained_order P
  have hA : ∀ d, ContDiff ℝ (D : WithTop ℕ∞) (AD d s) := fun d =>
    (P.AD_smooth d s hs).of_le (by exact_mod_cast hNL)
  have hC : ∀ r ∈ Finset.Icc 1 H, ∀ u d, ContDiff ℝ (D : WithTop ℕ∞) (CE r v u d s) :=
    fun r hr u d => (P.CE_smooth r hr v u d s hs).of_le (by exact_mod_cast hNL)
  obtain ⟨-, e⟩ := integral_wIntegrand W Fc (by omega) (by omega) (by omega) v hb hbp hdiv hA
    (fun d => P.AD_per d s hs) hC (fun r hr u d => P.CE_per r hr v u d s hs) hψ hp
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradField ψ) := contDiff_gradField_top hψ
  have hgp : AVenhance.IsZ2Periodic (gradField ψ) := isZ2Periodic_gradField hψ hp
  have hWp : ∀ w (X : Vec 2 → h w), ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) X →
      AVenhance.IsZ2Periodic X → cellInner (tval (W w s)) X =
        cellInner (familyValueSum k J H L U (cellBox J H) w s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p X) := fun w X hX hXp => by
    rw [witness_W_eq (covarianceMatrix Jm B t₀) U W hWit.1 hord hs w]
    exact cellInner_retainedW _ U hord w s hX hXp
  have hlap := lapField_regular v hψ hp
  have hrate : ContDiff ℝ (⊤ : ℕ∞) (rateOp Jm B s ψ) ∧
      AVenhance.IsZ2Periodic (rateOp Jm B s ψ) := by
    have h1 : ∀ k : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (partialOp k ψ) := fun k =>
      contDiff_partialOp_top hψ k
    refine ⟨ContDiff.sum fun k _ => ContDiff.sum fun l _ =>
      (contDiff_partialOp_top (h1 k) l).const_smul _, fun n x => ?_⟩
    unfold rateOp
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hp1 := isZ2Periodic_partialOp (hψ.differentiable (by simp)) hp k
    exact congrArg (fun z => (Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l) • z)
      (isZ2Periodic_partialOp ((h1 k).differentiable (by simp)) hp1 l n x)
  have h2p : ∀ {F : Vec 2 → h v}, ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) F := fun hF => hF.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [e, hWp v _ (h2p (contDiff_driftDeriv_top hb hψ)) (isZ2Periodic_driftDeriv hψ hbp hp),
    hWp v _ (h2p hlap.1) hlap.2, hWp v _ (h2p hrate.1) hrate.2,
    hWp v _ (diagFlux_regular P hs v hg hgp).1 (diagFlux_regular P hs v hg hgp).2,
    Finset.sum_congr rfl fun u _ => hWp u _ (edgeBlock_regular P hs v u hg hgp).1
      (edgeBlock_regular P hs v u hg hgp).2,
    witness_Fc_component hWit hs v (gradField ψ) hg hgp]

end
end

/-! **The conjugation identity at one time.** The response side (the time derivative of the
covariance polynomial plus the summed response identities) equals the retained side of the
witness: `M 𝖯_p = 𝖯_p L_c + div F_p - (𝖩 - BI):D² 𝒞^p/p!` tested against a smooth periodic field,
with the drift commutator, the commutation of constant-coefficient operators and the
cancellation `𝖯_p𝖰_p + (I - 𝖯_p𝖰_p) = I`. -/

section
/-- The real algebra of the matching. -/
theorem conj_algebra {B aCP aDχ aLχ a1TQ e2Q aPD aPL aPR aPdiag ebE a1T e2T a3T e4E aTay aComm
    a1Tg e2g : ℝ}
    (hDχ : aDχ = aPD - aComm) (hLχ : aLχ = aPL) (hCP : aCP = aPR - aTay)
    (hT : a1Tg + a3T = aComm - aPdiag) (hE : ebE = e2g + e4E) (h1 : a1TQ + a1T = a1Tg)
    (h2 : e2Q + e2T = e2g) :
    aCP + (aDχ + B * aLχ + a1TQ - e2Q) =
      aPD + B * aPL + aPR - aPdiag - ebE - ((a1T - e2T) + (a3T - e4E) + aTay) := by
  subst hDχ hLχ hCP hE
  linarith

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Laplacian is the covariance operator of the identity matrix. -/
theorem lapField_eq_covOperator_one (χ : Vec 2 → E) :
    lapField χ = AVRegularity.covOperator (1 : Matrix (Fin 2) (Fin 2) ℝ) χ := by
  funext x
  simp only [lapField, AVRegularity.covOperator, Matrix.one_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

/-- The rate operator is the covariance operator of the symmetric matrix `𝖩(s) - B I`. -/
theorem rateOp_eq_covOperator (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B s : ℝ)
    (hJ : ∀ i j, Jm s i j = Jm s j i) (χ : Vec 2 → E) :
    rateOp Jm B s χ = AVRegularity.covOperator (Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) χ := by
  funext x
  simp only [rateOp, AVRegularity.covOperator]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hJ k l]
  by_cases hkl : k = l
  · subst hkl; rfl
  · simp [Matrix.one_apply_ne hkl, Matrix.one_apply_ne (Ne.symm hkl)]

end General

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem cellInner_fam_sub {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (s : ℝ) {X Y : Vec 2 → h v} (hX : Continuous X)
    (hY : Continuous Y) :
    cellInner (familyValueSum k J H L U S v s) (X - Y) =
      cellInner (familyValueSum k J H L U S v s) X -
        cellInner (familyValueSum k J H L U S v s) Y := by
  unfold cellInner
  simp_rw [Pi.sub_apply, inner_sub_right]
  exact integral_sub (integrable_familyValueSum_inner U S v s hX)
    (integrable_familyValueSum_inner U S v s hY)

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [Fintype ι] [DecidableEq ι] in
theorem covarianceMatrix_symm (hJ : ∀ t i j, Jm t i j = Jm t j i) (B t₀ s : ℝ) (i j : Fin 2) :
    covarianceMatrix Jm B t₀ s i j = covarianceMatrix Jm B t₀ s j i := by
  simp only [covarianceMatrix, Matrix.of_apply]
  congr 1
  funext r
  rw [hJ r i j]
  by_cases hij : i = j
  · subst hij; rfl
  · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

omit [Fintype ι] [DecidableEq ι] in
/-- Pairings of a family sum with a test operator are additive, through its formal adjoint. -/
theorem fam_adj_add {k J H L m R Kc : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) {v u : ι} {s : ℝ} {C : ℝ}
    {T : (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h u)}
    (A : TorusAdj T m R Kc C) (hKc : k + m ≤ Kc) (hm : k + m ≤ k + 2 * L)
    {X Y : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hXp : AVenhance.IsZ2Periodic X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hYp : AVenhance.IsZ2Periodic Y) :
    cellInner (familyValueSum k J H L U S u s) (T X) +
        cellInner (familyValueSum k J H L U S u s) (T Y) =
      cellInner (familyValueSum k J H L U S u s) (T (X + Y)) := by
  have hXY : ContDiff ℝ (⊤ : ℕ∞) (X + Y) := hX.add hY
  have hXYp : AVenhance.IsZ2Periodic (X + Y) := fun n x => by
    simp only [Pi.add_apply, hXp n x, hYp n x]
  rw [← cellInner_adj_respSum U S hS A hKc hm hX hXp, ← cellInner_adj_respSum U S hS A hKc hm hY hYp,
    ← cellInner_adj_respSum U S hS A hKc hm hXY hXYp]
  have h := cellInner_add_right (tval (A.adj k hKc (truncateTorusHk hm (respSum k J H L U S u s))))
    (integrable_tval_inner _ hX.continuous) (integrable_tval_inner _ hY.continuous)
  exact h.symm

end Setting

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- **The conjugation identity at one time.** -/
theorem conj_at
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (htr : ∀ ij ∈ cellBox J H, ∀ w,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 w s) = U ij.1 ij.2 w s)
    (v : ι) {ψ : Vec 2 → h v} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (AVRegularity.covOperator (Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) (p - 1) ψ))
      + ∑ ij ∈ cellBox J H, respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ) s
      = ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v ψ s x := by
  have hHs : ∀ i j, covarianceMatrix Jm B t₀ s i j = covarianceMatrix Jm B t₀ s j i :=
    covarianceMatrix_symm P.J_symm B t₀ s
  have hb := P.drift_smooth s hs
  have hbp := P.drift_per s hs
  have hdiv := P.drift_div s hs
  have hp1 := P.p_pos
  obtain ⟨Bb, hBb⟩ := exists_drift_bounds P
  obtain ⟨BA, hBA⟩ := exists_diag_bounds P
  obtain ⟨BE, hBE⟩ := exists_edge_bounds P
  have hm : k + (6 * p + D) ≤ k + 2 * L := by have := (fcOrd_le P).2; omega
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradField ψ) := contDiff_gradField_top hψ
  have hgp : AVenhance.IsZ2Periodic (gradField ψ) := isZ2Periodic_gradField hψ hp
  have hχ := contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p hψ
  have hχp := isZ2Periodic_covPolyP (covarianceMatrix Jm B t₀ s) p hψ hp
  have hPg := contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p hg
  have hPgp := isZ2Periodic_covPolyP (covarianceMatrix Jm B t₀ s) p hg hgp
  have hQPg := contDiff_covPolyQ_top (covarianceMatrix Jm B t₀ s) p hPg
  have hQPgp := isZ2Periodic_covPolyQ (covarianceMatrix Jm B t₀ s) p hPg hPgp
  have hdr := contDiff_driftDeriv_top hb hψ
  rw [conj_response_side P hR hs htr v hχ hχp, conj_witness_side P hR hWit hs v hψ hp,
    gradField_covPolyP _ p hψ]
  -- the drift commutator
  have hcomm := covPolyP_driftDeriv_sub (covarianceMatrix Jm B t₀ s) hHs b s hb hdiv p hψ
  have hPdr := contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p hdr
  have hdrP := contDiff_driftDeriv_top hb hχ
  have hCommc : Continuous (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
      (driftDeriv (b s) ψ) - driftDeriv (b s) (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s)
        p ψ)) := hPdr.continuous.sub hdrP.continuous
  rw [hcomm] at hCommc
  have hDχ : cellInner (familyValueSum k J H L U (cellBox J H) v s)
      (driftDeriv (b s) (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)) =
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (driftDeriv (b s) ψ)) -
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
          (AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[l - 1 - a]
            (AVRegularity.commutatorAdjoint b (covarianceMatrix Jm B t₀ s) s
              ((AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[a] (gradField ψ)))) := by
    rw [← cellInner_fam_sub U _ v s hPdr.continuous hCommc, ← hcomm, sub_sub_cancel]
  -- the Laplacian
  have hLχ : cellInner (familyValueSum k J H L U (cellBox J H) v s)
      (lapField (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)) =
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (lapField ψ)) := by
    rw [lapField_eq_covOperator_one, lapField_eq_covOperator_one,
      covPolyP_covOperator_comm _ _ p hψ]
  -- the time derivative and the Taylor term
  have hrate := rateOp_eq_covOperator Jm B s (P.J_symm s) ψ
  have hCψ := contDiff_covOperator_top (Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hψ
  have hPC := contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p hCψ
  have hTay : taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s (gradField ψ) =
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[p]
        (AVRegularity.covOperator (Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ψ) := by
    rw [← hrate]; rfl
  have hTayc : Continuous (taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s (gradField ψ)) := by
    rw [hTay]
    exact continuous_const.smul (contDiff_covIter_top _ hCψ p).continuous
  have hCP : cellInner (familyValueSum k J H L U (cellBox J H) v s)
      (AVRegularity.covOperator (Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) (p - 1) ψ)) =
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (rateOp Jm B s ψ)) -
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s (gradField ψ)) := by
    have hPrate : Continuous (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (rateOp Jm B s ψ)) := by rw [hrate]; exact hPC.continuous
    rw [← cellInner_fam_sub U _ v s hPrate hTayc, hrate, hTay,
      covPolyP_eq_sub_one _ hp1, covPolyP_covOperator_comm _ _ (p - 1) hψ, add_sub_cancel_right]
  -- the coarse flux adjoint splits
  have hTc := (fluxAdj_regular P hs v hg hgp).1
  have hPdiag : Continuous (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
      (AVRegularity.diagonalFluxAdjoint D AD s (gradField ψ))) := by
    have e : AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (AVRegularity.diagonalFluxAdjoint D AD s (gradField ψ)) =
        (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
          (AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[l - 1 - a]
            (AVRegularity.commutatorAdjoint b (covarianceMatrix Jm B t₀ s) s
              ((AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[a] (gradField ψ)))) -
        AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s (gradField ψ) := by
      unfold AVRegularity.coarseFluxAdjoint; abel
    rw [e]; exact hCommc.sub hTc
  have hT : cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
        (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s (gradField ψ)) +
      cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
        (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s (gradField ψ)) =
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
          (AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[l - 1 - a]
            (AVRegularity.commutatorAdjoint b (covarianceMatrix Jm B t₀ s) s
              ((AVRegularity.covOperator (covarianceMatrix Jm B t₀ s))^[a] (gradField ψ)))) -
      cellInner (familyValueSum k J H L U (cellBox J H) v s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.diagonalFluxAdjoint D AD s (gradField ψ))) := by
    rw [← cellInner_familyValueSum_union U (disjoint_diag J H) v s hTc, ← cellBox_eq_union_diag,
      ← cellInner_fam_sub U _ v s hCommc hPdiag]
    rfl
  -- the edge rows split
  have hE : ∑ u, cellInner (familyValueSum k J H L U (cellBox J H) u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (edgeBlock D H CE s v u (gradField ψ))) =
      ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (edgeBlock D H CE s v u (gradField ψ))) +
      ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (edgeBlock D H CE s v u (gradField ψ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [cellBox_eq_union_edge, cellInner_familyValueSum_union U (disjoint_edge J H) u s
      (edgeAdj_regular P hs v u hg hgp).1]
  -- additivity through the adjoints
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hgQP : ContDiff ℝ (⊤ : ℕ∞) (gradField ψ - AVRegularity.covPolyQ
      (covarianceMatrix Jm B t₀ s) p (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (gradField ψ))) := hg.sub hQPg
  have hgQPp : AVenhance.IsZ2Periodic (gradField ψ - AVRegularity.covPolyQ
      (covarianceMatrix Jm B t₀ s) p (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (gradField ψ))) := fun n x => by simp only [Pi.sub_apply, hgp n x, hQPgp n x]
  have hsum : AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
      (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (gradField ψ)) +
      (gradField ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (gradField ψ))) = gradField ψ :=
    add_sub_cancel _ _
  have h1 := fam_adj_add (s := s) U _ hS1 (fcT3 P hs v Bb hBb BA hBA) le_rfl hm hQPg hQPgp hgQP
    hgQPp
  rw [hsum] at h1
  have h2 : ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
          (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
            (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (gradField ψ))))) +
      ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
          (gradField ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
            (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (gradField ψ))))) =
      ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (edgeBlock D H CE s v u (gradField ψ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have := fam_adj_add (s := s) U _ hS2 (fcT4 P hs v u (BE v u) (hBE v u)) le_rfl hm hQPg hQPgp
      hgQP hgQPp
    rw [hsum] at this
    exact this
  exact conj_algebra hDχ hLχ hCP hT hE h1 h2

end Main
end

/-! **The defect identity for smooth tests.** For a smooth periodic test field `ψ`, the retained
field satisfies `(W(t),ψ) - (f,ψ) = ∫_{(t₀,t]} ∫ wIntegrand`: test each response with the
time-dependent field `𝖯_p(s)ψ` (product rule), sum over the box of cells, identify `W(t)` and the
initial values, and apply the conjugation identity at almost every time. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The initial values of the responses add up to the incoming field. -/
theorem sum_initial {k J H L N : ℕ} {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {t₀ : ℝ} (v : ι)
    (hinit : ∀ ij ∈ cellBox J H, (if ij.1 = 0 ∧ ij.2 = 0 then
        (U ij.1 ij.2 v t₀).toFunction.jet (valueIndex2 (coarseSlot k J H L ij.1 ij.2))
          =ᵐ[volume.restrict AVenhance.unitCube] (f v).toFunction.jet (valueIndex2 N)
       else U ij.1 ij.2 v t₀ = 0))
    {ψ : Vec 2 → h v} :
    ∑ ij ∈ cellBox J H, cellInner (tval (U ij.1 ij.2 v t₀)) ψ =
      cellInner (fun x => (f v).toFunction.jet (valueIndex2 N) x) ψ := by
  have h00 : ((0, 0) : ℕ × ℕ) ∈ cellBox J H := by simp [cellBox]
  rw [Finset.sum_eq_single_of_mem _ h00]
  · have := hinit (0, 0) h00
    simp only [and_self, ↓reduceIte] at this
    exact cellInner_congr_left this ψ
  · intro ij hij hne
    have hz : ¬ (ij.1 = 0 ∧ ij.2 = 0) := fun hc => hne (Prod.ext hc.1 hc.2)
    have := hinit ij hij
    simp only [hz, ↓reduceIte] at this
    rw [this]
    exact cellInner_tval_zero ψ

/-- **The defect identity for smooth tests.** -/
theorem defect_smooth
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (v : ι) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) {ψ : Vec 2 → h v} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    IntegrableOn (fun s => ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v ψ s x)
        (Set.Ioc t₀ t) ∧
      cellInner (tval (W v t)) ψ - cellInner (fun x => (f v).toFunction.jet (valueIndex2 N) x) ψ =
        ∫ s in Set.Ioc t₀ t, ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v ψ s x := by
  obtain ⟨Φ, hval, hder⟩ := covPolyP_timeTest (E := h v) Jm B t₀ t₁ P.window P.J_meas
    (jm_bound P) ψ hψ hp p P.p_pos
  have hbc : ∀ s ∈ Set.Icc t₀ t₁, Continuous (b s) := fun s hs => (P.drift_smooth s hs).continuous
  have hcell : ∀ ij ∈ cellBox J H,
      IntegrableOn (fun s => cellInner (tval (U ij.1 ij.2 v s)) (Φ.deriv s) +
        respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) (Φ.val s) s) (Set.Ioc t₀ t) ∧
      cellInner (tval (U ij.1 ij.2 v t)) (Φ.val t) -
          cellInner (tval (U ij.1 ij.2 v t₀)) (Φ.val t₀) =
        ∫ s in Set.Ioc t₀ t, (cellInner (tval (U ij.1 ij.2 v s)) (Φ.deriv s) +
          respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) (Φ.val s) s) := fun ij hij => by
    obtain ⟨hi, hj⟩ := mem_cellBox hij
    obtain ⟨_, _, hsol, _⟩ := hR ij.1 hi ij.2 hj
    exact resp_timeTest hsol hbc v Φ ht
  have hsumI : IntegrableOn (fun s => ∑ ij ∈ cellBox J H,
      (cellInner (tval (U ij.1 ij.2 v s)) (Φ.deriv s) +
        respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) (Φ.val s) s)) (Set.Ioc t₀ t) :=
    integrable_finsetSum _ fun ij hij => (hcell ij hij).1
  have hsumE : ∑ ij ∈ cellBox J H, (cellInner (tval (U ij.1 ij.2 v t)) (Φ.val t) -
      cellInner (tval (U ij.1 ij.2 v t₀)) (Φ.val t₀)) =
      ∫ s in Set.Ioc t₀ t, ∑ ij ∈ cellBox J H,
        (cellInner (tval (U ij.1 ij.2 v s)) (Φ.deriv s) +
          respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) (Φ.val s) s) := by
    rw [integral_finsetSum _ fun ij hij => (hcell ij hij).1]
    exact Finset.sum_congr rfl fun ij hij => (hcell ij hij).2
  -- the endpoint values
  have hord := retained_order P
  have h0mem : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_rfl, P.window⟩
  have hΦt := hval t ht
  have hΦ0 : Φ.val t₀ = ψ := by rw [hval t₀ h0mem, covPolyP_initial]
  have hPψ := contDiff_covPolyP_top (covarianceMatrix Jm B t₀ t) p hψ
  have hWt : cellInner (tval (W v t)) ψ =
      ∑ ij ∈ cellBox J H, cellInner (tval (U ij.1 ij.2 v t)) (Φ.val t) := by
    rw [witness_W_eq (covarianceMatrix Jm B t₀) U W hWit.1 hord ht v,
      cellInner_retainedW _ U hord v t (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hp, hΦt,
      cellInner_familyValueSum U _ v t hPψ.continuous]
  have hinit : ∀ ij ∈ cellBox J H, (if ij.1 = 0 ∧ ij.2 = 0 then
        (U ij.1 ij.2 v t₀).toFunction.jet (valueIndex2 (coarseSlot k J H L ij.1 ij.2))
          =ᵐ[volume.restrict AVenhance.unitCube] (f v).toFunction.jet (valueIndex2 N)
       else U ij.1 ij.2 v t₀ = 0) := fun ij hij => by
    obtain ⟨hi, hj⟩ := mem_cellBox hij
    obtain ⟨f₀, hf₀, hsol, _⟩ := hR ij.1 hi ij.2 hj
    rw [hsol.2.2.2.1 v]
    split_ifs at hf₀ ⊢ <;> exact hf₀ v
  have hf0 : ∑ ij ∈ cellBox J H, cellInner (tval (U ij.1 ij.2 v t₀)) (Φ.val t₀) =
      cellInner (fun x => (f v).toFunction.jet (valueIndex2 N) x) ψ := by
    rw [hΦ0]; exact sum_initial v hinit
  -- the integrands agree at almost every time
  have htr_ae : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), ∀ ij ∈ cellBox J H, ∀ w,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 w s) = U ij.1 ij.2 w s := by
    rw [Filter.eventually_all_finset]
    intro ij hij
    obtain ⟨hi, hj⟩ := mem_cellBox hij
    obtain ⟨_, _, hsol, _⟩ := hR ij.1 hi ij.2 hj
    exact ae_all_iff.2 hsol.2.2.1
  have htr' := ae_restrict_of_ae_restrict_of_subset
    (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)) htr_ae
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)), ∑ ij ∈ cellBox J H,
      (cellInner (tval (U ij.1 ij.2 v s)) (Φ.deriv s) +
        respRhs B b (Uw ij.1 ij.2 v) (G ij.1 ij.2 v) (Φ.val s) s) =
      ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v ψ s x := by
    filter_upwards [htr', ae_restrict_mem measurableSet_Ioc] with s htrs hs
    have hsI : s ∈ Set.Icc t₀ t₁ := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hCP := contDiff_covOperator_top (Jm s - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) (p - 1) hψ)
    rw [Finset.sum_add_distrib, hder s hsI, hval s hsI,
      ← cellInner_familyValueSum U _ v s hCP.continuous]
    exact conj_at P hR hWit hsI htrs v hψ hp
  refine ⟨hsumI.congr hae, ?_⟩
  rw [hWt, ← hf0, ← Finset.sum_sub_distrib, hsumE]
  exact integral_congr_ae hae
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Coarse

/-! Pieces of the extension of the defect identity to first-order test fields: the integrand of the
weak identity of the retained field for a test `φ ∈ H¹`, its agreement with the smooth integrand on
Galerkin approximants, and its subtractivity in the test. -/

section Jet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

theorem jet_sub_ae {K : ℕ} (U V : TorusHk K E) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a,
      (U - V).toFunction.jet a x = U.toFunction.jet a x - V.toFunction.jet a x := by
  rw [ae_all_iff]
  intro a
  filter_upwards [periodicJetRepresentative_ae (U - V).val a,
    periodicJetRepresentative_ae U.val a, periodicJetRepresentative_ae V.val a,
    Lp.coeFn_sub (U.val a) (V.val a)] with x h1 h2 h3 h4
  change periodicJetRepresentative (U - V).val a x =
    periodicJetRepresentative U.val a x - periodicJetRepresentative V.val a x
  rw [h1, h2, h3]
  exact h4

end Jet

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The integrand of the weak identity of the retained field, tested with `φ ∈ H¹`. -/
def defIntegrand {K₀ : ℕ} (B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (φ : TorusHk 1 (h v))
    (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, b s x k * inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x)
      (φ.toFunction.jet (valueIndex2 1) x))
    - B * ∑ k : Fin 2, inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
    - ∑ k : Fin 2, inner ℝ (AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k +
        (Fc v s).toFunction.jet (valueIndex2 K₀) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
    + inner ℝ ((fun (_ : ℝ) (_ : Vec 2) => (0 : h v)) s x) (φ.toFunction.jet (valueIndex2 1) x)

/-- On Galerkin approximants the integrand is the smooth integrand. -/
theorem defIntegrand_galerkin_ae {K₀ : ℕ} (B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (φ : TorusHk 1 (h v))
    (n : ℕ) (s : ℝ) :
    defIntegrand B b D H AD CE Jm W Fc v (galerkinProj n φ) s
      =ᵐ[volume.restrict AVenhance.unitCube]
        wIntegrand B b D H AD CE Jm W Fc v (approxField n φ) s := by
  filter_upwards [galerkin_value_ae n φ, galerkin_deriv_ae n φ 0, galerkin_deriv_ae n φ 1]
    with x h0 hd0 hd1
  have hdk : ∀ k : Fin 2, (galerkinProj n φ).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x
      = fderiv ℝ (approxField n φ) x (basisVec k) := fun k => by
    fin_cases k
    exacts [hd0, hd1]
  unfold defIntegrand wIntegrand
  simp only [h0, hdk, inner_zero_left, add_zero]

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open Filter Topology
namespace AVRegularity.CycleComparison.Coarse

/-! **The exact defects of a coarse witness**: the retained field
`W` solves `(M I - E) W = div F_coarse` with `W(t₀) = f`, in the weak form `IsCoarseDefect`, for
every first-order test field. The identity holds for smooth tests (`defect_smooth`); both sides
are bounded linear in the test, uniformly in time, and the Galerkin projections of a first-order
field are smooth approximants converging to it. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [DecidableEq ι] in
/-- The defect integrand is an abstract weak integrand. -/
theorem defIntegrand_eq_weak {K₀ K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (φ : TorusHk 1 (h v))
    (s : ℝ) :
    defIntegrand B b D H AD CE Jm W Fc v φ s =
      weakIntegrand (fun k x => b s x k) B (fun k => torusJetOrder (W v s) 1 (fun _ => k))
        (fun k x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k +
          (Fc v s).toFunction.jet (valueIndex2 K₀) x k)
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) := by
  funext x
  simp only [defIntegrand, weakIntegrand, inner_zero_left, add_zero]

omit [DecidableEq ι] in
/-- The defect integrand is subtractive in the test. -/
theorem defIntegrand_sub {K₀ K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (φ φ' : TorusHk 1 (h v))
    (s : ℝ) :
    defIntegrand B b D H AD CE Jm W Fc v (φ - φ') s =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => defIntegrand B b D H AD CE Jm W Fc v φ s x -
        defIntegrand B b D H AD CE Jm W Fc v φ' s x := by
  filter_upwards [jet_sub_ae φ φ'] with x hx
  rw [defIntegrand_eq_weak, defIntegrand_eq_weak, defIntegrand_eq_weak]
  simp only [weakIntegrand, hx, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Uniform bounds of the defect integrand.** -/
theorem defIntegrand_bound
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (v : ι) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc t₀ t₁, ∀ φ : TorusHk 1 (h v),
      Integrable (defIntegrand B b D H AD CE Jm W Fc v φ s)
          (volume.restrict AVenhance.unitCube) ∧
        |∫ x in AVenhance.unitCube, defIntegrand B b D H AD CE Jm W Fc v φ s x| ≤ M * ‖φ‖ := by
  obtain ⟨Cb, hCb⟩ := P.drift_bdd
  obtain ⟨MW, hMW⟩ := witness_W_bounded P hR hWit
  obtain ⟨MF, hMF⟩ := witness_Fc_bounded P hR hWit
  obtain ⟨Mj, hMj⟩ := jm_bound P
  set CA : ℝ := ∑ d : Finset.Icc 2 D, coeffSup t₀ t₁ (AD d) 0
  set CC : ℝ := ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
    coeffSup t₀ t₁ (CE r v u d) 0
  set MZ : ℝ := dfConst D H (Fintype.card ι) CA CC (Mj + |B|) * MW + MF
  refine ⟨2 * Cb * MW + 2 * |B| * MW + 2 * MZ, fun s hs φ => ?_⟩
  -- coefficient bounds
  have hAD : ∀ d x, ‖AD d s x‖ ≤ CA := fun d x => by
    have h1 : ‖AD d s x‖ ≤ ‖coefficientDerivativeArray (AD d s) 0 x‖ :=
      norm_ordered_le_array (AD d s) 0 Fin.elim0 x
    refine h1.trans ((coeffSup_bound P.rho_pos (P.AD_fin d) (Nat.zero_le _) hs x).trans ?_)
    exact Finset.single_le_sum (f := fun d => coeffSup t₀ t₁ (AD d) 0)
      (fun d _ => coeffSup_nonneg _ _ _ _) (Finset.mem_univ d)
  have hCE : ∀ r ∈ Finset.Icc 1 H, ∀ u d x, ‖CE r v u d s x‖ ≤ CC := fun r hr u d x => by
    have h1 : ‖CE r v u d s x‖ ≤ ‖coefficientDerivativeArray (CE r v u d s) 0 x‖ :=
      norm_ordered_le_array (CE r v u d s) 0 Fin.elim0 x
    refine h1.trans ((coeffSup_bound P.rho_pos (P.CE_fin r hr v u d) (Nat.zero_le _) hs x).trans
      ?_)
    have e1 := Finset.single_le_sum (f := fun d => coeffSup t₀ t₁ (CE r v u d) 0)
      (fun d _ => coeffSup_nonneg _ _ _ _) (Finset.mem_univ d)
    have e2 := Finset.single_le_sum (f := fun u => ∑ d : Finset.Icc 2 D,
      coeffSup t₀ t₁ (CE r v u d) 0)
      (fun u _ => Finset.sum_nonneg fun d _ => coeffSup_nonneg _ _ _ _) (Finset.mem_univ u)
    have e3 := Finset.single_le_sum (f := fun r => ∑ u : ι, ∑ d : Finset.Icc 2 D,
      coeffSup t₀ t₁ (CE r v u d) 0)
      (fun r _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ =>
        coeffSup_nonneg _ _ _ _) hr
    exact e1.trans (e2.trans e3)
  have hJ : ∀ k' l, |Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l| ≤ Mj + |B| :=
    fun k' l => by
      refine (abs_sub _ _).trans (add_le_add (hMj s hs k' l) ?_)
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg B) ?_
      by_cases hkl : k' = l
      · rw [hkl, Matrix.one_apply_eq, abs_one]
      · rw [Matrix.one_apply_ne hkl, abs_zero]; exact zero_le_one
  obtain ⟨hDFm, hDFb⟩ := coarseDefectFlux_memLp_bound W (by have := P.D_ge; omega)
    (by omega) B AD CE Jm v s hAD hCE hJ (fun w => hMW s hs w)
    (fun d => (P.AD_smooth d s hs).continuous)
    (fun r hr u d => (P.CE_smooth r hr v u d s hs).continuous)
  -- the components of the flux
  have hFcm : MemLp (fun x => (Fc v s).toFunction.jet (valueIndex2 k) x) 2
      (volume.restrict AVenhance.unitCube) := memLp_jet (Fc v s) _
  have hFcb : (eLpNorm (fun x => (Fc v s).toFunction.jet (valueIndex2 k) x) 2
      (volume.restrict AVenhance.unitCube)).toReal ≤ MF :=
    (eLpNorm_jet_le (Fc v s) _).trans (hMF s hs v)
  have hcomp : ∀ {G : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {M : ℝ},
      MemLp G 2 (volume.restrict AVenhance.unitCube) →
      (eLpNorm G 2 (volume.restrict AVenhance.unitCube)).toReal ≤ M → ∀ k',
      MemLp (fun x => G x k') 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => G x k') 2 (volume.restrict AVenhance.unitCube)).toReal ≤ M :=
    fun {G M} hG hGb k' => by
      have hm := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => h v) k').comp_memLp' hG
      refine ⟨hm, le_trans (ENNReal.toReal_mono hG.eLpNorm_lt_top.ne
        (eLpNorm_mono hm.aestronglyMeasurable fun x => PiLp.norm_apply_le (G x) k')) hGb⟩
  have hZ : ∀ k', MemLp (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k' +
      (Fc v s).toFunction.jet (valueIndex2 k) x k') 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k' +
        (Fc v s).toFunction.jet (valueIndex2 k) x k') 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ MZ := fun k' => by
    obtain ⟨m1, b1⟩ := hcomp hDFm hDFb k'
    obtain ⟨m2, b2⟩ := hcomp hFcm hFcb k'
    refine ⟨m1.add m2, ?_⟩
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨m1.eLpNorm_lt_top.ne, m2.eLpNorm_lt_top.ne⟩)
      (eLpNorm_add_le (by norm_num))).trans ?_
    rw [ENNReal.toReal_add m1.eLpNorm_lt_top.ne m2.eLpNorm_lt_top.ne]
    exact add_le_add b1 b2
  -- the jets
  have hK : 1 ≤ k + 1 + D := by omega
  have hJm : ∀ k', MemLp (torusJetOrder (W v s) 1 (fun _ => k')) 2
      (volume.restrict AVenhance.unitCube) := fun k' => memLp_torusJetOrder _ hK _
  have hJb : ∀ k', (eLpNorm (torusJetOrder (W v s) 1 (fun _ => k')) 2
      (volume.restrict AVenhance.unitCube)).toReal ≤ MW := fun k' =>
    (eLpNorm_torusJetOrder_le _ hK _).trans (hMW s hs v)
  have hbm : ∀ k', AEStronglyMeasurable (fun x => b s x k')
      (volume.restrict AVenhance.unitCube) := fun k' =>
    ((continuous_apply k').comp (P.drift_smooth s hs).continuous).aestronglyMeasurable
  have hb : ∀ k' x, |b s x k'| ≤ Cb := fun k' x =>
    (norm_le_pi_norm (b s x) k').trans (hCb s hs x)
  rw [defIntegrand_eq_weak]
  exact weakIntegrand_integrable_and_bound hbm hb B hJm hJb (fun k' => (hZ k').1)
    (fun k' => (hZ k').2) (memLp_jet φ _) (eLpNorm_jet_le φ _) (fun k' => memLp_jet φ _)
    (fun k' => eLpNorm_jet_le φ _)


section Pairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The value pairing with a first-order test is subtractive in the test. -/
theorem integral_inner_jet_sub {F : Vec 2 → E}
    (hF : MemLp F 2 (volume.restrict AVenhance.unitCube)) (φ φ' : TorusHk 1 E) :
    ∫ x in AVenhance.unitCube, inner ℝ (F x) ((φ - φ').toFunction.jet (valueIndex2 1) x) =
      (∫ x in AVenhance.unitCube, inner ℝ (F x) (φ.toFunction.jet (valueIndex2 1) x)) -
        ∫ x in AVenhance.unitCube, inner ℝ (F x) (φ'.toFunction.jet (valueIndex2 1) x) := by
  rw [← integral_sub (integrable_inner_memLp hF (memLp_jet φ (valueIndex2 1)))
    (integrable_inner_memLp hF (memLp_jet φ' (valueIndex2 1)))]
  refine integral_congr_ae ?_
  filter_upwards [jet_sub_ae φ φ'] with x hx
  rw [hx, inner_sub_right]

/-- The value pairing with a first-order test is bounded by the norm of the test. -/
theorem abs_integral_inner_jet_le {K : ℕ} (U : TorusHk K E) (φ : TorusHk 1 E) :
    |∫ x in AVenhance.unitCube, inner ℝ (U.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 1) x)| ≤ ‖U‖ * ‖φ‖ :=
  (abs_integral_inner_le (memLp_jet U _) (memLp_jet φ _)).trans
    (mul_le_mul (eLpNorm_jet_le U _) (eLpNorm_jet_le φ _) ENNReal.toReal_nonneg (norm_nonneg _))

end Pairing

/-- **The exact defect identity of a coarse witness**. -/
theorem coarseDefect_of_witness
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc) :
    AVRegularity.IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc := by
  intro v t ht φ
  obtain ⟨M, hM⟩ := defIntegrand_bound P hR hWit v
  have hIcc : ∀ s ∈ Set.Ioc t₀ t, s ∈ Set.Icc t₀ t₁ := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hWm := memLp_jet (W v t) (valueIndex2 (k + 1 + D))
  have hfm := memLp_jet (f v) (valueIndex2 N)
  let Lf : TorusHk 1 (h v) → ℝ := fun φ =>
    (∫ x in AVenhance.unitCube, inner ℝ ((W v t).toFunction.jet (valueIndex2 (k + 1 + D)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) -
    ∫ x in AVenhance.unitCube, inner ℝ ((f v).toFunction.jet (valueIndex2 N) x)
      (φ.toFunction.jet (valueIndex2 1) x)
  let Rf : ℝ → TorusHk 1 (h v) → ℝ := fun s φ =>
    ∫ x in AVenhance.unitCube, defIntegrand B b D H AD CE Jm W Fc v φ s x
  have hLsub : ∀ φ φ', Lf (φ - φ') = Lf φ - Lf φ' := fun φ φ' => by
    simp only [Lf]
    rw [integral_inner_jet_sub hWm φ φ', integral_inner_jet_sub hfm φ φ']
    ring
  have hLb : ∀ φ, |Lf φ| ≤ (‖W v t‖ + ‖f v‖) * ‖φ‖ := fun φ => by
    simp only [Lf]
    refine (abs_sub _ _).trans ?_
    rw [add_mul]
    exact add_le_add (abs_integral_inner_jet_le _ φ) (abs_integral_inner_jet_le _ φ)
  have hRsub : ∀ s ∈ Set.Ioc t₀ t, ∀ φ φ', Rf s (φ - φ') = Rf s φ - Rf s φ' :=
    fun s hs φ φ' => by
      simp only [Rf]
      rw [integral_congr_ae (defIntegrand_sub W Fc v φ φ' s)]
      exact integral_sub (hM s (hIcc s hs) φ).1 (hM s (hIcc s hs) φ').1
  have hRb : ∀ s ∈ Set.Ioc t₀ t, ∀ φ, |Rf s φ| ≤ M * ‖φ‖ := fun s hs φ =>
    (hM s (hIcc s hs) φ).2
  have hN : ∀ n, IntegrableOn (fun s => Rf s (galerkinProj n φ)) (Set.Ioc t₀ t) ∧
      Lf (galerkinProj n φ) = ∫ s in Set.Ioc t₀ t, Rf s (galerkinProj n φ) := fun n => by
    obtain ⟨hI, heq⟩ := defect_smooth P hR hWit v ht (approxField_contDiff n φ)
      (approxField_periodic n φ)
    have hR' : (fun s => Rf s (galerkinProj n φ)) = fun s =>
        ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v (approxField n φ) s x :=
      funext fun s => integral_congr_ae (defIntegrand_galerkin_ae B b D H AD CE Jm W Fc v φ n s)
    have hL' : Lf (galerkinProj n φ) =
        cellInner (tval (W v t)) (approxField n φ) -
          cellInner (fun x => (f v).toFunction.jet (valueIndex2 N) x) (approxField n φ) := by
      simp only [Lf, cellInner, tval]
      congr 1
      · refine integral_congr_ae ?_
        filter_upwards [galerkin_value_ae n φ] with x hx
        rw [hx]
      · refine integral_congr_ae ?_
        filter_upwards [galerkin_value_ae n φ] with x hx
        rw [hx]
    refine ⟨?_, ?_⟩
    · rw [hR']; exact hI
    · rw [hR', hL']; exact heq
  obtain ⟨hI, heq⟩ := integrated_identity_of_tendsto Lf Rf hLsub hLb hRsub hRb
    (galerkinProj_tendsto φ) hN
  exact ⟨integrable_inner_memLp hWm (memLp_jet φ _), integrable_inner_memLp hfm (memLp_jet φ _),
    fun s hs => (hM s (hIcc s hs) φ).1, hI, heq⟩

end AVRegularity.CycleComparison.Coarse
end
