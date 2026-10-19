-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.First.Identity
public import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.First.RepMain
import AVRegularity.Proofs.GenSem.First.Child
public import AVRegularity.Definitions.Entry.TerminalResidualClauses
import AVRegularity.CycleReference.FluxFastDiscrepancy
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Proofs.GenSem.Jet.Chart

section
@[expose] public noncomputable section
open Set Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Generation: the lift setup of the grade-zero lifts of the first source.** The grade-zero lifts
(`IsDiagLifts`) are global lift sequences of the scalar family with no edge: box regular on all
offsets, so jointly regular without a cut-off (`liftRegular_of_isLiftSequence`), and their lift
setup over the admissible families has the offsets `univ` (`diagLiftGenSetup`). -/

section
variable {Dm : ℕ}

/-- **Global grade-zero lifts are jointly regular** of every order `R ≤ min sX sZ`. -/
theorem liftRegular_of_isLiftSequence (D : OCData) (m : ℕ) (k : ℤ) {A : RealChain}
    (hA : A.WellSlotted) (ρ : ℝ) {Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    (hC : IsLiftSequence (diagQ D Dm m k A ρ) sX sZ t₀ t₁ N H Cc) {R : ℕ} (hRX : R ≤ sX)
    (hRZ : R ≤ sZ) :
    ∀ hh ≤ H, ∀ n, ∀ τ ∈ Icc t₀ t₁, ∀ w, LiftRegular (diagQ D Dm m k A ρ) Cc w τ hh n R := by
  intro hh hH n τ hτ w
  refine liftRegular_of D m k hA ρ (fun _ _ _ => []) w τ hh n R
    (fun hh' hh'' k' _ m' α v => ?_) (fun v u d γ hγ α c => ?_)
  · have hbox := Uniqueness.IsBoxSmooth.toOn
      (hC.2.2.2.2.2.1 hh' (hh''.trans hH) k' m' α v w τ hτ).1 univ
    have := contDiffOn_coeff_of_box isOpen_univ hbox hRX hRZ
    rw [univ_prod_univ] at this
    exact contDiffOn_univ.mp this
  · simp [familyLiftData, liftEdges] at hγ

/-- **The grade-zero lift setup.** -/
theorem diagLiftGenSetup (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (b : ℝ) (j₀ : ℕ) (𝒮 : SeedExports)
    (m : ℕ) (k : ℤ) (hk : Odd k) (ρ : ℝ) (hρ : ρ ≠ 0)
    (Cc0 : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) {sX sZ N R : ℕ}
    (hRX : R ≤ sX) (hRZ : R ≤ sZ) (hNR : N + Dm + 2 ≤ R)
    (hC : ∀ A, IsAdmissibleChain D b j₀ m k A →
      IsLiftSequence (diagQ D Dm m k A ρ) sX sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N 0 (Cc0 A)) :
    LiftGenSetup D b j₀ 𝒮 m k {A | IsAdmissibleChain D b j₀ m k A} ρ
      (fun _ => (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))) (fun _ => univ)
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N 0 Cc0 := by
  have hc : 0 < D.cellScaleSq m := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ m
  have hkap : ∀ i, 0 < D.kap i := EntryWeakProofs.weakData_kap_pos D hΛ hζ hκ
  exact
    { hζ := hζ
      hρ := hρ
      hU := fun _ _ => isOpen_univ
      hk := hk
      hA := fun _ hA => ⟨hA.2.2.1, hA.2.2.2.1⟩
      hc := hc
      h01 := EntryWeakProofs.weakData_lift_window D hΛ hζ hκ m k
      hstart := mul_div_cancel₀ _ hc.ne'
      hη := (Real.sqrt_pos.mpr (div_pos (hkap m) (hkap (m - 1)))).ne'
      hsZ := by omega
      loc := fun A hA =>
        IsLiftSequenceOn.toLocal (Uniqueness.IsLiftSequence.toOn (hC A hA) univ) subset_rfl
      edges := fun v u d α c => (UEnv.isURep_const _ 0).congr fun l _ X _ z => by
        simp [familyLiftData, liftEdges]
      reg := fun A hA hh hhH n _ hnN τ hτ w =>
        liftRegular_of_isLiftSequence D m k hA.2.2.1 ρ (hC A hA) (R := n + Dm + 2) (by omega)
          (by omega) hh hhH n τ hτ w }
end

/-! **Generation: the finer outputs of the sources are family expressions.** From the cut-off lift
setup of a path family (`CutoffLiftSetup`), the finer outputs at the label `0` of the true lift
data and lifts are denoted by family expressions on the admissible families and the pulse window
(`SlotFamRep`):
* the path means `pathMeanFlux` (`CutoffLiftSetup.slotFamRep_pathMean`, copies and mean letters),
  of every degree `n` with `n + Dm + 2 ≤ R` (letter degrees exceed the lift degree);
* the covariance letters `covLetterFlux` at any anchor `s₀` (`0` in the cascade, `t_p` at
  terminal entry) (`CutoffLiftSetup.slotFamRep_covLetter`);
* the direct transport `directFlux` of a generated stage (`slotFamRep_directFlux`).
The setup represents the cut-off data; the germ of the outputs at `0` transfers them to the true
data (`fluxCoeff_pathMeanFlux_agree`, `fluxCoeff_covLetterFlux_agree`). -/

section
variable {h Dm : ℕ} {D : OCData} {b : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)} {sX sZ N R : ℕ}

namespace CutoffLiftSetup

/-- **The path means are family expressions.** -/
theorem slotFamRep_pathMean (hset : CutoffLiftSetup D b j₀ 𝒮 m k ρ edge Cc sX sZ N R)
    (hc : 0 < D.cellScaleSq m) {n : ℕ} (hn1 : 1 ≤ n) (hnR : n + Dm + 2 ≤ R) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    SlotFamRep D b j₀ 𝒮 m k (fun t A =>
      fluxCoeff (pathMeanFlux D m ρ (familyLiftData D m k A ρ (edge A)) (Cc A) n t) d I 0 κ) := by
  obtain ⟨edge', Cc', U, hS, hU⟩ := hset
  obtain ⟨c, hc'⟩ := hS.pathMeanFlux_famRep' (fun A hA => (hU A hA).2.1) le_rfl hn1
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ hnR τ hτ 0) d I κ
  refine (SlotFamRep.of_famURep hc hc').congr fun A hA t _ => ?_
  obtain ⟨hO, h0, -, hag, hCeq, -⟩ := hU A hA
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [Uniqueness.fluxCoeff_pathMeanFlux_agree D m ρ hag (Cc A) (Cc' A) n t hO h0
    (fun hh' _ n' m' α X hX => (hCeq hh' n' m' α _ X hX).symm) d I]

/-- **The covariance letters are family expressions** (any anchor `s₀`, cascade diffusivities,
reserve `2a + Dm + 2 ≤ R`). -/
theorem slotFamRep_covLetter (hset : CutoffLiftSetup D b j₀ 𝒮 m k ρ edge Cc sX sZ N R)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hc : 0 < D.cellScaleSq m) (s₀ : ℝ) {n : ℕ}
    (hn1 : 1 ≤ n)
    (hnR : n + Dm + 2 ≤ R)
    (a a' : ℕ) (ha : 2 * a + Dm + 2 ≤ R) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1)) (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    SlotFamRep D b j₀ 𝒮 m k (fun t A =>
      fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k A ρ (edge A)) (Cc A) n a a' t A)
        d I 0 κ) := by
  obtain ⟨edge', Cc', U, hS, hU⟩ := hset
  obtain ⟨c, hc'⟩ := hS.covLetter_famRep (fun A hA => (hU A hA).2.1) le_rfl hn1
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ hnR τ hτ 0) a a' (s₀ := s₀) hΛ hκ hκ'
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ ha τ hτ 0) d I κ
  refine (SlotFamRep.of_famURep hc hc').congr fun A hA t _ => ?_
  obtain ⟨hO, h0, -, hag, hCeq, -⟩ := hU A hA
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [fluxCoeff_covLetterFlux_agree D m ρ s₀ hag (Cc A) (Cc' A) n a a' t A hO h0
    ⟨(contDiff_famMapInv A t).continuous.continuousAt, famMapInv_zero hζ A t⟩
    (fun hh' _ n' m' α X hX => (hCeq hh' n' m' α _ X hX).symm) d I]

end CutoffLiftSetup
end

/-! **Generation: the finer outputs of the non-diagonal sources are family expressions.** For a
generated stage `G` of level `m` whose old fluxes at the offset `0` are continuous in the fast
variable, and an odd slot `k`, the finer output `fluxCoeff (s.fluxOp ρ 0 Cc k t A) d I 0 κ` of a
source `s` is denoted by a family expression on the admissible families and the pulse window
(`SlotFamRep`):
* the direct copies `copyDir` (`directFlux_famRep`);
* the quadratic copies `copyQuad` and the mean letters `letterMean` (path means of the cut-off lift
  setup, minus the direct part for a one-step path);
* the covariance letters `letterCov` (any anchor `s₀`: `0` in the cascade, `t_p` at terminal
  entry).
The path sources take the cut-off lift setup of their path family at the slot `k`
(`CutoffLiftSetup`), with the reserve `R` covering the letter degree. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The old fluxes of `G` at the offset `0` are continuous in the fast variable on the pulse
windows. -/
def OldFluxContinuous (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) v u (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)), ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
    Continuous fun z => G.fam.flux p c v u γ d I t 0 z

open scoped Classical in
omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The direct transport is a family expression.** -/
theorem slotFamRep_directFlux (hζ : IsFastProfile D.ζ) (G : GenStage D hr Dm b j₀)
    (hG : G.IsGenerated) (hcont : OldFluxContinuous G) {k : ℤ} (hk : Odd k)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ) (hords : ∀ d' ∈ ords, 1 ≤ d')
    {d : ℕ} (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    SlotFamRep D b j₀ G.exports G.level k (fun t A =>
      if hA : IsAdmissibleChain D b j₀ G.level k A then
        fluxCoeff (directFlux G ⟨k, hk⟩ ⟨A, hA⟩ γ ords t) d I 0 κ else 0) := by
  obtain ⟨c, hs, hf, fc, hd', hv⟩ := directFlux_famRep hζ G hG ⟨k, hk⟩ γ ords hords hd I κ
    (fun _ cc t ht σ => integrableOn_unitCube_of_continuous (hcont ⟨k, hk⟩ cc v u γ d (I ∘ σ) t ht))
  exact ⟨c, hs, hf, fc, hd', fun A hA t ht => by
    simp only [hA, ↓reduceDIte]
    exact (hv ⟨A, hA⟩ t ht).symm⟩

namespace SuccSourceG1

variable {G : GenStage D hr Dm b j₀}

/-- The cut-off lift setup of the path family of a source at the odd slot `k` (no condition for
the sources without a path). -/
def HasSetup (s : SuccSource G) (ρ : ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) (k : ℤ)
    (hk : Odd k) (sX sZ N R : ℕ) : Prop :=
  match s, Cc with
  | .copyQuad _ _ π, Cc | .letterMean _ _ _ π, Cc | .letterCov _ _ _ _ _ π, Cc =>
      CutoffLiftSetup D b j₀ G.exports G.level k ρ (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N R
  | .copyDir .., _ | .letterDiag .., _ => True

/-- The reserve `R` covers the degree (and the covariance order) of the source. -/
def Reserve (s : SuccSource G) (R : ℕ) : Prop :=
  match s with
  | .copyQuad .. => 2 + Dm + 2 ≤ R
  | .letterMean _ n _ _ => 1 ≤ n ∧ n + Dm + 2 ≤ R
  | .letterCov _ n _ a _ _ => 1 ≤ n ∧ n + Dm + 2 ≤ R ∧ 2 * a + Dm + 2 ≤ R
  | .copyDir .. | .letterDiag .. => True

end SuccSourceG1

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The finer output of a non-diagonal source is a family expression.** -/
theorem slotFamRep_fluxOp (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (G : GenStage D hr Dm b j₀)
    (hc : 0 < D.cellScaleSq G.level) (hκ : D.kap G.level = D.κ G.level)
    (hκ' : D.kap (G.level - 1) = D.κ (G.level - 1)) (hG : G.IsGenerated)
    (hcont : OldFluxContinuous G) (ρ s₀ : ℝ) (s : SuccSource G) (hnd : ¬ s.IsDiag)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) {k : ℤ}
    (hk : Odd k) {sX sZ N R : ℕ} (hset : SuccSourceG1.HasSetup s ρ Cc k hk sX sZ N R)
    (hres : SuccSourceG1.Reserve s R) {d : ℕ} (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1))
    (κ : Fin 2) :
    SlotFamRep D b j₀ G.exports G.level k (fun t A =>
      fluxCoeff (s.fluxOp ρ s₀ Cc k t A) d I 0 κ) := by
  have hadm : ∀ A, IsAdmissibleChain D b j₀ G.level k A →
      (IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) := fun A hA => ⟨hA, hk⟩
  cases s with
  | copyDir t' v u γ =>
    refine (slotFamRep_directFlux hζ G hG hcont hk γ (Finset.Icc 3 Dm)
      (fun d' hd' => by simp only [Finset.mem_Icc] at hd'; omega) hd I κ).congr
      fun A hA t _ => ?_
    simp only [SuccSource.fluxOp, hadm A hA, and_self, ↓reduceDIte]
  | letterDiag t' u => exact absurd trivial hnd
  | copyQuad t' h π =>
    refine (CutoffLiftSetup.slotFamRep_pathMean hset hc (n := 2) (by omega) hres d I κ).congr
      fun A hA t _ => ?_
    simp only [SuccSource.fluxOp, hadm A hA, and_self, ↓reduceDIte,
      pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
  | letterMean t' n h π =>
    obtain ⟨hn1, hnR⟩ := hres
    have hPM := CutoffLiftSetup.slotFamRep_pathMean hset hc hn1 hnR d I κ
    by_cases hh : h = 1
    · subst hh
      have hDF := slotFamRep_directFlux hζ G hG hcont hk (π.step ⟨0, by omega⟩).2.2 {n}
        (fun d' hd' => by simp only [Finset.mem_singleton] at hd'; omega) hd I κ
      refine (hPM.sub hDF).congr fun A hA t _ => ?_
      simp only [SuccSource.fluxOp, hadm A hA, and_self, ↓reduceDIte,
        pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
      unfold fluxCoeff
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · refine hPM.congr fun A hA t _ => ?_
      simp only [SuccSource.fluxOp, hadm A hA, and_self, ↓reduceDIte, hh,
        pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
      unfold fluxCoeff
      simp
  | letterCov t' n h a a' π =>
    obtain ⟨hn1, hnR, haR⟩ := hres
    refine (CutoffLiftSetup.slotFamRep_covLetter hset hΛ hζ hc s₀ hn1 hnR a a' haR hκ hκ' d I
      κ).congr
      fun A hA t _ => ?_
    simp only [SuccSource.fluxOp, hadm A hA, and_self, ↓reduceDIte,
      pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
    rfl
end

/-! **Generation: the non-diagonal new coefficients are generated.** For an old stage `G` that is
generated, slotwise transverse and context certified, and a valid non-diagonal source `s` of the
successor alphabet whose lifts form a lift family (`SuccSource.IsLiftFamily`, localized lifts
with the reserves `max (N + succSchedD D₀ N p H) (2p) + Dm + 2 ≤ sX, sZ`):
* the source has the cut-off lift setup of its path family at every odd slot
  (`hasSetup_of_liftFamily`), with source edges regular by holomorphy;
* the reserve covers its degree (`reserve_of_valid`);
* hence its finer outputs are family expressions, and every new edge with this source and a
  transferred coefficient is generated (`isExprFor_nonDiag`). -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The reserve covers the degree of a valid source of a successor alphabet**
`succAlphabet nMax hMax p npad` (the cascade's `succAlphabetOf`, the terminal `termAlphabet`). -/
theorem reserve_of_valid_alphabet {G : GenStage D hr Dm b j₀} {nMax hMax J p npad : ℕ}
    {A : Finset WordLetter} (hA : A = succAlphabet nMax hMax p npad) (hN : 2 ≤ nMax)
    (s : SuccSource G) (hv : s.Valid A J) :
    SuccSourceG1.Reserve s (max nMax (2 * p) + Dm + 2) := by
  subst hA
  obtain ⟨-, hl, -⟩ := hv
  cases s with
  | copyDir t' v u γ => trivial
  | letterDiag t' u => trivial
  | copyQuad t' h π =>
    show 2 + Dm + 2 ≤ _
    have : 2 ≤ max nMax (2 * p) := le_max_of_le_left hN
    omega
  | letterMean t' n h π =>
    obtain ⟨-, hA⟩ := hl _ rfl
    simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range,
      reduceCtorEq, false_or, or_false, and_false, exists_false, WordLetter.mean.injEq,
      Prod.exists] at hA
    obtain ⟨n', h', ⟨⟨hn3, hnM⟩, -⟩, hnn, -⟩ := hA
    have : n' ≤ max nMax (2 * p) := le_max_of_le_left hnM
    subst hnn
    show 1 ≤ _ ∧ _ + Dm + 2 ≤ _
    exact ⟨by omega, by omega⟩
  | letterCov t' n h a a' π =>
    obtain ⟨-, hA⟩ := hl _ rfl
    simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range,
      reduceCtorEq, false_or, or_false, and_false, exists_false, WordLetter.covariance.injEq,
      Prod.exists] at hA
    obtain ⟨n', h', a₁, a₂, ⟨⟨⟨⟨hn2, hnM⟩, -⟩, ha₁, -⟩, -⟩, hnn, -, haa, -⟩ := hA
    have h1 : n' ≤ max nMax (2 * p) := le_max_of_le_left hnM
    have h2 : 2 * a₁ ≤ max nMax (2 * p) := le_max_of_le_right (by omega)
    subst hnn haa
    show 1 ≤ _ ∧ _ + Dm + 2 ≤ _ ∧ 2 * _ + Dm + 2 ≤ _
    exact ⟨by omega, by omega, by omega⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The reserve covers the degree of a valid source of the successor alphabet.** -/
theorem reserve_of_valid {G : GenStage D hr Dm b j₀} {r₀ D₀ H J N p npad : ℕ} (hN : 2 ≤ N)
    (s : SuccSource G) (hv : s.Valid (succAlphabetOf r₀ D₀ H J N p npad) J) :
    SuccSourceG1.Reserve s (max (N + succSchedD D₀ N p H) (2 * p) + Dm + 2) :=
  reserve_of_valid_alphabet rfl (by omega) s hv

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The old fluxes are continuous in the fast variable** (from the holomorphic extensions of a
certified stage, `GenStage.OldCert`). -/
theorem oldFluxContinuous_of_cert (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ}
    (hcert : G.OldCert 𝒮 μ L Cθ) : OldFluxContinuous G := by
  intro p c v u γ d I t ht
  refine continuous_pi fun c' => ?_
  obtain ⟨θ, -, -, hcert'⟩ := hcert v u γ
  obtain ⟨f, F, hfF, -⟩ := hcert' d I c'
  obtain ⟨-, hhol, hval⟩ := hfF p
  have hsm := contDiffOn_holExtension_recenter hΛ hb hhol c.1 0 ht
  have hcz : Continuous fun z => f p t c.1 z := by
    have h1 := hsm.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id : Continuous fun z : Vec 2 => ((0 : Vec 2), z))
      (fun z => ⟨by
        show IsAdmissibleChain D b j₀ G.level p.1 (c.1.recenter D ((0 : ℝ) • (0 : Vec 2)))
        rw [zero_smul, recenter_zero D hζ]
        exact c.2, trivial⟩)
    simpa [Function.comp_def, zero_smul, recenter_zero D hζ] using h1
  have e : (fun z => G.fam.flux p c v u γ d I t 0 z c') = fun z => f p t c.1 z := by
    funext z
    rw [hval c t ht 0 z, smul_zero, recenter_zero D hζ]
    simp [c.2]
  rw [e]
  exact hcz

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The cut-off lift setups of a source** from its lift family. -/
theorem hasSetup_of_liftFamily (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) (G : GenStage D hr Dm b j₀)
    (hG : G.IsGenerated) (hT : G.IsSlotTransverse) {kI : InvConsts}
    (hcert : G.IsContextCertified kI) (Mn : SuccMenu) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc)
    (hlam : Mn.lenFactor * liftLength D G.level / D.eps (G.level - 1) ≠ 0) {R : ℕ}
    (hRX : R ≤ Mn.sX) (hRZ : R ≤ Mn.sZ) (hNR : Mn.N + Dm + 2 ≤ R) (k : ℤ) (hk : Odd k) :
    SuccSourceG1.HasSetup s (Mn.lenFactor * liftLength D G.level) Cc k hk Mn.sX Mn.sZ Mn.N R := by
  cases s with
  | copyDir t' v u γ => trivial
  | letterDiag t' u => trivial
  | copyQuad t' h π =>
    exact cutoffLiftSetup_of_path hΛ hζ hκ G hG hT π k hk _ hlam (Cc k) hRX hRZ hNR
      (fun A hA => hLF k A ⟨hA, hk⟩)
      (fun A hA τ hτ v u d γ hγ α c =>
        contDiffOn_liftedPathEdge hΛ hζ hκ hb G hcert.oldCert π k hk _ hA hτ v u d γ hγ α c R)
  | letterMean t' n h π =>
    exact cutoffLiftSetup_of_path hΛ hζ hκ G hG hT π k hk _ hlam (Cc k) hRX hRZ hNR
      (fun A hA => hLF k A ⟨hA, hk⟩)
      (fun A hA τ hτ v u d γ hγ α c =>
        contDiffOn_liftedPathEdge hΛ hζ hκ hb G hcert.oldCert π k hk _ hA hτ v u d γ hγ α c R)
  | letterCov t' n h a a' π =>
    exact cutoffLiftSetup_of_path hΛ hζ hκ G hG hT π k hk _ hlam (Cc k) hRX hRZ hNR
      (fun A hA => hLF k A ⟨hA, hk⟩)
      (fun A hA τ hτ v u d γ hγ α c =>
        contDiffOn_liftedPathEdge hΛ hζ hκ hb G hcert.oldCert π k hk _ hA hτ v u d γ hγ α c R)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **A new edge with a non-diagonal source is generated.** -/
theorem isExprFor_nonDiag (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hlev : G.level = G'.level + 1)
    (hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e)
    (hG : G.IsGenerated) (hT : G.IsSlotTransverse) {kI : InvConsts}
    (hcert : G.IsContextCertified kI) (hκm : D.kap G.level = D.κ G.level)
    (hκm' : D.kap (G.level - 1) = D.κ (G.level - 1)) (Mn : SuccMenu)
    (hlam : Mn.lenFactor * liftLength D G.level / D.eps (G.level - 1) ≠ 0) {R : ℕ}
    (hRX : R ≤ Mn.sX) (hRZ : R ≤ Mn.sZ) (hNR : Mn.N + Dm + 2 ≤ R) (s : SuccSource G)
    (hnd : ¬ s.IsDiag) (hres : SuccSourceG1.Reserve s R)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (lam : ℝ)
    (Dγ : ℕ) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hflux : 2 ≤ d → ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (t : ℝ) (X z : Vec 2),
      G'.fam.flux p ctx v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level p.1 lam Dγ
          (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc) t
          (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0) :
    ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1, G'.IsExprFor v' u' γ' d I c e := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hcont := oldFluxContinuous_of_cert hΛ hζ hb G hcert.oldCert
  refine isExprFor_of_transfer hζ hΛ hb hstart G' hexp γ' d I c lam Dγ
    (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc)
    (fun hd p ctx t X z => by rw [hflux hd p ctx t X z, hlev]) fun k hk d₁ hd₁ I₁ i₀ => ?_
  rw [← hlev]
  exact slotFamRep_fluxOp hΛ hζ G hc hκm hκm' hG hcont _ _ s hnd Cc hk
    (hasSetup_of_liftFamily hΛ hζ hκ hb G hG hT hcert Mn s Cc hLF hlam hRX hRZ hNR k hk) hres
    hd₁ I₁ i₀
end

/-! **Generation: the first-source coefficients are generated.** A new edge whose source is the first
source `𝖣` has the coefficient `C · fluxCoeff (firstSourceFlux … Cc0 …)` on the admissible
recenterings (`IsActualSuccessor`), and the first source is a context expression
(`firstSource_ctxRep`) once its premises are supplied:
* a scheduled finer slot exists (`exists_isScheduledIn`);
* the appended children with nonzero weight are admissible (`appendChild_admissible`);
* the grade-zero lifts (`IsDiagLifts`) are regular at the weighted times
  (`liftRegular_of_isLiftSequence`; the time of a nonzero weight lies in the lift window) and
  have family jets on the appended children (`LiftGenSetup.arrJetG_diagChild` with the grade-zero
  setup `diagLiftGenSetup`);
* the context strain is `C^{4p}` along the recentering (hypothesis `hSreg`).
Then every first-source edge is generated (`isExprFor_diag`). -/

section
/-- Every slot has a scheduled finer slot (the glueing cutoffs cover the time line). -/
theorem exists_isScheduledIn {D : OCData} (hΛ : 1 ≤ D.Λ) (i : ℕ) (pc : ℤ) :
    ∃ p' : ℤ, IsScheduledIn D i p' pc := by
  set τ := ocTau D.α D.q D.Λ i
  set τ' := ocTau D.α D.q D.Λ (i + 1)
  have hτ : 0 < τ := Construction.Stream.ocTau_pos hΛ
  have hτ' : 0 < τ' := Construction.Stream.ocTau_pos hΛ
  refine ⟨round ((pc : ℝ) * τ / τ'), (pc : ℝ) * τ, ?_, ?_⟩
  · show ocCutoff D.α D.q D.Λ (i + 1) _ _ ≠ 0
    unfold ocCutoff
    refine (Real.smoothTransition.pos_of_pos ?_).ne'
    have hr := abs_sub_round ((pc : ℝ) * τ / τ')
    have e : |(pc : ℝ) * τ - (round ((pc : ℝ) * τ / τ') : ℝ) * τ'| =
        |(pc : ℝ) * τ / τ' - round ((pc : ℝ) * τ / τ')| * τ' := by
      rw [← abs_of_pos hτ', ← abs_mul, abs_of_pos hτ']
      congr 1
      field_simp
    rw [e]
    change 0 < 5 / 2 - 2 * (|(pc : ℝ) * τ / τ' - round ((pc : ℝ) * τ / τ')| * τ') / τ'
    rw [mul_div_assoc, mul_div_cancel_right₀ _ hτ'.ne']
    linarith
  · change ((pc : ℝ) - 61 / 48) * τ ≤ (pc : ℝ) * τ ∧ (pc : ℝ) * τ ≤ ((pc : ℝ) + 61 / 48) * τ
    exact ⟨by rw [sub_mul]; linarith, by rw [add_mul]; linarith⟩

/-- A time of the pulse window is, in cell time, in the lift window. -/
theorem mem_liftWindow_of_mem_ocPulseWindow {D : OCData} {m : ℕ} {k : ℤ}
    (hc : 0 < D.cellScaleSq m) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) :
    (D.cellScaleSq m)⁻¹ * t ∈ Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  rw [inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right ht.1 hc.le, div_le_div_of_nonneg_right ht.2 hc.le⟩

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **A first-source edge is generated.** -/
theorem isExprFor_diag (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G' : GenStage D hr Dm b j₀) {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → G'.exports e) (ρ : ℝ) (hρ : ρ ≠ 0) {N p : ℕ}
    (hN : 1 ≤ N) {m : ℕ} (hm : m = G'.level + 1) (hκm : D.kap m = D.κ m)
    (hκm' : D.kap G'.level = D.κ G'.level) {sX sZ R : ℕ} (hRX : R ≤ sX) (hRZ : R ≤ sZ)
    (hRp : 2 * p + Dm + 2 ≤ R) (hRN : N + 1 + Dm + 2 ≤ R) {s₀ : ℝ}
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hDL : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ m k A →
      IsLiftSequence (diagQ D Dm m k A ρ) sX sZ
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)
        N 0 (Cc0 k A))
    (hSreg : ∀ (pc : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2),
      IsAdmissibleChain D b j₀ G'.level pc ch → ∀ a c,
        ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
          contextStrain D G'.level pc t (ch.recenter D y) (z + (D.eps G'.level)⁻¹ • y) a c))
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (C : ℝ) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hflux : 2 ≤ d → ∀ (q : OddSlot) (ctx : StageCtx D b j₀ G'.level q) (t : ℝ) (X z : Vec 2),
      G'.fam.flux q ctx v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (ctx.1.recenter D (D.eps (G'.level - 1) • X))
        then C • fluxCoeff (firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t
          (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z) d I 0
        else 0) :
    ∃ e : (q : OddSlot) → Gen .ctx G'.level q.1, G'.IsExprFor v' u' γ' d I c e := by
  subst hm
  classical
  by_cases hd : 2 ≤ d
  swap
  · refine ⟨fun q => Gen.time (s := .ctx) (i := G'.level) (p := q.1) (.const 0), fun q =>
      ⟨.timeConst 0, .time _, GenSort.ofTime .ctx (TimeLetter.eval D (.const 0)), .time _,
        fun ctx t _ X z => ?_⟩⟩
    rw [G'.fam.flux_zero q ctx v' u' γ' d I (fun h => hd h.1)]
    split_ifs <;> simp [GenSort.ofTime, TimeLetter.eval]
  set i := G'.level with hi
  have hc : 0 < D.cellScaleSq (i + 1) := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ _
  have hτ : ∀ k, 0 < ocTau D.α D.q D.Λ k := fun _ => Construction.Stream.ocTau_pos hΛ
  have key : ∀ q : OddSlot, ∃ e : Gen .ctx i q.1, CtxRep D b j₀ 𝒮
      (fun t ch _ => IsAdmissibleChain D b j₀ i q.1 ch ∧ t ∈ ocPulseWindow D.α D.q D.Λ i q.1)
      (fun t ch z => C * fluxCoeff (firstSourceFlux D b j₀ Dm (i + 1) ρ N p s₀ Cc0 t ch z) d I 0 c)
      e := by
    intro q
    set P : ℝ → RealChain → Vec 2 → Prop := fun t ch _ =>
      IsAdmissibleChain D b j₀ i q.1 ch ∧ t ∈ ocPulseWindow D.α D.q D.Λ i q.1 with hPdef
    have hfin := scheduledSlots_finite D i q.1 (hτ _)
    have hS : ∀ k, k ∈ hfin.toFinset ↔ Odd k ∧ IsScheduledIn D i k q.1 := fun k =>
      hfin.mem_toFinset
    obtain ⟨p', hp'⟩ := exists_isScheduledIn hΛ i q.1
    have hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = q.1 :=
      fun l => ⟨l.2.1.2.2.1, l.2.1.1, l.2.1.2.2.2.1⟩
    have hadm : ∀ l : CtxIdx P, ∀ k ∈ hfin.toFinset, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
        IsAdmissibleChain D b j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) :=
      fun l k hk hcut => appendChild_admissible D hΛ hζ hb hstart i q.1 l.1.2.1 l.2.1 k
        ((hS k).1 hk).1 ((hS k).1 hk).2 l.1.1 hcut l.1.2.2
    have hwin : ∀ k t, ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
        (D.cellScaleSq (i + 1))⁻¹ * t ∈ Icc (D.slotStart (i + 1) k / D.cellScaleSq (i + 1))
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ (i + 1)) / D.cellScaleSq (i + 1)) :=
      fun k t hcut => mem_liftWindow_of_mem_ocPulseWindow hc
        (mem_ocPulseWindow_of_ocCutoff_ne_zero (hτ _) hcut)
    have hreg : ∀ l : CtxIdx P, ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ hfin.toFinset,
        IsAdmissibleChain D b j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) →
        ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
        LiftRegular (diagQ D Dm (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) ρ)
          (Cc0 k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) (0 : Fin 1)
          ((D.cellScaleSq (i + 1))⁻¹ * l.1.1) 0 n (2 * p + Dm + 2) :=
      fun l n _ _ k hk hA hcut => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ
        (hDL k _ ((hS k).1 hk).1 hA) (R := 2 * p + Dm + 2) (by omega) (by omega) 0 le_rfl n _
        (hwin k _ hcut) 0
    have hchild : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ hfin.toFinset, ∀ c',
        ArrJetG (famAlg D b j₀ 𝒮 (i + 1) k (childW D i k P)) (2 * p)
          (fun q' => diagChildArr D Dm (i + 1) ρ Cc0 k n q'.1.1 q'.1.2 c') := by
      intro n hn2 hnN k hk c'
      have hkodd := ((hS k).1 hk).1
      have hset := diagLiftGenSetup D hΛ hζ hκ b j₀ 𝒮 (i + 1) k hkodd ρ hρ (Cc0 k) hRX hRZ
        (by omega) (fun A hA => hDL k A hkodd hA)
      have hmax : max (2 * p) n + Dm + 2 ≤ R := by
        have := max_le (show 2 * p ≤ R - Dm - 2 by omega) (show n ≤ R - Dm - 2 by omega)
        omega
      refine hset.arrJetG_diagChild (fun _ _ => trivial) (by omega : 1 ≤ n) (2 * p)
        (fun A hA τ hτ' => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ (hDL k A hkodd hA)
          (R := max (2 * p) n + Dm + 2) (by omega) (by omega) 0 le_rfl n τ hτ' 0) ?_ c'
      rintro ⟨t, A⟩ ⟨t', ch, z, hPz, hcut, heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨hadm ⟨(t, ch, z), hPz⟩ k hk hcut, hwin k t hcut⟩
    obtain ⟨e, he⟩ := firstSource_ctxRep hζ hρ hΛ hN (s₀ := s₀)
      (hκm ▸ kap_pos_of_cellScaleSq_pos D hc) hκm hκm' hfin.toFinset hS hp'
      hP hadm (fun l a c' => hSreg q.1 l.1.1 l.1.2.1 l.1.2.2 l.2.1 a c') hreg hchild d I c
    exact ⟨_, (CtxRep.const C).mul he⟩
  choose e he using key
  refine ⟨e, fun q => ?_⟩
  obtain ⟨hs, hf, f, hden, hv⟩ := he q
  refine ⟨hs, fromSeed_mono hexp hf, f, hden, fun ctx t ht X z => ?_⟩
  rw [hflux hd q ctx t X z]
  split_ifs with hadm
  · rw [hv t _ z ⟨hadm, ht⟩]
    simp only [Pi.smul_apply, smul_eq_mul, hi]
  · rfl
end

end AVRegularity.Providers.GenSem
end
end

section
section
/-! **Generation, one successor step: every new coefficient is generated** (`successorGeneration_isExprFor`). For a
generated, slotwise transverse, context-certified stage `G` of a cascade level `≤ M` and an actual
successor `G'` at the successor menus with the standard reserves, every new edge,
order, word and component of `G'` has scheduled, seed-provenanced expressions (`IsExprFor`):
the non-diagonal sources through the transfer of their finer outputs (`isExprFor_nonDiag`), the
first source through `firstSource_ctxRep` (`isExprFor_diag`). The context strain regularity is a
hypothesis here (`hSreg`). -/

@[expose] public noncomputable section

open Set Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.Providers.GenSem

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {b : ℝ} {j₀ : ℕ}

theorem kap_eq_of_le_term (D : OCData) {m : ℕ} (hm : m ≤ D.term) : D.kap m = D.κ m := by
  unfold OCData.kap
  rw [min_eq_left hm]

theorem one_le_succSchedD_succ (D₀ N p g : ℕ) : 1 ≤ succSchedD D₀ N p (g + 1) := by
  simp only [succSchedD]
  omega

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **Generation, one successor step at any menu: the new coefficients are generated.** The menu has
the alphabet `succAlphabet nMax hMax p npad` (the cascade's `succAlphabetOf`, the terminal
`termAlphabet`), any covariance anchor (`0` in the cascade, `t_p` at terminal entry), a nonzero
length factor (`1`, `c_r`), and lift reserves `max nMax (2p) + Dm + 2`. -/
theorem successorGeneration_isExprFor_menu (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {P : ProvParams} {Dm : ℕ} (Mn : SuccMenu) {nMax hMax npad : ℕ}
    (hA : Mn.A = succAlphabet nMax hMax Mn.p npad) (hN : 2 ≤ Mn.N) (hNn : Mn.N + 1 ≤ nMax)
    (hsX : max nMax (2 * Mn.p) + Dm + 2 ≤ Mn.sX) (hsZ : max nMax (2 * Mn.p) + Dm + 2 ≤ Mn.sZ)
    (hlen : Mn.lenFactor ≠ 0)
    (G G' : GenStage D hr Dm b j₀) (hG : G.IsGenerated)
    (hT : G.IsSlotTransverse) {kI : InvConsts} (hcert : G.IsContextCertified kI)
    (hterm : G.level ≤ D.term) (hSucc : IsActualSuccessor D P Mn G G')
    (hSreg : ∀ (pc : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2),
      IsAdmissibleChain D b j₀ G'.level pc ch → ∀ a c,
        ContDiff ℝ ((4 * Mn.p : ℕ) : WithTop ℕ∞) (fun y =>
          contextStrain D G'.level pc t (ch.recenter D y) (z + (D.eps G'.level)⁻¹ • y) a c)) :
    ∀ v' u' (γ' : G'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (q : OddSlot) → Gen .ctx G'.level q.1, G'.IsExprFor v' u' γ' d I c e := by
  obtain ⟨hlev1, hlev', -, -, -, hexpIff, e, Cc, Cc0, hLF, hDL, hfl⟩ := hSucc
  intro v' u' γ' d I c
  have hlevG : G.level = G'.level + 1 := by omega
  have hNR : Mn.N + Dm + 2 ≤ max nMax (2 * Mn.p) + Dm + 2 := by
    have : Mn.N ≤ max nMax (2 * Mn.p) := le_max_of_le_left (by omega)
    omega
  have hexp : ∀ {i q} (e' : Gen .ctx i q), G.exports e' → G'.exports e' :=
    fun e' h => (hexpIff _ _ e').mpr h
  have hκm : D.kap G.level = D.κ G.level := kap_eq_of_le_term D hterm
  have hκm' : D.kap (G.level - 1) = D.κ (G.level - 1) := kap_eq_of_le_term D (by omega)
  have hρpos : 0 < liftLength D G.level := by
    unfold liftLength
    exact Real.sqrt_pos.mpr (mul_pos (CycleReference.bandChain_pos hΛ hζ hκ (by omega))
      (Construction.Stream.ocTauPP_pos hΛ))
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  obtain ⟨-, -, hnd, hdg⟩ := hfl v' u' γ'
  by_cases hdiag : (e v' u' γ').1.IsDiag
  · -- the first source
    have hflux := hdg hdiag
    have hκG' : D.kap G'.level = D.κ G'.level := kap_eq_of_le_term D (by omega)
    exact isExprFor_diag hΛ hζ hκ hb hstart G' (𝒮 := G.exports) hexp
      (Mn.lenFactor * liftLength D G.level) (mul_ne_zero hlen hρpos.ne') (N := Mn.N)
      (p := Mn.p) (by omega) hlevG hκm hκG' hsX hsZ
      (by have : 2 * Mn.p ≤ max nMax (2 * Mn.p) := le_max_right _ _; omega)
      (by have : Mn.N + 1 ≤ max nMax (2 * Mn.p) := le_max_of_le_left hNn; omega)
      Cc0 (fun k A hk hA => hDL k A hk hA) hSreg γ'
      ((e v' u' γ').1.lam G.level Mn.η0 * (D.κ G'.level * D.eps G'.level ^ (d - 2))⁻¹) d I c
      (fun hd q ctx t X z => hflux q ctx d I t X z hd)
  · -- a non-diagonal source
    exact isExprFor_nonDiag hΛ hζ hκ hb hstart G G' hlevG hexp hG hT hcert hκm hκm' Mn
      (div_ne_zero (mul_ne_zero hlen hρpos.ne') hε) hsX hsZ hNR
      (e v' u' γ').1 hdiag (reserve_of_valid_alphabet hA (by omega) _ (e v' u' γ').2.1) (Cc (e v' u' γ').1)
      (hLF (e v' u' γ').1) γ' _ _ d I c
      (fun hd q ctx t X z => hnd hdiag q ctx d I t X z hd)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **Generation, one successor step: the new coefficients are generated** (the cascade menu). -/
theorem successorGeneration_isExprFor (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {P : ProvParams} {Mnat r₀ D₀ H J N p npad sX sZ : ℕ} {η₀ : ℝ} (hN : 2 ≤ N) (hH : 1 ≤ H)
    (hsX : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX)
    (hsZ : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ)
    (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) b j₀) (hG : G.IsGenerated)
    (hT : G.IsSlotTransverse) {kI : InvConsts} (hcert : G.IsContextCertified kI)
    (hterm : G.level ≤ D.term)
    (hSucc : IsActualSuccessor D P (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀) G G')
    (hSreg : ∀ (pc : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2),
      IsAdmissibleChain D b j₀ G'.level pc ch → ∀ a c,
        ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
          contextStrain D G'.level pc t (ch.recenter D y) (z + (D.eps G'.level)⁻¹ • y) a c)) :
    ∀ v' u' (γ' : G'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (q : OddSlot) → Gen .ctx G'.level q.1, G'.IsExprFor v' u' γ' d I c e := by
  have hsched1 : 1 ≤ succSchedD D₀ N p H := by
    obtain ⟨g, hg⟩ : ∃ g, H = g + 1 := ⟨H - 1, by omega⟩
    rw [hg]
    exact one_le_succSchedD_succ D₀ N p g
  exact successorGeneration_isExprFor_menu hΛ hζ hκ hb hstart (succMenu Mnat r₀ D₀ H J N p npad sX sZ η₀)
    (nMax := N + succSchedD D₀ N p H) (hMax := succSchedR r₀ J H) (npad := npad) rfl hN
    (by show N + 1 ≤ N + succSchedD D₀ N p H; omega) hsX hsZ one_ne_zero G G' hG hT hcert
    hterm hSucc hSreg

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation at terminal entry** (the terminal successor `Gt'` of the weak stage `Gw`). The
terminal menu `termMenu` has the alphabet `termAlphabet N_T p_T D_W d_W =
succAlphabet (N_T + D_W) d_W p_T 0`, one grade (`H = 1`), the covariance anchor `t_p` and the
length factor `c_r`. Generation at any menu (`successorGeneration_isExprFor_menu`,
`successor_slotTransverse_of_exports`) applies:
* the weak stage is generated, slotwise transverse and context certified (its stage invariant);
* its exports are slotwise parallel invariant (`HasCertifiedExports`);
* its level `M` is the terminal level;
* the context strain along recentering is `C^∞` (`contDiff_contextStrain_recenter`);
* the start bound of the appended children comes from a carrier start with `1 ≤ CH`, `1 ≤ Υ`.

Special cases: a successor without identities is vacuously generated and transverse; `D_W = 1`
gives `N_T + 1 ≤ N_T + D_W`, the reserve of the first source. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.Providers.GenSem

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Generation at terminal entry: the coefficients of the terminal successor are generated, and it
is slotwise structurally transverse.** -/
theorem terminalSuccessor_generation (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) {CH Υ : ℝ} (hCH : 1 ≤ CH)
    (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {M : ℕ} (hterm : D.term = M)
    {law : BirthLaw} {P : ProvParams} {φ₀ : Vec 2 → ℝ} {hφ₀ : MeasureTheory.Integrable φ₀}
    {Mnat Jw dW DW : ℕ} {nW : ℕ+} {kW : InvConsts} {a T₀ σw CL Cχ χw aM : ℝ}
    {Gw Gt' : GenStage D ScalarH Dm b j₀}
    (hw : IsWeakStage law P φ₀ hφ₀ M Mnat Jw dW DW nW kW a T₀ σw CL Cχ χw Gw aM)
    {Pt : ProvParams} {Mt RT NT pT DWt dWt sX sZ : ℕ} {η₀ tp cr : ℝ} (hN : 2 ≤ NT)
    (hDW : 1 ≤ DWt) (hcr : cr ≠ 0) (hsX : max (NT + DWt) (2 * pT) + Dm + 2 ≤ sX)
    (hsZ : max (NT + DWt) (2 * pT) + Dm + 2 ≤ sZ)
    (hSucc : IsActualSuccessor D Pt
      (termMenu Mt (termAlphabet NT pT DWt dWt) RT NT pT sX sZ η₀ tp cr) Gw Gt') :
    (∀ v' u' (γ' : Gt'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (q : OddSlot) → Gen .ctx Gt'.level q.1, Gt'.IsExprFor v' u' γ' d I c e) ∧
      Gt'.IsSlotTransverse := by
  obtain ⟨-, -, hlev, -, -, ⟨-, hexpw, -⟩, -, -, -, hinv⟩ := hw
  obtain ⟨-, -, hG, -, hT, hcert, -⟩ := hinv
  have hstart := startBound_of_carrierStart hΛ hCH hΥ hcar
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hSreg : ∀ (pc : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2),
      IsAdmissibleChain D b j₀ Gt'.level pc ch → ∀ a c,
        ContDiff ℝ ((4 * pT : ℕ) : WithTop ℕ∞) (fun y =>
          contextStrain D Gt'.level pc t (ch.recenter D y) (z + (D.eps Gt'.level)⁻¹ • y) a c) :=
    fun pc t ch z hA a c =>
      (contDiff_contextStrain_recenter D hζ Gt'.level pc t ch hA.2.2.1 z a c).of_le
        (htop (4 * pT))
  have hE := successorGeneration_isExprFor_menu hΛ hζ hκ hb hstart
    (termMenu Mt (termAlphabet NT pT DWt dWt) RT NT pT sX sZ η₀ tp cr)
    (nMax := NT + DWt) (hMax := dWt) (npad := 0) rfl hN
    (by show NT + 1 ≤ NT + DWt; omega) hsX hsZ hcr Gw Gt' hG hT hcert
    (by rw [hlev, hterm]) hSucc hSreg
  exact ⟨hE, successor_slotTransverse_of_exports hΛ hζ hb hstart
    (fun i p e he f hd => (hexpw.1 i p e he).2.1 f hd) hSucc hE⟩

end AVRegularity.Providers.GenSem
end
end
end
