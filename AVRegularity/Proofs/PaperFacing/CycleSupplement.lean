-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.CascadeCyclePassage
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleJoint.PeriodizedCarrierRawReadout

/-! # The cycle supplement: one cycle with a free history start, and the passage bounds

At the parameters `P : PaperParameters` and `m₀ = paperBottom P`, with `E = ε_{m-1}`, `e = ε_m`,
`η₀ = succEta0`, `K = paperRepOrder`, `‖f‖_G = weightedNorm 1 π d f`, and the radius
`ρ(m) = (κ_{m-1} h_m)^{1/2} = ocRh α q Λ m κ_{m-1}`:

* `PaperPassageSupplement` (the further properties of a cycle and the profile bounds), for the same
  `G`, `Gr`, `t_pr`, `Π` as one cycle and one passage: (i) `‖𝖱‖ ≤ 1 + CE^{5η₀/4}`;
  `‖Πf‖_{G;ρ(m),N_out} ≤ C‖f‖_G` for every datum `f` (part (a) of one cycle at `ρ(m)`); and, for
  every datum `f`, every solution `U` of `G` from `f` at `t_c` and every solution `Y` of `Gr` from
  the retained trace of `Πf` at `t_pr`: (ii) the order-`N_aux` solution `Y^{(N_aux)}` from the same
  trace, whose truncation is `Y`, has `‖Y^{(N_aux)}(t)‖_{G';ρ(m),N_aux} ≤ C‖f‖_G` on `[t_pr, t_f]`;
  for all `C^{K+N+2p+2}` representatives of `U`, `Y`, every actual lift and every `t ∈ [t_pr, t_f]`:
  (iii) the jets of order `2(K+2)` of `U(t)` and of `Y^♯(t) = T P_p 𝖱 Y(t)` at `ρ_⋆(m)` are at most
  `C‖f‖_G`; (P1) `X_E(𝖱(P_p - I)SY) ≤ CE^{δ-2σ₀}[Y]`, (P2) `X_e((T - I)P_p𝖱SY) ≤ CE^{μ_s}[Y]`, (P3)
  `X_E(𝖱(P_p - I)(I - S)Y) + X_e((T - I)P_p𝖱(I - S)Y) ≤ CE²‖f‖_G`, (P4) `X_e(U - Y^♯) ≤ CE²‖f‖_G`.
* `PaperStepStatementAt`: one cycle with a free history start (`PaperCycleConclusionAt`), one
  passage and the supplement, under one existential `(t_pr, Π)`.
* `paper_step_of_step_at`: `PaperStepStatement` is the case `t_A = t_c - 3τ_m`.
* `paper_cascade_at_of_parameters`, `paper_cascade_cycle_passage_at`: the cascade, one cycle and
  one passage with `PaperStepStatementAt`; `paper_cascade_cycle_passage_order`: the same at
  parameters whose invariant order is at least a prescribed function of the schedule.
* `paper_weightedNorm_scale_le`, `paper_weightedNorm_mono_radius`: the radius comparisons of the
  weighted norms (for the bound (ii) at `ρ(m)` from the one at `c_r ρ(m)`).
* `PaperPreparationFrame`, `PaperPreparationBundleStatement`,
  `paper_preparation_bundle_of_parameters`: the preparation of Proposition 11.1 of the paper (the
  common preparation, the delay `t_c + ρ_⋆(m)²/κ_m ≤ t_pr`, the quiet margin) together with one
  cycle, one passage and the supplement, for one `(t_pr, Π)`; `paper_step_at_of_preparation_bundle`:
  the bundle gives `PaperStepStatementAt`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-- **Supplement to one passage**: the bounds (i)-(iii) (Proposition 13.1(i), Proposition 12.10(i),
and the bounds of Proposition 13.1(ii) and Proposition 12.10(ii) of the paper), the profile bounds
(P1)-(P4) and the bound `‖Πf‖_{G;ρ(m),N_out} ≤ C‖f‖_G` (Proposition 11.1(iv) of the paper), for
the same `G`, `Gr`, `tp`, `Preg` as one cycle and one passage. The bound (ii) and the bound of `Πf`
are at the radius `ρ(m) = (κ_{m-1} h_m)^{1/2}`. -/
def PaperPassageSupplement (cfg : FiniteParameters) (C : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  -- (i)
  ‖readoutCLM m (D.eps (m - 1)) (succEta0 cfg.α cfg.q cfg.s) (G.mass law) (Gr.mass law)‖ ≤
      1 + C * D.eps (m - 1) ^ (5 * succEta0 cfg.α cfg.q cfg.s / 4) ∧
  -- part (a) of one cycle at the radius `ρ(m)`: `‖Πf‖_{G;ρ(m),N_out} ≤ C‖f‖_G`
  (∀ f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root),
    weightedNorm (ocRh D.α D.q D.Λ m (D.κ (m - 1))) (G.mass law) (G.marker law) (Preg f) ≤
      C * weightedNorm 1 (G.mass law) (G.marker law) f) ∧
  ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
  ∀ (Y0 : ∀ v : CompIn Gr.comps, TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0 →
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    -- (ii), at the radius `ρ(m) = (κ_{m-1} h_m)^{1/2}`
    (∃ (YN0 : ∀ v : CompIn Gr.comps, TorusHk cfg.Naux (ScalarH v.1.root))
        (YN : ∀ v : CompIn Gr.comps, ℝ → TorusHk cfg.Naux (ScalarH v.1.root))
        (YNw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (cfg.Naux + 1) (ScalarH v.1.root))
        (YNk : ∀ v u (_ : Gr.fam.Γ v u), ℝ →
          TorusHk (cfg.Naux + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      IsRetainedTrace G Gr m cfg.p tp (Preg f) YN0 ∧
      Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
        (streamVel (D.Φ (m - 1))) cfg.Naux tp tf YN0 (fun _ _ => 0) (fun _ _ => 0) YN YNw YNk ∧
      (∀ v, ∀ t ∈ Set.Icc tp tf, truncateTorusHk (Nat.zero_le cfg.Naux) (YN v t) = Y v t) ∧
      ∀ t ∈ Set.Icc tp tf,
        weightedNorm (hr := ScalarH) (k := cfg.Naux) (ocRh D.α D.q D.Λ m (D.κ (m - 1)))
            (Gr.mass law) (Gr.marker law) (fun v => YN v t) ≤
          C * weightedNorm 1 (G.mass law) (G.marker law) f) ∧
    ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc tp tf,
        IsSmoothRep (fun v => U v t) (aU t) (paperRepOrder cfg + cfg.N + 2 * cfg.p + 2)) →
      (∀ t ∈ Set.Icc tp tf,
        IsSmoothRep (fun v => Y v t) (aY t) (paperRepOrder cfg + cfg.N + 2 * cfg.p + 2)) →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m cfg.N (succSchedR (paperDepthBound cfg) cfg.J cfg.H) cfg.sX cfg.sZ CcT →
    ∀ t ∈ Set.Icc tp tf,
      -- (iii)
      (∃ Un Uh : ∀ v : CompIn G.comps, TorusHk (2 * (paperRepOrder cfg + 2)) (ScalarH v.1.root),
        (∀ v, (Un v).toFunction.jet (valueIndex2 (2 * (paperRepOrder cfg + 2)))
            =ᵐ[volume.restrict AVenhance.unitCube] fun x => aU t x v) ∧
        (∀ v, (Uh v).toFunction.jet (valueIndex2 (2 * (paperRepOrder cfg + 2)))
            =ᵐ[volume.restrict AVenhance.unitCube] fun x => passageLift D m cfg.N
              (succSchedR (paperDepthBound cfg) cfg.J cfg.H) CcT
              (fieldCov D m cfg.p (fieldReadout m (D.eps (m - 1)) (succEta0 cfg.α cfg.q cfg.s) aY))
              t x v) ∧
        weightedNorm (rhoStar D cfg.kI.c₀ m) (G.mass law) (fun _ => 1) Un +
            weightedNorm (rhoStar D cfg.kI.c₀ m) (G.mass law) (fun _ => 1) Uh ≤
          C * weightedNorm 1 (G.mass law) (G.marker law) f) ∧
      -- (P1), (P2), (P3), (P4)
      (let E := D.eps (m - 1)
       let e := D.eps m
       let prof := (passageProfiles D law G Gr m cfg.p cfg.N
         (succSchedR (paperDepthBound cfg) cfg.J cfg.H) (succEta0 cfg.α cfg.q cfg.s) cfg.φ₀
         (freshK (m - 1)) CcT aU aY).map fun q => q.1 t
       let YE := profileSeminorm E (paperRepOrder cfg) cfg.s (compField (Gr.mass law) (aY t))
       profileNorm E (paperRepOrder cfg) cfg.s (prof.getD 0 0) ≤
          ENNReal.ofReal (C * E ^ (ocDelta cfg.α cfg.q - 2 * cfg.σ₀)) * YE ∧
       profileNorm e (paperRepOrder cfg) cfg.s (prof.getD 1 0) ≤
          ENNReal.ofReal (C * E ^ ocMuS cfg.α cfg.q cfg.s) * YE ∧
       profileNorm E (paperRepOrder cfg) cfg.s (prof.getD 2 0) +
          profileNorm e (paperRepOrder cfg) cfg.s (prof.getD 3 0) ≤
          ENNReal.ofReal (C * E ^ (2 : ℝ) * weightedNorm 1 (G.mass law) (G.marker law) f) ∧
       profileNorm e (paperRepOrder cfg) cfg.s (prof.getD 4 0) ≤
          ENNReal.ofReal (C * E ^ (2 : ℝ) * weightedNorm 1 (G.mass law) (G.marker law) f))

/-- **One cycle, one passage and the supplement** with a free history start `t_A`, at the parameters
`cfg`, bottom level `m₀` and constant `C`: for every admissible family `G` of level `m > m₀` on
`[t_A, t_f]` with `t_A + 3τ_m ≤ t_c` and `t_c + 4τ''_m ≤ t_f` and every actual successor, one
preparation `(t_pr, Π)` gives all three conclusions. -/
def PaperStepStatementAt (cfg : FiniteParameters) (m₀ : ℕ) (C : ℝ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (m : ℕ), m₀ < m →
  ∀ (tA tc tf : ℝ) (G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    IsPaperFamily cfg M Mnat law seedK freshK G m tA tf →
    tA + 3 * ocTau cfg.α cfg.q cfg.Λ m ≤ tc →
    tc + 4 * ocTauPP cfg.α cfg.q cfg.Λ m ≤ tf →
    IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G' →
  ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))),
    PaperCycleConclusionAt cfg C M Mnat law seedK freshK m tA tc tp tf G
      (G'.retained m cfg.H cfg.J) Preg ∧
    PaperPassageConclusion cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J) Preg ∧
    PaperPassageSupplement cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J) Preg

/-- The weighted norm at the radius `Aρ`, `A ≥ 1`, is at most `A^k` times the one at `ρ`. -/
theorem paper_weightedNorm_scale_le {S : Finset Comp} {k : ℕ} (ρ A : ℝ) (hA : 1 ≤ A)
    (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) :
    weightedNorm (A * ρ) π w X ≤ A ^ k * weightedNorm ρ π w X := by
  unfold weightedNorm massNormSq
  have hw : ∀ v, 0 ≤ (π v / w v ^ 2)⁻¹ :=
    fun v => inv_nonneg.mpr (div_nonneg (hπ v).le (sq_nonneg _))
  have hAk : 0 ≤ A ^ k := pow_nonneg (zero_le_one.trans hA) k
  rw [← Real.sqrt_sq hAk, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have h := Construction.Preservation.FullLift.factorialNormSq_mul_radius_le hA ρ (X v).val
  have hpow : (A ^ k) ^ 2 = A ^ (2 * k) := by rw [← pow_mul, mul_comm]
  rw [hpow, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h (hw v)

/-- The weighted norm grows with the radius. -/
theorem paper_weightedNorm_mono_radius {S : Finset Comp} {k : ℕ} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ≤ R) (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) :
    weightedNorm r π w X ≤ weightedNorm R π w X := by
  unfold weightedNorm massNormSq
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun v _ => ?_
  exact mul_le_mul_of_nonneg_left (CycleJointProofs.factorialNormSq_mono_radius hr hrR _)
    (inv_nonneg.mpr (div_nonneg (hπ v).le (sq_nonneg _)))

/-- The norm at the radius `ρ(m)` from the one at `c_r ρ(m) = rhoEnh D c_r m`: since
`ρ(m) ≤ A c_r ρ(m)` for `A = max{1, c_r⁻¹}`, it costs the factor `A^k`. -/
private theorem paper_weightedNorm_ocRh_le {S : Finset Comp} {k : ℕ} (D : OCData) {cr : ℝ}
    (hcr : 0 < cr) (m : ℕ) (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) :
    weightedNorm (ocRh D.α D.q D.Λ m (D.κ (m - 1))) π w X ≤
      max 1 cr⁻¹ ^ k * weightedNorm (rhoEnh D cr m) π w X := by
  have hA : 1 ≤ max 1 cr⁻¹ := le_max_left _ _
  have hAc : 1 ≤ max 1 cr⁻¹ * cr :=
    (inv_mul_cancel₀ hcr.ne').symm.le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hcr.le)
  have hρ : 0 ≤ ocRh D.α D.q D.Λ m (D.κ (m - 1)) := Real.sqrt_nonneg _
  have hle : ocRh D.α D.q D.Λ m (D.κ (m - 1)) ≤ max 1 cr⁻¹ * rhoEnh D cr m := by
    change _ ≤ max 1 cr⁻¹ * (cr * ocRh D.α D.q D.Λ m (D.κ (m - 1)))
    rw [← mul_assoc]
    exact le_mul_of_one_le_left hρ hAc
  exact (paper_weightedNorm_mono_radius hρ hle π w hπ X).trans
    (paper_weightedNorm_scale_le _ _ hA π w hπ X)

/-- `x ≤ a y`, `y ≤ c n` and `a|c| ≤ C` give `x ≤ C n`. -/
private theorem paper_scaled_le (a x y c C n : ℝ) (ha : 0 ≤ a) (hn : 0 ≤ n) (hx : x ≤ a * y)
    (hy : y ≤ c * n) (hC : a * |c| ≤ C) : x ≤ C * n :=
  calc x ≤ a * y := hx
    _ ≤ a * (|c| * n) :=
      mul_le_mul_of_nonneg_left (hy.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn)) ha
    _ = a * |c| * n := (mul_assoc _ _ _).symm
    _ ≤ C * n := mul_le_mul_of_nonneg_right hC hn

/-- (P1)-(P4) from the profile bounds of `PassageClauses`, with a larger constant; (P3) and (P4)
are the two parts of the summed bound. -/
private theorem paper_profile_bounds_mono (a b c d e Y : ℝ≥0∞) {Cp C x₁ x₂ x₃ A : ℝ}
    (hC : Cp ≤ C) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃A : 0 ≤ x₃ * A)
    (h1 : a ≤ ENNReal.ofReal (Cp * x₁) * Y) (h2 : b ≤ ENNReal.ofReal (Cp * x₂) * Y)
    (h3 : c + d + e ≤ ENNReal.ofReal (Cp * x₃ * A)) :
    a ≤ ENNReal.ofReal (C * x₁) * Y ∧ b ≤ ENNReal.ofReal (C * x₂) * Y ∧
      c + d ≤ ENNReal.ofReal (C * x₃ * A) ∧ e ≤ ENNReal.ofReal (C * x₃ * A) := by
  have hm : ∀ x, 0 ≤ x → ENNReal.ofReal (Cp * x) ≤ ENNReal.ofReal (C * x) :=
    fun x hx => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hx)
  have h3' : c + d + e ≤ ENNReal.ofReal (C * x₃ * A) := by
    refine h3.trans ?_
    rw [mul_assoc, mul_assoc]
    exact hm _ hx₃A
  exact ⟨h1.trans (mul_le_mul' (hm _ hx₁) le_rfl), h2.trans (mul_le_mul' (hm _ hx₂) le_rfl),
    le_self_add.trans h3', le_add_self.trans h3'⟩

/-- **The supplement** from the frame and the datum part of `iteration_passage` at the same
`(t_p, Π)`, for every constant `C ≥ |C_pass|, A^{N_aux}|C_pass|, A^{N_out}|C_Q|`,
`A = max{1, c_r⁻¹}`. -/
private theorem paper_supplement_proof {cfg : FiniteParameters} {CQ Cp C : ℝ}
    (hCp : |Cp| ≤ C) (hCpr : max 1 cfg.kI.cr⁻¹ ^ cfg.Naux * |Cp| ≤ C)
    (hCQr : max 1 cfg.kI.cr⁻¹ ^ cfg.Nout * |CQ| ≤ C) (hcr : 0 < cfg.kI.cr)
    {D : OCData} (hq : 1 < D.q) (hΛD : 128 ≤ D.Λ) {Mnat : ℕ} {law : BirthLaw}
    {seedK freshK : ℕ → KernelSpec} {m : ℕ} {tA tc tf tp : ℝ}
    {seed G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))}
    (hlev : G.level = m) (hε : 0 ≤ D.eps (m - 1))
    (hframe : PaperPassageFrameAt cfg CQ Cp Mnat law seedK freshK seed G G' m tA tc tf tp Preg)
    (hout : PaperPassageOutputAt cfg Cp law seedK freshK G G' m tc tf tp Preg) :
    PaperPassageSupplement cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J)
      Preg := by
  subst hlev
  have hmass {S : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀} :
      ∀ v : CompIn S.comps, 0 < S.mass law v :=
    fun v => Construction.Preservation.Buffer.birth_compMass_pos hq hΛD law v.1
  have hCp' : Cp ≤ C := (le_abs_self _).trans hCp
  have hA0 : ∀ k : ℕ, 0 ≤ max 1 cfg.kI.cr⁻¹ ^ k :=
    fun k => pow_nonneg (zero_le_one.trans (le_max_left _ _)) k
  refine ⟨hframe.2.2.2.2.2.2.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCp' (Real.rpow_nonneg hε _))),
    fun f => ?_, fun f U Uw Uk hU Y0 Y Yw Yk htr hY => ?_⟩
  · exact paper_scaled_le _ _ _ _ _ _ (hA0 _) (Real.sqrt_nonneg _)
      (paper_weightedNorm_ocRh_le D hcr _ _ _ hmass _)
      (hframe.1.2.2.2.2 (G.marker law) (Or.inr rfl) f).2.2.1 hCQr
  have hd := (hout f _ le_rfl U Uw Uk hU).2 Y0 Y Yw Yk htr hY
  refine ⟨?_, fun aU aY haU haY CcT hL t ht => ⟨?_, ?_⟩⟩
  · exact hd.2.1.elim fun YN0 h => h.elim fun YN h => h.elim fun YNw h => h.elim fun YNk h =>
      ⟨YN0, YN, YNw, YNk, h.1, h.2.1, h.2.2.1, fun t ht =>
        paper_scaled_le _ _ _ _ _ _ (hA0 _) (Real.sqrt_nonneg _)
          (paper_weightedNorm_ocRh_le D hcr _ _ _ hmass _) (h.2.2.2.1 t ht) hCpr⟩
  · exact ((hd.2.2.2 aU aY haU haY CcT hL) t ht).1.elim fun Un h => h.elim fun Uh h =>
      ⟨Un, Uh, h.1, h.2.1, h.2.2.trans (mul_le_mul_of_nonneg_right hCp' (Real.sqrt_nonneg _))⟩
  · have hpc := hd.2.2.1.2 aU aY haU haY CcT hL t ht
    exact paper_profile_bounds_mono _ _ _ _ _ _ hCp' (Real.rpow_nonneg hε _)
      (Real.rpow_nonneg hε _) (mul_nonneg (Real.rpow_nonneg hε _) (Real.sqrt_nonneg _))
      hpc.1 hpc.2.1 hpc.2.2.1

/-- `PaperStepStatement` is the case `t_A = t_c - 3τ_m` of `PaperStepStatementAt`. -/
theorem paper_step_of_step_at (cfg : FiniteParameters) (m₀ : ℕ) (C : ℝ)
    (h : PaperStepStatementAt cfg m₀ C) : PaperStepStatement cfg m₀ C := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm tc tf G
    G' hG htf hsucc
  obtain ⟨tp, Preg, hcyc, hpass, -⟩ := h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh m hm _ tc tf G G' hG (sub_add_cancel _ _).le htf hsucc
  exact ⟨tp, Preg, paper_cycle_conclusion_of_at hcyc, hpass⟩

/-- **One cycle with a free history start, one passage and the supplement** at the parameters, for
every
constant `C ≥ 3|C_pass|, |C_Q|, A^{N_aux}|C_pass|, A^{N_out}|C_Q|`, `A = max{1, c_r⁻¹}`. -/
private theorem paper_step_at_proof {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (C : ℝ)
    (hCp : 3 * |P.Cpass| ≤ C) (hCQ : |P.CQpass| ≤ C)
    (hCpr : max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Naux * |P.Cpass| ≤ C)
    (hCQr : max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Nout * |P.CQpass| ≤ C) :
    PaperStepStatementAt P.ready.cfg (paperBottom P) C := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm tA tc tf
    G G' hG htA htf hsucc
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hq : 1 < D.q := by rw [hDq]; exact P.ready.valid.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hε := Scales.epsilon_basic (m := m - 1) hq hΛD
  have hlev : G.level = m := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hG
    exact h
  have hCp' : |P.Cpass| ≤ C := by linarith [abs_nonneg P.Cpass]
  obtain ⟨tp, Preg, hcyc, hpass, ⟨seed, hframe⟩, hout⟩ :=
    paper_step_frame_of_parameters hs₀ hΛ P C hCp hCQ hDα hDq hDΛ hDζ hDΦ hband hterm hMnat hlaw
      hfresh hm hG htA htf hsucc
  exact ⟨tp, Preg, hcyc, hpass,
    paper_supplement_proof hCp' hCpr hCQr P.ready.valid.hcr hq hΛD hlev hε.1.le hframe hout⟩

/-- **The cascade, one cycle with a free history start and one passage at the parameters `P`**,
with `m₀ = paperBottom P`. -/
theorem paper_cascade_at_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (_htT : t₀ < T₀)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    ∃ C : ℝ, 0 < C ∧ P.mStar ≤ paperBottom P ∧
      PaperStepStatementAt P.ready.cfg (paperBottom P) C ∧
      PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  refine ⟨max (3 * |P.Cpass|) (max |P.CQpass| (max |P.ready.cfg.Ccas| (max 1
      (max (max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Naux * |P.Cpass|)
        (max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Nout * |P.CQpass|))))),
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))),
    le_max_left _ _, paper_step_at_proof hs₀ hΛ P _ (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))))
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))),
    paper_cascade_proof hΛ ht₀ P _ ((le_abs_self _).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))⟩

/-- **The cascade, one cycle with a free history start, one passage and the supplement**, in the
setting of the entry statement `paper_entry`: one choice of parameters satisfies the entry
statement with a constant `C_E`, and the cascade, one cycle with free `t_A`, one passage and the
supplement with a constant `C > 0` and `m₀ = paperBottom P ≥ m_*`. -/
theorem paper_cascade_cycle_passage_at (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw → ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ →
    ∃ (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (CE C : ℝ),
      PaperEntryStatement P.ready.cfg P.ready.Mstar CE ∧
      0 < C ∧ P.mStar ≤ paperBottom P ∧
      PaperStepStatementAt P.ready.cfg (paperBottom P) C ∧
      PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  obtain ⟨Λ₀, hΛ₀, hP⟩ := paper_parameters_exist α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Jw hJw t₀ T₀ ht₀ htT => ?_⟩
  obtain ⟨P⟩ := hP Λ hΛ Jw hJw t₀ T₀ ht₀ htT
  obtain ⟨CE, hE⟩ := paper_entry_of_ready hs₀ (hΛ₀.trans hΛ) ht₀ htT P.ready
  obtain ⟨C, hC, hm, hstep, hcas⟩ := paper_cascade_at_of_parameters hs₀ (hΛ₀.trans hΛ) ht₀ htT P
  exact ⟨P, CE, C, hE, hC, hm, hstep, hcas⟩

/-- **The same at a prescribed invariant order**, in the setting of the entry statement
`paper_entry`: for every order requirement `K_req` computed from the schedule, one choice of
parameters whose invariant constants have the single order `k_I.K_s ≥ K_req(schedule)` satisfies
the entry statement with a constant `C_E`, and the cascade, one cycle with free `t_A`, one passage
and the supplement with a constant `C > 0` and `m₀ = paperBottom P ≥ m_*`; the threshold `Λ₀` is
chosen before the order. -/
theorem paper_cascade_cycle_passage_order (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw → ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ →
    ∀ Kreq : PaperSchedule → ℕ, ∃ (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (CE C : ℝ),
      Kreq (paperScheduleOf P.ready.cfg) ≤ P.ready.cfg.kI.Ks ∧
      P.ready.cfg.kI.Kan = P.ready.cfg.kI.Ks ∧ P.ready.cfg.kI.Lan = P.ready.cfg.kI.Ks ∧
      P.ready.cfg.kI.Jm = P.ready.cfg.kI.Ks ∧
      PaperEntryStatement P.ready.cfg P.ready.Mstar CE ∧
      0 < C ∧ P.mStar ≤ paperBottom P ∧
      PaperStepStatementAt P.ready.cfg (paperBottom P) C ∧
      PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  obtain ⟨Λ₀, hΛ₀, hP⟩ := paper_parameters_exist_order α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Jw hJw t₀ T₀ ht₀ htT Kreq => ?_⟩
  obtain ⟨P, hKs, hKan, hLan, hJm⟩ := hP Λ hΛ Jw hJw t₀ T₀ ht₀ htT Kreq
  obtain ⟨CE, hE⟩ := paper_entry_of_ready hs₀ (hΛ₀.trans hΛ) ht₀ htT P.ready
  obtain ⟨C, hC, hm, hstep, hcas⟩ := paper_cascade_at_of_parameters hs₀ (hΛ₀.trans hΛ) ht₀ htT P
  exact ⟨P, CE, C, hKs, hKan, hLan, hJm, hE, hC, hm, hstep, hcas⟩

/-- **The preparation frame** (Proposition 11.1(i) of the paper, and conjuncts 1-3 of
`PassageFrame`) at the parameters and the constant `C`: `(t_pr, Π)` is a common preparation of `G`
from `t_c` on `[t_c, t_f]` (`t_pr` a quiet time in `[t_c, t_c + 4τ''_m]`, `Π` fixes constants, the
three bounds of `Π f`, and the bound of the retained traces), `t_c + ρ_⋆(m)²/κ_m ≤ t_pr`, and the
quiet margin `[t_pr - τ'_m, t_pr + τ'_m]` is quiet. -/
def PaperPreparationFrame (cfg : FiniteParameters) (C : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tf tp : ℝ)
    (G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  IsCommonPreparation law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ G cfg.kI.cr cfg.Q C C
      cfg.p cfg.Nout cfg.Naux tc tf tp Preg ∧
    tc + rhoStar D cfg.kI.c₀ m ^ 2 / D.κ m ≤ tp ∧
    Set.Icc (tp - ocTauP D.α D.q D.Λ m) (tp + ocTauP D.α D.q D.Λ m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ m

/-- **One cycle, one passage, the supplement and the preparation frame for one `(t_pr, Π)`**, at
the parameters `cfg`, bottom level `m₀` and constant `C`: for every admissible family `G` of level
`m > m₀` on `[t_A, t_f]` with `t_A + 3τ_m ≤ t_c` and `t_c + 4τ''_m ≤ t_f` and every actual
successor, one preparation `(t_pr, Π)` gives the preparation frame, the three conclusions of
`PaperStepStatementAt`, and one passage at the exponent `η₀` (`PaperPassageConclusionEta`). -/
def PaperPreparationBundleStatement (cfg : FiniteParameters) (m₀ : ℕ) (C : ℝ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (m : ℕ), m₀ < m →
  ∀ (tA tc tf : ℝ) (G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    IsPaperFamily cfg M Mnat law seedK freshK G m tA tf →
    tA + 3 * ocTau cfg.α cfg.q cfg.Λ m ≤ tc →
    tc + 4 * ocTauPP cfg.α cfg.q cfg.Λ m ≤ tf →
    IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G' →
  ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))),
    PaperPreparationFrame cfg C law seedK freshK m tc tf tp G Preg ∧
    PaperCycleConclusionAt cfg C M Mnat law seedK freshK m tA tc tp tf G
      (G'.retained m cfg.H cfg.J) Preg ∧
    PaperPassageConclusion cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J) Preg ∧
    PaperPassageConclusionEta cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J)
      Preg ∧
    PaperPassageSupplement cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J) Preg

/-- The preparation bundle gives `PaperStepStatementAt` (forget the preparation frame). -/
theorem paper_step_at_of_preparation_bundle {cfg : FiniteParameters} {m₀ : ℕ} {C : ℝ}
    (h : PaperPreparationBundleStatement cfg m₀ C) : PaperStepStatementAt cfg m₀ C := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm tA tc tf
    G G' hG htA htf hsucc
  obtain ⟨tp, Preg, -, hcyc, hpass, -, hsup⟩ := h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law
    hlaw seedK freshK hfresh m hm tA tc tf G G' hG htA htf hsucc
  exact ⟨tp, Preg, hcyc, hpass, hsup⟩

/-- `IsCommonPreparation` is monotone in its two constants. -/
private theorem paper_commonPreparation_mono {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {law : BirthLaw} {Pp : ProvParams} {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {G : GenStage D ScalarH Dm b j₀} {cr Q CQ C CQ' C' : ℝ}
    {p Nout Naux : ℕ} {s tf tp : ℝ}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))}
    (hCQ : CQ ≤ CQ') (hC : C ≤ C') (hε : 0 ≤ D.eps (G.level - 1) ^ Q)
    (h : IsCommonPreparation law Pp seedK freshK φ₀ hφ₀ G cr Q CQ C p Nout Naux s tf tp Preg) :
    IsCommonPreparation law Pp seedK freshK φ₀ hφ₀ G cr Q CQ' C' p Nout Naux s tf tp Preg := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun w hw f => ?_⟩
  have h4 := h.2.2.2.2 w hw f
  have hN : 0 ≤ weightedNorm 1 (G.mass law) w f := Real.sqrt_nonneg _
  refine ⟨fun U W Y hU => (h4.1 U W Y hU).trans ?_, h4.2.1.trans ?_, h4.2.2.1.trans ?_,
    fun Ain hA Qh hQ => (h4.2.2.2 Ain hA Qh hQ).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCQ hε) hN
  · exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCQ hε)) hN
  · exact mul_le_mul_of_nonneg_right hCQ hN
  · exact mul_le_mul_of_nonneg_right hC (hN.trans hA)

/-- **The preparation bundle** at the parameters, for every constant
`C ≥ 3|C_pass|, |C_Q|, A^{N_aux}|C_pass|, A^{N_out}|C_Q|`, `A = max{1, c_r⁻¹}`. -/
private theorem paper_preparation_bundle_proof {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (C : ℝ)
    (hCp : 3 * |P.Cpass| ≤ C) (hCQ : |P.CQpass| ≤ C)
    (hCpr : max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Naux * |P.Cpass| ≤ C)
    (hCQr : max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Nout * |P.CQpass| ≤ C) :
    PaperPreparationBundleStatement P.ready.cfg (paperBottom P) C := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm tA tc tf
    G G' hG htA htf hsucc
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hq : 1 < D.q := by rw [hDq]; exact P.ready.valid.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hε := Scales.epsilon_basic (m := m - 1) hq hΛD
  have hlev : G.level = m := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hG
    exact h
  have hCp' : |P.Cpass| ≤ C := by linarith [abs_nonneg P.Cpass]
  obtain ⟨tp, Preg, hcyc, hpass, ⟨seed, hframe⟩, hout⟩ :=
    paper_step_frame_of_parameters hs₀ hΛ P C hCp hCQ hDα hDq hDΛ hDζ hDΦ hband hterm hMnat hlaw
      hfresh hm hG htA htf hsucc
  have hε0 : 0 ≤ D.eps (G.level - 1) ^ P.ready.cfg.Q := by
    rw [hlev]
    exact Real.rpow_nonneg hε.1.le _
  exact ⟨tp, Preg, ⟨paper_commonPreparation_mono ((le_abs_self _).trans hCQ)
      ((le_abs_self _).trans hCp') hε0 hframe.1, hframe.2.1, hframe.2.2.1⟩, hcyc, hpass,
    paper_passage_eta_proof hs₀ P hCp hq hΛD hε.1 hε.2.1 hout,
    paper_supplement_proof hCp' hCpr hCQr P.ready.valid.hcr hq hΛD hlev hε.1.le hframe hout⟩

/-- **The preparation bundle at the parameters `P`**, with `m₀ = paperBottom P`, together with the
cascade at the same constant. -/
theorem paper_preparation_bundle_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (_htT : t₀ < T₀)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    ∃ C : ℝ, 0 < C ∧ PaperPreparationBundleStatement P.ready.cfg (paperBottom P) C ∧
      PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  refine ⟨max (3 * |P.Cpass|) (max |P.CQpass| (max |P.ready.cfg.Ccas| (max 1
      (max (max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Naux * |P.Cpass|)
        (max 1 P.ready.cfg.kI.cr⁻¹ ^ P.ready.cfg.Nout * |P.CQpass|))))),
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))),
    paper_preparation_bundle_proof hs₀ hΛ P _ (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))))
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))),
    paper_cascade_proof hΛ ht₀ P _ ((le_abs_self _).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))⟩

end AVRegularity.PaperFacing
