-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.TerminalSeedTransportOfIngredients
import AVRegularity.Construction.EntryScales.TerminalCore
public import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.Assembly

/-! Extract the actual entry witnesses once and locate their seed start before
the final cascade window. No cascade construction or entry statement is proved here. -/

theorem finite_entry_selection : FiniteEntrySelectionStatement := by
  intro cfg _hvalid _htransport _hs _hs1 hΛ _hη _ht₀ _htT _hτ hc _hCcas _hPw _hPT
    M _hM _hbudget hwait hentry _hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm _haxes a f _hf θ hθ
  let PW := termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M
  obtain ⟨stage, Gw, lawW, ιw, aM, CcR, W, hconstruction, hencoding, hlifts, hchain, hstage,
    tp, Pterm, lawT, Gt', seed, rootM, rootR, seedKc, ι, hprep, hlaw, hactual,
    hseedenc, hseed, hterminalwindow, hdatum⟩ :=
    hentry D hDα hDq hDΛ hDζ hDΦ hband hDterm PW a
  obtain ⟨tq, Ur, Urw, Urk, U₀, U, V, Uw, Vw, Uk, Vk, _hred, _htq, _hU₀, _hU,
    _hpair, _hreadout, _hprepbounds, Z, hfamily, hidentity⟩ := hdatum f θ hθ
  have hH : 0 ≤ D.termH M := by
    unfold OCData.termH
    rw [hDα, hDq, hDΛ]
    exact (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ cfg.Λ)).le
  have haM := hstage.1
  have haMup := hstage.2.1
  simp only [hDα, hDq, hDΛ] at haMup
  have htplow := hprep.2.1
  have htpup := hprep.2.2.1
  have hclow : 0 ≤ cfg.c * D.termH M := mul_nonneg hc.le hH
  have hCup : cfg.C * D.termH M ≤ |cfg.C| * D.termH M :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hH
  have hH' : D.termH M = ocTauPP cfg.α cfg.q cfg.Λ M := by
    simp only [OCData.termH, hDα, hDq, hDΛ]
  have hseedwait : tp + D.termH M ≤ a + cfg.t₀ / 4 := by
    rw [hH'] at htpup hCup ⊢
    linarith only [htpup, hCup, haMup, hwait]
  exact ⟨{
    PW := PW
    stage := stage
    Gw := Gw
    lawW := lawW
    ιw := ιw
    CcR := CcR
    W := W
    aM := aM
    construction := hconstruction
    encoding := hencoding
    lifts := hlifts
    chain := hchain
    weakStage := hstage
    tp := tp
    Pterm := Pterm
    lawT := lawT
    Gt' := Gt'
    prep := hprep
    terminalLaw := hlaw
    actual := hactual
    V := V
    Z := Z
    identity := hidentity
    seed := seed
    rootM := rootM
    rootR := rootR
    seedKc := seedKc
    ι := ι
    seedEncoding := hseedenc
    seedClauses := hseed
    family := hfamily
    a_le_tp := by linarith only [haM, htplow, hclow]
    seed_wait := hseedwait
    terminal_window := hterminalwindow
  }⟩

/-- The routine selection and the reindexing are discharged. -/
theorem finite_strong_entry_of_seed_representation (hseed : FiniteSeedRepresentationStatement) :
    FiniteStrongEntryStatement :=
  finite_strong_entry_of_ingredients finite_entry_selection hseed

end AVRegularity.Finite.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.Assembly

/-! Extract the seed-level solution and its represented bound from an actual cascade
output. The extraction keeps a single seed-family carrier so that frame equality
can be used before comparing its components with the terminal family. -/

theorem terminal_seed_datum_reindex {S T : Finset Comp} (ι : CompIn S ≃ CompIn T)
    (K : ℕ) (Z : CompIn S → ℝ → TorusHk K ℝ) (sn : ℝ)
    (fn : CompIn T → TorusHk 0 ℝ)
    (hfn : ∀ v, fn (ι v) = truncateTorusHk (Nat.zero_le K) (Z v sn)) :
    fn = fun w => truncateTorusHk (Nat.zero_le K) (Z (ι.symm w) sn) := by
  funext w
  have hw := hfn (ι.symm w)
  simpa only [ι.apply_symm_apply w] using hw

theorem finite_seed_mass {cfg : FiniteParameters} {D : OCData} {M : ℕ} {a : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} (E : FiniteEntryData cfg D M a f θ)
    (law : BirthLaw) (hroot : law.rootMass = E.rootM) (w : CompIn E.seed.comps) :
    E.seed.mass law w = E.rootM w.1.root := by
  have hbirth : w.1.births = [] := by
    simpa only [Equiv.apply_symm_apply] using E.seedEncoding.2.1 (E.ι.symm w)
  change compMass D.q D.Λ law w.1 = _
  simp only [compMass, hbirth, List.map_nil, List.prod_nil, mul_one, hroot]

def SeedCascadeRepresentation {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D ScalarH Dm b j₀)
    (n K : ℕ) (sn delay tf s C : ℝ)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) : Prop :=
  ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (r : TimeRep (CompSpace G.comps)),
    G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ n) (streamVel (D.Φ n)) 0 sn tf f
      (fun _ _ => 0) (fun _ _ => 0) U Uw Uk ∧
    (∀ t ∈ Set.Icc (sn + delay) tf,
      IsRepresentationAt (D.eps n) K (r.atTime t) ∧ IsRepOf (G.mass law) (fun v => U v t) (r.atTime t).value) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (sn + delay) tf)),
      representedSize s K (D.eps n) (r.atTime t) ≤
        ENNReal.ofReal (C * weightedNorm 1 (G.mass law) (fun _ => 1) f)

theorem cascade_seed_representation {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C cr c₀ : ℝ) (n m₀ : ℕ) (sn delay tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (hmn : m₀ ≤ n) (hstart : st n = sn) (hmass : ∀ v : CompIn (stage n).comps, 0 < (stage n).mass law v)
    (hout : CascadeOutput law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp
      Pacc Q C cr c₀ n m₀ sn delay tf stage hist st tp Preg f) :
    SeedCascadeRepresentation law P seedK freshK φ₀ hφ₀ (stage n) n K sn delay tf s C f := by
  obtain ⟨U, Uw, Uk, Y0, aU, _CcT, rep, hY0, hsol, _hpass, hsmooth, _hbase, hrep, hsize⟩ := hout
  have hnsol := (hsol n hmn le_rfl).1
  rw [hstart, hY0] at hnsol
  refine ⟨U n, Uw n, Uk n, rep n, hnsol, ?_, hsize⟩
  intro t ht
  obtain ⟨hr, hvalue⟩ := hrep t ht
  refine ⟨hr, ?_⟩
  intro v
  have hv := (hsmooth t ht).2.2 v
  filter_upwards [hv] with x hx
  rw [hvalue]
  change _ = Real.sqrt ((stage n).mass law v) *
    ((Real.sqrt ((stage n).mass law v))⁻¹ * aU n t x v)
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hmass v)).ne', one_mul]
  exact hx

/-- The prescribed successor law exists for the positive seed roots. -/
theorem finite_successor_law (cfg : FiniteParameters) (hη : 0 < succEta0 cfg.α cfg.q cfg.s)
    (rootM rootR : ℕ → ℝ) (hM : ∀ r, 0 < rootM r) (hR : ∀ r, 0 < rootR r) :
    ∃ law : BirthLaw, law.rootMass = rootM ∧ law.rootReadout = rootR ∧
      IsSuccessorLaw cfg.α cfg.q cfg.s
        (wordsUpTo (succAlphabetOf (termR0bar cfg.RT (cfg.Jw * cfg.Rw))
          (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.H cfg.J cfg.N cfg.p 0)
          (cfg.J + 1)).card law := by
  classical
  let A := succAlphabetOf (termR0bar cfg.RT (cfg.Jw * cfg.Rw))
    (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.H cfg.J cfg.N cfg.p 0
  have hdiag : WordLetter.diag ∈ A := by
    simp only [A, succAlphabetOf, succAlphabet, Finset.mem_union, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl True.intro))
  have hword : [WordLetter.diag] ∈ wordsUpTo A (cfg.J + 1) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    change [WordLetter.diag] ∈ (A ×ˢ {[]}).image (fun x => x.2 ++ [x.1])
    exact Finset.mem_image.mpr ⟨(WordLetter.diag, []),
      Finset.mem_product.mpr ⟨hdiag, Finset.mem_singleton_self _⟩, rfl⟩
  have hcount : 0 < (wordsUpTo A (cfg.J + 1)).card :=
    Finset.card_pos.mpr ⟨_, hword⟩
  have hpow : (128 : ℝ) ^ (-(succEta0 cfg.α cfg.q cfg.s / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (div_pos hη (by norm_num)))
  let law : BirthLaw := {
    cH := (1 - (128 : ℝ) ^ (-(succEta0 cfg.α cfg.q cfg.s / 2))) / 2
    cH_pos := div_pos (sub_pos.mpr hpow) (by norm_num)
    wordCount := (wordsUpTo A (cfg.J + 1)).card
    wordCount_pos := hcount
    etaB := succEta0 cfg.α cfg.q cfg.s / 2
    eta0 := succEta0 cfg.α cfg.q cfg.s
    iota := succEta0 cfg.α cfg.q cfg.s / 8
    rootMass := rootM
    rootMass_pos := hM
    rootReadout := rootR
    rootReadout_pos := hR
  }
  exact ⟨law, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AVRegularity.Finite.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Finite.Assembly

/-! Uniform seed kernel-price and radius thresholds retained by the finite selector. -/

theorem exists_finite_seed_budget_level (cfg : FiniteParameters)
    (hv : FiniteLocalValidity cfg) (hΛ : 128 ≤ cfg.Λ) :
    ∃ N : ℕ, ∀ M, N ≤ M → FiniteSeedBudgetLevel cfg M := by
  have hp : 0 < cfg.q * cfg.τe := mul_pos (lt_trans zero_lt_one hv.hq.1) hv.hτe
  have hprice : Tendsto (fun n : ℕ => cfg.Ce * ocEpsilon cfg.q cfg.Λ n ^ (cfg.q * cfg.τe))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (EntryScales.epsilon_rpow_tendsto_zero hv.hq.1 hΛ hp)
  have hrad : Tendsto (fun n : ℕ => (2 * cfg.kS.c₀) * ocEpsilon cfg.q cfg.Λ n ^ (cfg.q - 1))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (EntryScales.epsilon_rpow_tendsto_zero hv.hq.1 hΛ (sub_pos.mpr hv.hq.1))
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hprice.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))).and
      (hrad.eventually (eventually_le_nhds zero_lt_one)))
  refine ⟨max (N + 2) (cfg.j₀ + 2), ?_⟩
  intro M hM
  have hMn : N ≤ M - 2 := by omega
  have hE := (Scales.epsilon_basic (m := M - 2) hv.hq.1 hΛ).1
  refine ⟨by omega, by omega, (hN (M - 2) hMn).1, ?_⟩
  have hstep := Scales.epsilon_q_step hv.hq.1 hv.hq.2.1 hΛ (by omega : 1 ≤ M - 1)
  have hpow : ocEpsilon cfg.q cfg.Λ (M - 2) ^ cfg.q =
      ocEpsilon cfg.q cfg.Λ (M - 2) ^ (cfg.q - 1) * ocEpsilon cfg.q cfg.Λ (M - 2) := by
    calc _ = ocEpsilon cfg.q cfg.Λ (M - 2) ^ ((cfg.q - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hE, Real.rpow_one]
  calc cfg.kS.c₀ * ocEpsilon cfg.q cfg.Λ (M - 1)
      ≤ cfg.kS.c₀ * (2 * ocEpsilon cfg.q cfg.Λ (M - 2) ^ cfg.q) :=
        mul_le_mul_of_nonneg_left (by simpa only [Nat.sub_sub] using hstep) hv.hc₀.le
    _ = ((2 * cfg.kS.c₀) * ocEpsilon cfg.q cfg.Λ (M - 2) ^ (cfg.q - 1)) *
        ocEpsilon cfg.q cfg.Λ (M - 2) := by rw [hpow]; ring
    _ ≤ 1 * ocEpsilon cfg.q cfg.Λ (M - 2) :=
        mul_le_mul_of_nonneg_right (hN (M - 2) hMn).2 hE.le
    _ = _ := one_mul _

/-- The generated seed supplies the literal seed-transport operator at order zero. -/
def finite_seed_kernel_operator (cfg : FiniteParameters) (hv : FiniteLocalValidity cfg)
    (M : ℕ) (hbudget : FiniteSeedBudgetLevel cfg M) (D : OCData)
    (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ) (_hDζ : D.ζ = cfg.ζ)
    (hΛ : 128 ≤ cfg.Λ) (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ)
    (hDterm : D.term = M) (law : BirthLaw) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (a b : ℝ) (hab : a ≤ b)
    (seed : GenStage D ScalarH
      (succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))
        cfg.N cfg.p (cfg.H + 1)) cfg.bw cfg.j₀)
    (hg : IsGeneratedSeed law P seedK freshK cfg.φ₀ cfg.hφ₀ (M + cfg.Jw) cfg.kS seed
      (M - 1) a b cfg.Ce cfg.τe (termR0bar cfg.RT (cfg.Jw * cfg.Rw))
      (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))) :
    KernelEnergy.TorusKernelOperator (h := fun w : CompIn seed.comps => ScalarH w.1.root)
      (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
      a b (rhoStar D cfg.kS.c₀ seed.level) (D.kap seed.level) 0
      (succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))
        cfg.N cfg.p (cfg.H + 1)) := by
  have hM2 := hbudget.hlevel
  have hlevel := hg.1
  have hI := hg.2.2.2.2.2.2.2.1
  have hε (n : ℕ) : 0 < D.eps n := by
    change 0 < ocEpsilon D.q D.Λ n
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hv.hq.1 hΛ).1
  have hkap : D.kap seed.level = D.κ (M - 1) := by
    simp only [OCData.kap, hlevel, hDterm, min_eq_left (Nat.sub_le M 1)]
  have hν : 0 < D.kap seed.level := by
    rw [hkap]
    exact CycleReference.bandChain_pos (by omega) hv.hζ hband (by omega)
  have hνκ : 0 < D.κ seed.level := by
    rw [hlevel]
    exact CycleReference.bandChain_pos (by omega) hv.hζ hband (by omega)
  have hA : 0 < ocA D.α D.q D.Λ seed.level :=
    Real.rpow_pos_of_pos (hε seed.level) _
  have hρ : 0 < rhoStar D cfg.kS.c₀ seed.level :=
    mul_pos hv.hc₀ (lt_min (hε _) (Real.sqrt_pos.mpr (div_pos hνκ hA)))
  have hradius : rhoStar D cfg.kS.c₀ seed.level ≤ D.eps (seed.level - 1) := by
    apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hv.hc₀.le).trans
    simpa only [hlevel, OCData.eps, hDq, hDΛ, Nat.sub_sub] using hbudget.hradius
  have hθ : cfg.Ce * D.eps (M - 1 - 1) ^ (D.q * cfg.τe) ≤ 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ, Nat.sub_sub] using hbudget.hprice
  exact Construction.Preservation.Buffer.nativeInvariantKernelOperator law P
    (succMenu (M + cfg.Jw) (termR0bar cfg.RT (cfg.Jw * cfg.Rw))
      (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))
      cfg.H cfg.J cfg.N cfg.p 0 cfg.sX cfg.sZ cfg.η₀)
    seedK freshK cfg.φ₀ cfg.hφ₀ (M + cfg.Jw) cfg.kS a b
    (cfg.Ce * D.eps (M - 1) ^ cfg.τe) _ seed seed hI hg.2.1 .seed hv.hHprod
    (by rw [hDq]; exact hv.hq.1) (by rw [hDΛ]; exact hΛ)
    (by rw [hlevel]; omega) (by rw [hlevel]; exact hbudget.hj₀) hv.hbw (hε _) hab hν hρ hradius
    (by unfold succSchedD; omega) hθ 0 (Nat.zero_le _) (fun _ => 1) (Or.inl rfl)

end AVRegularity.Finite.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.Assembly

/-! Apply the supplied cascade to the actual entry seed. The
pointwise envelope comes from the seed clauses. The transport input
identifies the seed solution. Its kernel premises are supplied by the generated
seed invariant and the selector's proved numerical threshold. -/

theorem finite_seed_representation : FiniteSeedRepresentationStatement := by
  intro cfg hvalid htransport _hs _hs1 hΛ hη ht₀ htT _hτ _hc hCcas _hPw _hPT M hM hbudget
    _hwait _hentry hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm haxes a f _hf θ _hθ E
  classical
  obtain ⟨law, hrootM, hrootR, hlaw⟩ := finite_successor_law cfg hη E.rootM E.rootR
    E.seedClauses.1 E.seedClauses.2.1
  obtain ⟨hgenerated, hpointwise, _hmassSum, _hreadoutSum⟩ := E.seedClauses.2.2 law hrootM hrootR
  choose H₁ H₂ hH using haxes
  let freshK (b' : ℕ) : KernelSpec := {
    width := freshWidth D cfg.kI.cr cfg.σ₀ b'
    order := cfg.nk.toPNat'
    H₁ := if h : 1 ≤ b' ∧ b' < M then H₁ b' h.1 h.2 else fun _ => ContinuousLinearMap.id ℝ (Vec 2)
    H₂ := if h : 1 ≤ b' ∧ b' < M then H₂ b' h.1 h.2 else fun _ => ContinuousLinearMap.id ℝ (Vec 2)
  }
  have hfresh : ∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b') := by
    intro b' hb hM'
    have hbirth : 1 ≤ b' ∧ b' < M := ⟨hb, hM'⟩
    exact ⟨rfl, rfl, by simpa only [freshK, dite_eq_left hbirth] using hH b' hb hM'⟩
  let P := succProvParams D cfg.CwCas cfg.kI.cr cfg.σ₀ (succEta0 cfg.α cfg.q cfg.s) cfg.N cfg.p
  let sn := E.tp + D.termH M
  have hH0 : 0 ≤ D.termH M := by
    unfold OCData.termH
    rw [hDα, hDq, hDΛ]
    exact (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ cfg.Λ)).le
  have ha_sn : a ≤ sn := by dsimp [sn]; linarith only [E.a_le_tp, hH0]
  have hsn_tf : sn ≤ a + cfg.T₀ := by
    dsimp [sn]
    linarith only [E.seed_wait, ht₀, htT]
  have hdelay : sn + cfg.t₀ / 2 < a + cfg.T₀ := by
    dsimp [sn]
    linarith only [E.seed_wait, ht₀, htT]
  have hlength : a + cfg.T₀ - sn ≤ cfg.T₀ := by linarith only [ha_sn]
  obtain ⟨cs, ext, hist, st, tp, Preg, hframe, houtput⟩ :=
    hcas D hDα hDq hDΛ hDζ hDΦ M hband hDterm (M + cfg.Jw) (by omega) law hlaw
      E.seedKc freshK hfresh E.seed (M - 1) sn (a + cfg.T₀) hdelay hlength
      (hgenerated P freshK) hpointwise (by omega) (by omega)
  have hseedmass (w : CompIn E.seed.comps) : 0 < E.seed.mass law w := by
    rw [finite_seed_mass E law hrootM]
    exact E.seedClauses.1 _
  have hmassCS : ∀ w : CompIn (cs (M - 1)).comps, 0 < (cs (M - 1)).mass law w := by
    rw [hframe.1]
    exact hseedmass
  have hseedAll : ∀ fn : ∀ v : CompIn (cs (M - 1)).comps, TorusHk 0 (ScalarH v.1.root),
      SeedCascadeRepresentation law P E.seedKc freshK cfg.φ₀ cfg.hφ₀ (cs (M - 1)) (M - 1)
        (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) sn (cfg.t₀ / 2) (a + cfg.T₀)
        cfg.s cfg.Ccas fn := by
    intro fn
    exact cascade_seed_representation law P E.seedKc freshK cfg.φ₀ cfg.hφ₀ cfg.p cfg.N
      (succSchedR (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) cfg.J cfg.H) cfg.sX cfg.sZ
      (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) cfg.Naux cfg.s (succEta0 cfg.α cfg.q cfg.s)
      (ocMuS cfg.α cfg.q cfg.s) (ocDelta cfg.α cfg.q - 2 * cfg.σ₀) 2 cfg.Q cfg.Ccas cfg.kI.cr
      cfg.kI.c₀ (M - 1) cfg.m₀ sn (cfg.t₀ / 2) (a + cfg.T₀) cs hist st tp Preg fn
      (by omega) hframe.2.2.1 hmassCS (houtput fn)
  rw [hframe.1] at hseedAll
  let fn : ∀ w : CompIn E.seed.comps, TorusHk 0 (ScalarH w.1.root) :=
    fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) sn)
  obtain ⟨U, Uw, Uk, rep, hU, hrep, hsize⟩ := hseedAll fn
  obtain ⟨Z₀, Zw, Zk, _htrace, hZ, _henergy, fnStored, hfnStored, hnorm⟩ := E.family
  have hfn : fnStored = fn := terminal_seed_datum_reindex E.ι _ E.Z sn fnStored hfnStored
  have hnorm' : weightedNorm 1 (fun w => E.rootM w.1.root) (fun _ => 1) fn ≤
      cfg.Centry * Real.sqrt (l2NormSq f) := by simpa only [hfn] using hnorm
  have hnormLaw : weightedNorm 1 (E.seed.mass law) (fun _ => 1) fn ≤
      |cfg.Centry| * Real.sqrt (l2NormSq f) := by
    have hm : E.seed.mass law = fun w => E.rootM w.1.root := funext (finite_seed_mass E law hrootM)
    rw [hm]
    exact hnorm'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  let R := finite_seed_kernel_operator cfg hvalid M hbudget D hDq hDΛ hDζ hΛ hband hDterm
    law P E.seedKc freshK sn (a + cfg.T₀) hsn_tf E.seed (hgenerated P freshK)
  have hkap : D.kap E.seed.level = D.κ (M - 1) := by
    simp only [OCData.kap, (hgenerated P freshK).1, hDterm,
      min_eq_left (Nat.sub_le M 1)]
  have hν : 0 < D.κ (M - 1) := by rw [← hkap]; exact R.diffusivity_pos
  have hschur := R.hschur
  conv at hschur =>
    arg 2
    arg 1
    rw [hkap]
  have hidentify := (htransport (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
    E.lawT E.rootM E.rootR (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
    (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT) E.seedKc cfg.φ₀ cfg.hφ₀
    (E.Gt'.retained M 1 cfg.RT) E.seed E.ι E.seedEncoding M _ E.tp sn (a + cfg.T₀)
    (by dsimp [sn]; linarith only [hH0]) hsn_tf Z₀ E.Z Zw Zk hZ P freshK (rhoStar D cfg.kS.c₀ E.seed.level) R.θ R.π R.c
    R.radius_pos hν R.order_ge_two R.hπ R.hθ
    (fun w u γ d => ⟨R.hB_meas w u γ d, R.hB_smooth w u γ d,
      R.hB_per w u γ d, R.hB_fin w u γ d⟩)
    (fun w u γ => ⟨R.hr w u γ, R.hS w u γ⟩) hschur).2 U Uw Uk hU
  have hsubset : Set.Icc (a + cfg.t₀) (a + cfg.T₀) ⊆ Set.Icc (sn + cfg.t₀ / 2) (a + cfg.T₀) := by
    intro t ht
    refine ⟨?_, ht.2⟩
    dsimp [sn]
    linarith only [E.seed_wait, ht.1, ht₀]
  have hae := ae_restrict_of_ae_restrict_of_subset hsubset hsize
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with t ht htw
  have htc := hsubset htw
  have hts : t ∈ Set.Icc sn (a + cfg.T₀) := ⟨by linarith only [htc.1, ht₀], htc.2⟩
  refine ⟨rep.atTime t, (hrep t htc).1, ?_, ?_⟩
  · intro w
    have hw := (hrep t htc).2 w
    dsimp only at hw
    rw [hidentify w t hts] at hw
    simpa only [finite_seed_mass E law hrootM] using hw
  · exact ht.trans (ENNReal.ofReal_mono (by simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hnormLaw hCcas.le)))

/-- Seed-to-terminal represented transfer and its window restriction are proved from
the entry/cascade/transport inputs already present in the glue statement. -/
theorem finite_strong_entry : FiniteStrongEntryStatement :=
  finite_strong_entry_of_seed_representation finite_seed_representation

end AVRegularity.Finite.Assembly
end
