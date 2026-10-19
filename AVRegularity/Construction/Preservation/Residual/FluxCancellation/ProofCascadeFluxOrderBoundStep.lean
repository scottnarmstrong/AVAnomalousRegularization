-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredConstantsLift
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.CascadeInvariants.Scales

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound

/-! Tools of the step of the cascade flux order bound.

`transferAt_eq_zero_window`: the transfer to the coarser chart only lowers the orders
(`transportedCoeff` sums the finer orders `d ≥ d'`), and reads the finer output of the slot `k`
only at the times of its pulse window (the cutoff of the slot vanishes elsewhere). Schedule
arithmetic of `succSchedD`, grades of `succComp`, and the bound `a, a' ≤ p` of the covariance
letters of the alphabet. The step is `orderBound_step'` and the induction
`cascadeFluxOrderBound`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem fluxCoeff_zero_op (d : ℕ) (I : DerivativeWord2 (d - 1)) (y : Vec 2) :
    fluxCoeff (fun _ _ => (0 : Vec 2)) d I y = 0 := by
  simp [fluxCoeff]

theorem fluxOrderLE_dite (K : ℕ) {hA : Prop} {inst : Decidable hA}
    (L : hA → (Vec 2 → ℝ) → Vec 2 → Vec 2) (h : ∀ h, FluxOrderLE K (L h)) :
    FluxOrderLE K (@dite _ hA inst (fun hh => L hh) (fun _ => fun _ _ => (0 : Vec 2))) := by
  by_cases hA' : hA
  · simp only [hA', ↓reduceDIte]; exact h hA'
  · simp only [hA', ↓reduceDIte]
    intro d I _
    exact fluxCoeff_zero_op d I 0

/-- The transfer of a finer output whose orders vanish above `K` at the times of the pulse windows
has no array of order above `K`: the slot `k` enters with its cutoff, which vanishes off its
window. -/
theorem transferAt_eq_zero_window (D : OCData) (m : ℕ) (pc : ℤ) (lam : ℝ) (Dγ : ℕ)
    (fop : FamFluxOp) (hτ : 0 < ocTau D.α D.q D.Λ m) (K : ℕ)
    (h : ∀ k τ A, τ ∈ ocPulseWindow D.α D.q D.Λ m k → FluxOrderLE K (fop k τ A)) (t : ℝ)
    (ch : RealChain) (z : Vec 2) (d' : ℕ) (β : DerivativeWord2 (d' - 1)) (hd : K < d') :
    transferAt D m pc lam Dγ fop t ch z d' β = 0 := by
  unfold transferAt
  have hd1 : d' - 1 + 1 = d' := by omega
  apply smul_eq_zero_of_right
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  by_cases hcut : ocCutoff D.α D.q D.Λ m k t = 0
  · simp only [hcut, zero_smul, finsum_zero]
  · have hw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
    have hz : transportedCoeff
        (fun h => (childTransition D k t (RealChain.recenter D ch h)
          (z + (D.eps (m - 1))⁻¹ • h))⁻¹) Dγ
        (fun d I => fluxCoeff (fop k t (RealChain.appendChild D ch k t z)) d I 0) (d' - 1) β 0 =
        0 := by
      unfold transportedCoeff
      funext a₀
      simp only [Pi.zero_apply]
      refine Finset.sum_eq_zero fun d hdm => ?_
      refine Finset.sum_eq_zero fun I _ => ?_
      refine Finset.sum_eq_zero fun i₀ _ => ?_
      have hdd : K < d := by
        have := (Finset.mem_Icc.1 hdm).1
        omega
      have := h k t (ch.appendChild D k t z) hw d I hdd
      rw [this]
      simp
    simp only [hz, smul_zero, finsum_zero]

theorem succSchedD_mono' (D₀ N p : ℕ) {g g' : ℕ} (h : g ≤ g') :
    succSchedD D₀ N p g ≤ succSchedD D₀ N p g' := by
  rw [succSchedD_eq, succSchedD_eq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem succSchedD_succ' (D₀ N p g : ℕ) :
    succSchedD D₀ N p (g + 1) = succSchedD D₀ N p g + 2 * N + 4 * p + 4 := rfl

theorem compGrade_le_succComp (m : ℕ) (c : Comp) (t : List WordLetter) :
    compGrade c ≤ compGrade (succComp m c t) := by
  by_cases ht : t = []
  · subst ht; rw [Providers.CascadeInvariants.compGrade_succComp_nil]
  · rw [Providers.CascadeInvariants.compGrade_succComp_ne m c ht]; omega

theorem cov_mem_le {nMax hMax p npad n h a a' : ℕ}
    (hm : WordLetter.covariance n h a a' ∈ succAlphabet nMax hMax p npad) : a ≤ p ∧ a' ≤ p := by
  simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc, reduceCtorEq,
    false_or, WordLetter.covariance.injEq] at hm
  rcases hm with (⟨_, _, hf⟩ | ⟨x, ⟨⟨_, hx1, hx2⟩, _⟩, _, _, e2, e3⟩) | ⟨_, _, hf⟩
  · exact hf.elim
  · omega
  · exact hf.elim
end

/-! The direct copy has no array above the order of its identity: the ordered
derivative of order `m < r` of a monomial of degree `r` vanishes at the origin (homogeneity), so
`directFlux` against the monomial test of degree `d - 1` sees only the order `d`. -/

section
/-- The ordered derivative of order `m < r` of a monomial of degree `r` vanishes at `0`. -/
theorem orderedDerivative_monomial_zero {m r : ℕ} (hmr : m < r) (β : DerivativeWord2 m)
    (I : DerivativeWord2 r) :
    orderedDerivative β (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 = 0 := by
  set F : Vec 2 → ℝ := fun Y => ∏ j, (Y - 0) (I j) with hF
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := by
    simp only [hF, sub_zero]
    exact contDiff_prod fun j _ => contDiff_apply ℝ ℝ (I j)
  have hhom : (F ∘ ((2 : ℝ) • ContinuousLinearMap.id ℝ (Vec 2))) = (2 : ℝ) ^ r • F := by
    funext Y
    simp [hF, Finset.prod_mul_distrib, Finset.prod_const]
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_right
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (Vec 2)) hFs (0 : Vec 2) (i := m) (by exact_mod_cast le_top)
  rw [hhom] at h1
  have h2 : iteratedFDeriv ℝ m ((2 : ℝ) ^ r • F) 0 =
      (2 : ℝ) ^ r • iteratedFDeriv ℝ m F 0 :=
    iteratedFDeriv_const_smul_apply (hFs.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [h2] at h1
  have h3 : (iteratedFDeriv ℝ m F 0) (fun i => basisVec (β (Fin.rev i))) = 0 := by
    have h4 := congrArg (fun T => T (fun i => basisVec (β (Fin.rev i)))) h1
    simp only [smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.id_apply, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul] at h4
    rw [smul_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h4
    have hne : (2 : ℝ) ^ r ≠ (2 : ℝ) ^ m := by
      intro h
      exact absurd (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h)) (by omega)
    by_contra hT
    exact hne (mul_right_cancel₀ hT h4)
  rw [orderedDerivative_eq_iteratedFDeriv β (hFs.of_le (by exact_mod_cast le_top))]
  exact h3

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The direct copy** (statement `DirectOrderStatement`). -/
theorem directOrder : DirectOrderStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro G v u γ E hE p c t d I hd
  unfold fluxCoeff directFlux
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun d'' hd'' => ?_)
  refine Finset.sum_eq_zero fun β _ => ?_
  have h3 : 3 ≤ d'' := (Finset.mem_Icc.1 hd'').1
  by_cases hle : d'' ≤ E
  · have h0 := orderedDerivative_monomial_zero (m := d'' - 1) (r := d - 1) (by omega) β I
    rw [h0]; simp
  · have hz := hE p c d'' β (by omega) (by omega)
    simp [hz, fieldCellMean]
end

/-! One actual successor preserves the flux order bound: by
cases on the source of the identity of the extended successor, through the source bijection of
`IsActualSuccessor`, and on the recorded order `R` of the new identity (its `maxOrder`, by `HasTags`
of the successor and the provenance clause).

* `d > R`: the array vanishes by `flux_zero`. This disposes of the quadratic conversions (`R = 2`)
  and of the first source (`R = N + 1 + 4p`, below the bound `D_{g+1}` of its target).
* A direct copy: `directOrder`, from the bound of the incoming stage.
* A mean letter (`R = n`) or a covariance letter (`R = n + 2(a + a') ≤ n + 4p`) with `d ≤ R` and
  `d > D_{g+1} = D_g + 2N + 4p + 4`: the degree is `n > N + max 2 D_g`, and the finer output has no
  coefficient at all (`MeanHighDegreeStatement`, `CovHighDegreeStatement`), at the times of the
  pulse windows, which are the only times the transfer reads (`transferAt_eq_zero_window`).

No certificate of the incoming stage is used: its order bound and the lift relation of the step
only. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The order bound of a stage: the arrays of orders `d > max 2 D_g` into a component of grade `g`
vanish. -/
def OrdIH (G : GenStage D hr Dm b j₀) (D₀ N p : ℕ) : Prop :=
  ∀ (pp : OddSlot) (c : StageCtx D b j₀ G.level pp) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)), 2 < d → succSchedD D₀ N p (compGrade v.1) < d →
      G.fam.flux pp c v u γ d I = fun _ _ _ => 0

/-- One actual successor preserves the order bound; no certificate of `G`. -/
theorem orderBound_step' (P : ProvParams) (Mn : SuccMenu) (D₀ hMax npad : ℕ)
    (hPN : P.N = Mn.N) (hPp : P.p = Mn.p)
    (hA : Mn.A = succAlphabet (Mn.N + succSchedD D₀ Mn.N Mn.p Mn.H) hMax Mn.p npad)
    (G G' : GenStage D hr Dm b j₀) (hsucc : IsActualSuccessor D P Mn G G')
    (hgm : ∀ v u : CompIn G.comps, Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hsX : Dm ≤ Mn.sX) (hsZ : Dm ≤ Mn.sZ) (ih : OrdIH G D₀ Mn.N Mn.p)
    (hmean : MeanHighDegreeStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (hcov : CovHighDegreeStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀)) :
    OrdIH G' D₀ Mn.N Mn.p := by
  obtain ⟨-, -, -, -, htags, -, e, Cc, Cc0, hCc, -, hmain⟩ := hsucc
  intro pp c v' u' γ' d I hd2 hdD
  have hm := hmain v' u' γ'
  have hes := (e v' u' γ').2
  have hrec : (G'.fam.identity v' u' γ').maxOrder =
      (((e v' u' γ').1.prov G.level).tags P).order := by
    rw [← hm.1]
    exact (htags v' u' γ').2
  generalize e v' u' γ' = es at hm hes hrec
  obtain ⟨s, hs⟩ := es
  obtain ⟨-, -, hnd, -⟩ := hm
  obtain ⟨hval, -, hgrade⟩ := hes
  change (G'.fam.identity v' u' γ').maxOrder = ((s.prov G.level).tags P).order at hrec
  have hg' : compGrade v'.1 = compGrade (succComp G.level s.oldTgt s.newWord) := by
    rw [← hgrade]; rfl
  -- above the recorded order of the source: `flux_zero`
  have hz : ((s.prov G.level).tags P).order < d →
      G'.fam.flux pp c v' u' γ' d I = fun _ _ _ => 0 := by
    intro hlt
    refine G'.fam.flux_zero pp c v' u' γ' d I fun h => ?_
    have := h.2
    omega
  have key : ¬ s.IsDiag → ∀ K, (∀ k τ A, τ ∈ ocPulseWindow D.α D.q D.Λ G.level k →
      FluxOrderLE K (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (Cc s) k τ A)) →
      K < d → G'.fam.flux pp c v' u' γ' d I = fun _ _ _ => 0 := by
    intro hnd' K hK hKd
    funext t X z
    rw [hnd hnd' pp c d I t X z hd2.le]
    split_ifs
    · exact transferAt_eq_zero_window _ _ _ _ _ _ (Construction.Stream.ocTau_pos hΛ) K hK _ _ _ _
        _ hKd
    · rfl
  have hadd := succSchedD_succ' D₀ Mn.N Mn.p
  cases s with
  | copyDir t v u γ0 =>
    have hgr : compGrade v.1 ≤ compGrade v'.1 := by
      rw [hg']; exact compGrade_le_succComp _ _ _
    have hmo := succSchedD_mono' D₀ Mn.N Mn.p hgr
    refine key (by simp [SuccSource.IsDiag]) (max 2 (succSchedD D₀ Mn.N Mn.p (compGrade v.1)))
      ?_ (by omega)
    intro k τ A _
    unfold SuccSource.fluxOp
    apply fluxOrderLE_dite
    intro hA'
    exact directOrder G v u γ0 _ (fun p' c' d' I' h2 hE => ih p' c' v u γ0 d' I' h2 hE) _ _ _
  | copyQuad t h π =>
    refine hz ?_
    have h2 : (((SuccSource.copyQuad t h π).prov G.level).tags P).order = 2 := by
      simp only [SuccSource.prov, Prov.tags]
      split <;> rfl
    rw [h2]
    exact hd2
  | letterDiag t u =>
    have hgr : compGrade v'.1 = compGrade u.1 + 1 := by
      rw [hg']; exact Providers.CascadeInvariants.compGrade_succComp_ne _ _ (by simp [SuccSource.newWord,
        SuccSource.letter?])
    rw [hgr, hadd] at hdD
    refine hz ?_
    have h2 : (((SuccSource.letterDiag t u : SuccSource G).prov G.level).tags P).order =
        P.N + 1 + 4 * P.p := by
      simp only [SuccSource.prov, Prov.tags, letterOrder]
    rw [h2, hPN, hPp]
    omega
  | letterMean t n h π =>
    by_cases hdn : n < d
    · refine hz ?_
      have h2 : (((SuccSource.letterMean t n h π).prov G.level).tags P).order = n := by
        simp only [SuccSource.prov, Prov.tags, letterOrder]
      rw [h2]
      exact hdn
    · have hgr : compGrade v'.1 = compGrade π.tgt + 1 := by
        rw [hg']; exact Providers.CascadeInvariants.compGrade_succComp_ne _ _ (by simp [SuccSource.newWord,
          SuccSource.letter?])
      have hev : ∀ j, EdgeVanish G (succSchedD D₀ Mn.N Mn.p (compGrade π.tgt)) (π.step j).2.2 :=
        fun j p' c' d' I' h2 hE => ih p' c' (π.step j).1 (π.step j).2.1 (π.step j).2.2 d' I' h2
          (lt_of_le_of_lt (succSchedD_mono' _ _ _
            (Providers.CascadeInvariants.stagePath_grade_step_le_tgt hgm π j)) hE)
      rw [hgr, hadd] at hdD
      refine key (by simp [SuccSource.IsDiag]) 0 ?_ (by omega)
      intro k τ A hτ
      exact hmean G Mn t n h π (Cc (.letterMean t n h π)) _ hΛ hζ hκ hsX hsZ hev (hCc _)
        (by omega) k τ A hτ
  | letterCov t n h a a' π =>
    by_cases hdn : n + 2 * (a + a') < d
    · refine hz ?_
      have h2 : (((SuccSource.letterCov t n h a a' π).prov G.level).tags P).order =
          n + 2 * (a + a') := by
        simp only [SuccSource.prov, Prov.tags, letterOrder]
      rw [h2]
      exact hdn
    · have hgr : compGrade v'.1 = compGrade π.tgt + 1 := by
        rw [hg']; exact Providers.CascadeInvariants.compGrade_succComp_ne _ _ (by simp [SuccSource.newWord,
          SuccSource.letter?])
      have hev : ∀ j, EdgeVanish G (succSchedD D₀ Mn.N Mn.p (compGrade π.tgt)) (π.step j).2.2 :=
        fun j p' c' d' I' h2 hE => ih p' c' (π.step j).1 (π.step j).2.1 (π.step j).2.2 d' I' h2
          (lt_of_le_of_lt (succSchedD_mono' _ _ _
            (Providers.CascadeInvariants.stagePath_grade_step_le_tgt hgm π j)) hE)
      have hmem := (hval.2.1 (.covariance n h a a') rfl).2
      rw [hA] at hmem
      obtain ⟨ha, ha'⟩ := cov_mem_le hmem
      rw [hgr, hadd] at hdD
      refine key (by simp [SuccSource.IsDiag]) 0 ?_ (by omega)
      intro k τ A hτ
      exact hcov G Mn t n h a a' π (Cc (.letterCov t n h a a' π)) _ hΛ hζ hκ hsX hsZ hev (hCc _)
        (by omega) k τ A hτ
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound
end
