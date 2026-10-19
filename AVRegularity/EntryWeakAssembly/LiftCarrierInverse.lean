-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.RelabelStage
public import AVRegularity.EntryWeakAssembly.MeanLeftTermsLocalCongruence
import AVRegularity.EntryWeakAssembly.WindowListL2Representative
import AVRegularity.EntryWeakAssembly.WindowFieldExtension
public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Exact edge equivalences preserve graph depth under weak rerooting. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakEncoding_depth (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι)
    (H : ℕ) (hG : G.fam.HasDepthAtMost H) : Gw.fam.HasDepthAtMost H := by
  obtain ⟨_Cθ, e, _idx, _hCθ, _hinj, _hdata⟩ := he.2.2.2.2.2.2
  intro p
  obtain ⟨k, hk⟩ := hG (fun j => ι.symm (p j))
  refine ⟨k, ⟨?_⟩⟩
  intro γ
  have heq : Gw.fam.Γ (ι (ι.symm (p k.succ))) (ι (ι.symm (p k.castSucc))) =
      Gw.fam.Γ (p k.succ) (p k.castSucc) := by simp only [Equiv.apply_symm_apply]
  let γ' := cast heq.symm γ
  let old := (e (ι.symm (p k.succ)) (ι.symm (p k.castSucc))).symm γ'
  exact hk.false old
end

/-! Exact weak rerooting preserves orders, lengths, widths, seed provenance, and the bound of the
identity maps. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakEncoding_orders_records (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι)
    (K : ℕ) (length width : ℝ) (ho : G.maxOrderBound K)
    (hr : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.length = length ∧
      (G.fam.identity v u γ).record.width = width) :
    Gw.maxOrderBound K ∧
      (∀ v u (γ : Gw.fam.Γ v u), (Gw.fam.identity v u γ).record.length = length ∧
        (Gw.fam.identity v u γ).record.width = width) ∧
      (∀ v u (γ : Gw.fam.Γ v u), ∃ k tag, Gw.prov v u γ = .seed k tag) := by
  obtain ⟨Cθ, e, idx, _hCθ, _hinj, hd⟩ := he.2.2.2.2.2.2
  have trans (v' u' : CompIn Gw.comps) (γ' : Gw.fam.Γ v' u') :
      (Gw.fam.identity v' u' γ').maxOrder ≤ K ∧
      ((Gw.fam.identity v' u' γ').record.length = length ∧
        (Gw.fam.identity v' u' γ').record.width = width) ∧
      (∃ k tag, Gw.prov v' u' γ' = .seed k tag) := by
    obtain ⟨v, rfl⟩ := ι.surjective v'
    obtain ⟨u, rfl⟩ := ι.surjective u'
    obtain ⟨γ, rfl⟩ := (e v u).surjective γ'
    rcases hd v u γ with ⟨⟨tag, _hp, hq⟩, _hmap, _hsize, _hbirthLevel,
      _hbirthExcess, hlength, hwidth, _hbirths, horder, _hflux⟩
    refine ⟨?_, ?_, idx v u γ, { tag with size := Cθ * tag.size }, hq⟩
    · rw [horder]
      exact ho v u γ
    · rw [hlength, hwidth]
      exact hr v u γ
  exact ⟨fun v u γ => (trans v u γ).1,
    (fun v u γ => (trans v u γ).2.1), fun v u γ => (trans v u γ).2.2⟩

/-- Exact weak rerooting preserves the bound of the identity maps. -/
theorem weakEncoding_map_norm_le_one (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι)
    (hm : ∀ v u (γ : G.fam.Γ v u), ‖(G.fam.identity v u γ).map‖ ≤ 1)
    (v' u' : CompIn Gw.comps) (γ' : Gw.fam.Γ v' u') :
    ‖(Gw.fam.identity v' u' γ').map‖ ≤ 1 := by
  obtain ⟨_Cθ, e, _idx, _hCθ, _hinj, hd⟩ := he.2.2.2.2.2.2
  obtain ⟨v, rfl⟩ := ι.surjective v'
  obtain ⟨u, rfl⟩ := ι.surjective u'
  obtain ⟨γ, rfl⟩ := (e v u).surjective γ'
  rw [(hd v u γ).2.1]
  exact hm v u γ
end

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Inflation of seed witnesses leaves the independent fields and all geometric tags intact. -/

section
/-- Only the witness of a seed is inflated. Other provenance constructors are unchanged. -/
def scaleWeakSeedProv (C : ℝ) : Prov → Prov
  | .seed k tag => .seed k { tag with size := C * tag.size }
  | p => p

private theorem scaleWeakSeedProv_leftInverse (C : ℝ) (hC : C ≠ 0) (p : Prov) :
    scaleWeakSeedProv C⁻¹ (scaleWeakSeedProv C p) = p := by
  cases p with
  | seed k tag =>
    cases tag
    simp only [scaleWeakSeedProv, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  | dir => rfl
  | quad => rfl
  | letter => rfl

theorem scaleWeakSeedProv_injective (C : ℝ) (hC : C ≠ 0) :
    Function.Injective (scaleWeakSeedProv C) :=
  Function.LeftInverse.injective (scaleWeakSeedProv_leftInverse C hC)

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Change record sizes and seed witnesses by one common positive factor. -/
def scaleWeakSeedStage (G : GenStage D ScalarH Dm b j₀) (C : ℝ) (hC : 0 ≤ C) :
    GenStage D ScalarH Dm b j₀ :=
  { G with
    fam := { G.fam with identity := fun v u γ =>
      { G.fam.identity v u γ with record :=
        { (G.fam.identity v u γ).record with
          size := C * (G.fam.identity v u γ).record.size
          size_nonneg := mul_nonneg hC (G.fam.identity v u γ).record.size_nonneg } } }
    prov := fun v u γ => scaleWeakSeedProv C (G.prov v u γ) }

theorem scaleWeakSeedStage_isNatural (G : GenStage D ScalarH Dm b j₀)
    (C : ℝ) (hC : 0 < C) (M : ℕ) (hG : G.IsNatural M) :
    (scaleWeakSeedStage G C hC.le).IsNatural M := by
  refine ⟨hG.1, hG.2.1, hG.2.2.1, ?_⟩
  intro v u
  exact (scaleWeakSeedProv_injective C hC.ne').comp (hG.2.2.2 v u)

theorem scaleWeakSeedStage_hasTags (G : GenStage D ScalarH Dm b j₀)
    (C : ℝ) (hC : 0 ≤ C) (P : ProvParams) (hG : G.HasTags P)
    (hs : ∀ v u (γ : G.fam.Γ v u), ∃ k tag, G.prov v u γ = .seed k tag) :
    (scaleWeakSeedStage G C hC).HasTags P := by
  intro v u γ
  obtain ⟨k, tag, ht⟩ := hs v u γ
  have hh := hG v u γ
  rw [ht] at hh
  change (Prov.tags P (scaleWeakSeedProv C (G.prov v u γ))).Matches _ ∧
    (G.fam.identity v u γ).maxOrder = (Prov.tags P (scaleWeakSeedProv C (G.prov v u γ))).order
  rw [ht]
  change (Prov.tags P (.seed k { tag with size := C * tag.size })).Matches _ ∧ _
  exact ⟨⟨congrArg (C * ·) hh.1.1, hh.1.2.1, hh.1.2.2.1, hh.1.2.2.2.1,
    hh.1.2.2.2.2.1, hh.1.2.2.2.2.2⟩, hh.2⟩

theorem scaleWeakSeedStage_isShiftInvariant (G : GenStage D ScalarH Dm b j₀)
    (C : ℝ) (hC : 0 ≤ C) (hG : G.IsShiftInvariant) :
    (scaleWeakSeedStage G C hC).IsShiftInvariant := hG

theorem scaleWeakSeedStage_isSlotTransverse (G : GenStage D ScalarH Dm b j₀)
    (C : ℝ) (hC : 0 ≤ C) (hG : G.IsSlotTransverse) :
    (scaleWeakSeedStage G C hC).IsSlotTransverse := hG

/-- Relabeling transports all four structural laws literally. -/
theorem relabelWeakStage_laws (G : GenStage D ScalarH Dm b j₀) (S : Finset Comp)
    (e : CompIn G.comps ≃ CompIn S) (M : ℕ) (P : ProvParams) :
    (G.IsNatural M → (relabelWeakStage G S e).IsNatural M) ∧
    (G.HasTags P → (relabelWeakStage G S e).HasTags P) ∧
    (G.IsShiftInvariant → (relabelWeakStage G S e).IsShiftInvariant) ∧
    (G.IsSlotTransverse → (relabelWeakStage G S e).IsSlotTransverse) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, fun v u => h.2.2.2 (e.symm v) (e.symm u)⟩
  · intro h v u γ
    exact h (e.symm v) (e.symm u) γ
  · intro h
    exact ⟨fun p c c' n hc v u γ d I => h.1 p c c' n hc (e.symm v) (e.symm u) γ d I,
      fun p c c' n h0 hc v u γ d I => h.2 p c c' n h0 hc (e.symm v) (e.symm u) γ d I⟩
  · intro h p c v u γ d I t ht X z s
    exact h p c (e.symm v) (e.symm u) γ d I t ht X z s
end

/-! The finite downward induction for the complete positive stored-weight sum. -/

section
open Homogenization
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Iterating the menu recurrence costs at most `(2Q)^J`. -/
theorem weakConstruction_storedTotal_stage_bound (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D (fun _ => ℝ) Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J)
    (heps : ∀ i, 0 < D.eps i) (e : ℝ) (he : 0 ≤ e)
    (hed : ∀ i, M < i → i ≤ M + J → weakStoredEddyWeight D Mn.N J Mn.η0 i ≤ e)
    (hsmall : (2 * (weakStoredPassageBudget Mn.N J Mn.R : ℝ)) ^ J * e ≤ 1) :
    ∀ n, n ≤ J → weakStoredTotal (stage (M + J - n)) Mn.N J Mn.η0 ≤
      (2 * (weakStoredPassageBudget Mn.N J Mn.R : ℝ)) ^ n * e := by
  let Q : ℝ := weakStoredPassageBudget Mn.N J Mn.R
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast weakStoredPassageBudget_one_le Mn.N J Mn.R
  have h2Q : 1 ≤ 2 * Q := le_trans hQ (le_mul_of_one_le_left (by positivity) (by norm_num))
  intro n
  induction n with
  | zero =>
    intro _
    have hroot := hc.2.1.2.2.1
    have hzero : weakStoredTotal (stage (M + J)) Mn.N J Mn.η0 = 0 := by
      unfold weakStoredTotal
      apply Finset.sum_eq_zero
      intro a _
      exact (hroot a.1 a.2.1).false a.2.2 |>.elim
    simpa only [Nat.sub_zero, pow_zero, one_mul, hzero] using he
  | succ n ih =>
    intro hn
    let i := M + J - n
    have hi : M < i := by dsimp [i]; omega
    have hit : i ≤ M + J := by dsimp [i]; omega
    have hlevel := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc i hi.le hit
    have ht := EntryWeakProofs.weakConstruction_stage_hasTags P Mn M J r rW hc i hi.le hit
    have hp := hc.2.2 i hi hit
    have hnJ : n ≤ J := by omega
    have hh := ih hnJ
    have hpow := pow_le_pow_right₀ h2Q hnJ
    have hsm : weakStoredTotal (stage i) Mn.N J Mn.η0 ≤ 1 :=
      hh.trans ((mul_le_mul_of_nonneg_right hpow he).trans hsmall)
    have hpath := EntryWeakProofs.weakConstruction_path_length_bound P Mn M J r rW stage hc i hi.le hit
    have hcomp := weakConstruction_card_le P Mn M J r rW stage hc i hi.le hit
    have hstep := weakStoredTotal_passage_uniform P Mn J (1 + (M + J - i) * Mn.N)
      rW (stage i) (stage (i - 1)) hp.1 ht hp.2 hN hJ heps hpath hsm hcomp
      (by apply Nat.add_le_add_left; exact Nat.mul_le_mul_right _ (by omega))
    rw [hlevel] at hstep
    have hepow : e ≤ (2 * Q) ^ n * e := le_mul_of_one_le_left he (one_le_pow₀ h2Q)
    have hbound := hstep.trans (mul_le_mul_of_nonneg_left
      (add_le_add hh ((hed i hi hit).trans hepow)) (by positivity : 0 ≤ Q))
    have hidx : M + J - (n + 1) = i - 1 := by dsimp [i]; omega
    rw [hidx]
    calc
      _ ≤ Q * ((2 * Q) ^ n * e + (2 * Q) ^ n * e) := hbound
      _ = (2 * Q) ^ (n + 1) * e := by rw [pow_succ]; ring


/-- The output-stage specialization of the uniform finite induction. -/
theorem weakConstruction_storedTotal_bound (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D (fun _ => ℝ) Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J)
    (heps : ∀ i, 0 < D.eps i) (e : ℝ) (he : 0 ≤ e)
    (hed : ∀ i, M < i → i ≤ M + J → weakStoredEddyWeight D Mn.N J Mn.η0 i ≤ e)
    (hsmall : (2 * (weakStoredPassageBudget Mn.N J Mn.R : ℝ)) ^ J * e ≤ 1) :
    weakStoredTotal (stage M) Mn.N J Mn.η0 ≤
      (2 * (weakStoredPassageBudget Mn.N J Mn.R : ℝ)) ^ J * e := by
  simpa only [Nat.add_sub_cancel] using
    weakConstruction_storedTotal_stage_bound P Mn M J r rW stage hc hN hJ heps e he hed hsmall J le_rfl
end

/-! Canonical identities for actual weak source edges retain the whole seed record. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def weakSourceCoefficientIdentity (G : GenStage D ScalarH Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (S : Finset Comp) (m N R Din : ℕ) (hDin : 1 ≤ Din)
    (hDm : N + Din ≤ Dm) (rW η : ℝ) (heps : ∀ i, 0 < D.eps i) (hrW : 0 < rW)
    (v u : CompIn S) (γ : weakSourceEdge G S m N R Din v u) :
    CoefficientIdentity Dm (ScalarH u.1.root) (ScalarH v.1.root) where
  map := rootPathMap ScalarH u.1.root [] v.1.root
  record := weakSourceRecord G P ht m rW η heps hrW γ.1
  maxOrder := γ.1.degree
  two_le := (weakSource_degree_bounds G N R Din hDin γ.1 γ.2.1).1
  le_D := (weakSource_degree_bounds G N R Din hDin γ.1 γ.2.1).2.trans hDm
  le_birth := by
    have hn := (weakSource_degree_bounds G N R Din hDin γ.1 γ.2.1).1
    have he : (weakSourceRecord G P ht m rW η heps hrW γ.1).birthExcess = γ.1.degree - 2 := by
      cases γ.1 <;> rfl
    rw [he, Nat.sub_add_cancel hn]
end

/-! An actual seed-labeled weak stage admits the prescribed root encoding. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakRootEncoding (N J : ℕ) (η : ℝ) (G : GenStage D ScalarH Dm b j₀)
    (idx : ∀ v u, G.fam.Γ v u → ℕ)
    (hinj : ∀ v u (γ : G.fam.Γ v u) v' u' (γ' : G.fam.Γ v' u'),
      idx v u γ = idx v' u' γ' → v = v' ∧ u = u' ∧ HEq γ γ')
    (hseed : ∀ v u (γ : G.fam.Γ v u), ∃ tag, G.prov v u γ = .seed (idx v u γ) tag) :
    IsWeakEncoding N J η
      (weakRootWeight G.comps (fun v => weakMass D N J η v.1))
      (weakRootWeight G.comps (fun v => weakReadoutWeight D η v.1))
      G (relabelWeakStage G (weakRootComps G.comps) (weakRootEquiv G.comps))
      (weakRootEquiv G.comps) := by
  refine ⟨rfl, weakRootEquiv_births _, ?_, (fun _ => rfl), (fun _ => rfl),
    (fun _ _ => rfl), 1, relabelWeakEdge G _ _, idx, le_rfl, hinj, ?_⟩
  · intro v
    change weakRootWeight G.comps _ (weakRootLabel G.comps v) = _ ∧
      weakRootWeight G.comps _ (weakRootLabel G.comps v) = _
    exact ⟨weakRootWeight_label _ _ _, weakRootWeight_label _ _ _⟩
  · intro v u γ
    obtain ⟨tag, ht⟩ := hseed v u γ
    have hid := relabelWeakStage_identity G _ (weakRootEquiv G.comps) v u γ
    have hrec := congrArg CoefficientIdentity.record hid
    refine ⟨⟨tag, ht, ?_⟩, congrArg CoefficientIdentity.map hid, ?_,
      congrArg ConstituentRecord.birthLevel hrec, congrArg ConstituentRecord.birthExcess hrec,
      congrArg ConstituentRecord.length hrec, congrArg ConstituentRecord.width hrec,
      congrArg ConstituentRecord.births hrec, congrArg CoefficientIdentity.maxOrder hid, ?_⟩
    · rw [one_mul]
      cases tag
      exact (relabelWeakStage_prov G _ (weakRootEquiv G.comps) v u γ).trans ht
    · rw [one_mul]
      exact congrArg ConstituentRecord.size hrec
    · intro p c c' hc d I t X z
      have hcc : c = c' := Subtype.ext hc
      subst c'
      exact congrFun (congrFun (congrFun (congrFun (congrFun
        (relabelWeakStage_flux G _ (weakRootEquiv G.comps) v u γ p c) d) I) t) X) z
end

/-! Almost measurable finite-window sources produce the actual raw molecular solution. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution

theorem molecular_exists_raw_ae {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (initial : ComplexCellL2) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Icc a b) (dataCoefficients P) src F D ∧
      cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] initial := by
  have hS := cellSourceSlice_memLp (Icc a b) src hsrc
  have hflux (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun t x => F t x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  obtain ⟨u, slice, h, hi⟩ := molecular_exists_Hilbert_sources hab P (cellSourceSlice src) hS
    (fun t j => cellSourceSlice (fun s x => F s x j) t) hflux initial
  obtain ⟨D, hD, he⟩ := dataWeakHilbert_exists_raw_solution P src F hsrc hF u slice h
  exact ⟨D, hD, (he a).symm.trans (Filter.EventuallyEq.of_eq
    (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) hi))⟩

theorem molecular_exists_zero_raw_ae {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Icc a b) (dataCoefficients P) src F D ∧
      cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] (fun _ => 0) := by
  obtain ⟨D, hD, hi⟩ := molecular_exists_raw_ae hab P src F hsrc hF 0
  exact ⟨D, hD, hi.trans (by simpa using! (Lp.coeFn_zero ℂ 2
    (volume.restrict AVenhance.unitCube)))⟩
end

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs

/-! Produced higher word states uniformly bound every genuine metric perturbation source. -/

open AVRegularity.EntryWeakProofs
variable {I Y : Type*}

theorem uniform_word_window_perturbed_higher_source_exists (a b : ℝ) (hab : a ≤ b) (N K : ℕ)
    (A : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (E : Y → List I → ℝ → RawJet2 1 ℂ)
    (C : Y → CellCoefficients)
    (f : Y → List I → ℝ → Vec 2 → ℂ)
    (F : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (hE : ∀ y w, w.length ≤ N → IsCellSolution (Icc a b) (C y) (f y w) (F y w) (E y w))
    (B : List I → ℝ) (hB : ∀ w, w.length ≤ N → 0 ≤ B w)
    (hb : ∀ y w, w.length ≤ N → ∀ t i j, |A y w t i j| ≤ B w)
    (hm : ∀ y w, w.length ≤ N → ∀ i j, Measurable (fun t => A y w t i j))
    (w : List I) (hw : w.length ≤ N)
    (hcarrier : ∀ u : List I, u.length ≤ w.length →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ v : ℝ → TorusHk (K + 1) ℂ,
        StronglyMeasurable v ∧ (∀ t, ‖v t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (v t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (E y u) t)
    (src : Y → ℝ → Vec 2 → ℂ) (flux : Y → ℝ → Vec 2 → ComplexCellVector)
    (Q : ∀ y, HigherSourceCarrierData (Icc a b) K (src y) (flux y))
    (Ns Nf : ℝ) (hNs : 0 ≤ Ns) (hNf : 0 ≤ Nf)
    (hQs : ∀ y, (Q y).Ns ≤ Ns) (hQf : ∀ y, (Q y).Nf ≤ Nf) :
    ∃ Rs Rf : ℝ, 0 ≤ Rs ∧ 0 ≤ Rf ∧ ∀ y,
      ∃ Qnext : HigherSourceCarrierData (Icc a b) K (src y)
        ((flux y + independentWordMetricFlux (fun p t _ => A y p t) (E y) w) +
          cellMetricFlux (fun t _ => A y [] t) (E y w)), Qnext.Ns ≤ Rs ∧ Qnext.Nf ≤ Rf := by
  classical
  have hall (u : List I) : ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ v : ℝ → TorusHk (K + 1) ℂ,
      StronglyMeasurable v ∧ (∀ t, ‖v t‖ ≤ R) ∧
      (u.length ≤ w.length → ∀ t ∈ Icc a b,
        torusHkValueCLM (v t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (E y u) t) := by
    by_cases hu : u.length ≤ w.length
    · obtain ⟨R, hR, hh⟩ := hcarrier u hu
      refine ⟨R, hR, fun y => ?_⟩
      obtain ⟨v, hvm, hvb, hve⟩ := hh y
      exact ⟨v, hvm, hvb, fun _ => hve⟩
    · exact ⟨0, le_rfl, fun _ => ⟨0, stronglyMeasurable_const,
        (fun _ => by simp), fun h => (hu h).elim⟩⟩
  choose R hR v hvm hvb hve using hall
  let r := ((independentWordForcing w).map
    (fun p => B p.1 * metricGradientCarrierConstant K * R p.2)).sum
  have hr : 0 ≤ r := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hl := independentWordForcing_lengths w p hp
    exact mul_nonneg (mul_nonneg (hB p.1 (by omega)) (metricGradientCarrierConstant_nonneg K)) (hR p.2)
  let Rf := (Nf + r) + B [] * metricGradientCarrierConstant K * R w
  have hRf : 0 ≤ Rf := add_nonneg (add_nonneg hNf hr)
    (mul_nonneg (mul_nonneg (hB [] (by simp)) (metricGradientCarrierConstant_nonneg K)) (hR w))
  refine ⟨Ns, Rf, hNs, hRf, fun y => ?_⟩
  have hAfin u hu := bounded_matrix_field_admissible (A y u) (B u) (hb y u hu) (hm y u hu)
  have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
  obtain ⟨Qt, hts, htf⟩ := (Q y).metricFluxList_exists (independentWordForcing w)
    (fun p => A y p.1) (fun p => E y p.2) (fun p => v p.2 y)
    (fun p => B p.1) (fun p => R p.2)
    (fun p hp => hB p.1 (by have hh := hl p hp; omega)) (fun p _ => hR p.2)
    (fun p hp => hm y p.1 (by have hh := hl p hp; omega))
    (fun p hp => hb y p.1 (by have hh := hl p hp; omega))
    (fun p _ => hvm p.2 y) (fun p _ => hvb p.2 y)
    (fun p hp => (hE y p.2 (by have hh := hl p hp; omega)).2.1)
    (fun p hp => ae_restrict_of_forall_mem measurableSet_Icc (hve p.2 y (by have hh := hl p hp; omega)))
    (fun p hp => cell_window_metric_flux_memLp hab (fun t _ => A y p.1 t)
      (hAfin p.1 (by have hh := hl p hp; omega)).2
      (B p.1) (hB p.1 (by have hh := hl p hp; omega))
      (fun t _ => hb y p.1 (by have hh := hl p hp; omega) t)
      (hE y p.2 (by have hh := hl p hp; omega)))
  let Qnext := Qt.withMetricFlux (A y []) (E y w) (v w y) (B []) (R w)
    (hB [] (by simp)) (hR w) (hm y [] (by simp)) (hb y [] (by simp))
    (hvm w y) (hvb w y)
    ((hE y w hw).2.1)
    (ae_restrict_of_forall_mem measurableSet_Icc (hve w y le_rfl))
    (cell_window_metric_flux_memLp hab (fun t _ => A y [] t) (hAfin [] (by simp)).2
      (B []) (hB [] (by simp)) (fun t _ => hb y [] (by simp) t) (hE y w hw))
  refine ⟨Qnext, ?_, ?_⟩
  · change Qt.Ns ≤ Ns
    rw [hts]
    exact hQs y
  · change Qt.Nf + B [] * metricGradientCarrierConstant K * R w ≤ Rf
    rw [htf]
    exact add_le_add (add_le_add (hQf y) (le_refl r)) (le_refl _)

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! The last actual weak passage supplies a globally injective seed labeling for rerooting. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_seedLabels (P : ProvParams) (Mn : WeakMenu) (M J : ℕ)
    (rW : ℝ) (r : ℕ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (h : IsWeakConstruction D P Mn M J rW r stage) (hJ : 1 ≤ J) :
    ∃ idx : ∀ v u, (stage M).fam.Γ v u → ℕ,
      (∀ v u (γ : (stage M).fam.Γ v u) v' u' (γ' : (stage M).fam.Γ v' u'),
        idx v u γ = idx v' u' γ' → v = v' ∧ u = u' ∧ HEq γ γ') ∧
      ∀ v u (γ : (stage M).fam.Γ v u), ∃ tag, (stage M).prov v u γ = .seed (idx v u γ) tag := by
  have hp := (h.2.2 (M + 1) (by omega) (by omega)).1
  obtain ⟨_, _, _, _, _, e, idx, Cc, Cc0, _hCc, _hCc0, hinj, hd⟩ := hp
  have hm : M + 1 - 1 = M := by omega
  simp only [hm] at idx hinj hd
  exact ⟨idx, hinj, fun v u γ => ⟨_, (hd v u γ).1⟩⟩

theorem weakConstruction_hasRootEncoding (P : ProvParams) (Mn : WeakMenu) (M J : ℕ)
    (rW : ℝ) (r : ℕ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (h : IsWeakConstruction D P Mn M J rW r stage) (hJ : 1 ≤ J) :
    IsWeakEncoding Mn.N J Mn.η0
      (weakRootWeight (stage M).comps (fun v => weakMass D Mn.N J Mn.η0 v.1))
      (weakRootWeight (stage M).comps (fun v => weakReadoutWeight D Mn.η0 v.1))
      (stage M) (relabelWeakStage (stage M) (weakRootComps (stage M).comps)
        (weakRootEquiv (stage M).comps)) (weakRootEquiv (stage M).comps) := by
  obtain ⟨idx, hi, hs⟩ := weakConstruction_seedLabels P Mn M J rW r stage h hJ
  exact weakRootEncoding Mn.N J Mn.η0 (stage M) idx hi hs

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

/-! Finite molecular higher energy includes arbitrary regular divergence sources and bounded transport. -/

open AVRegularity.EntryWeakProofs

theorem molecularFiniteSource_flux_energy (N K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c : FiniteMolecularCoefficients N) (S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
 :
    2 * inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N Unit.unit K (plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => F + dataFiniteFlux N K P t c)
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb c))).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N Unit.unit K c).val) +
      gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1) c).val / 2 ≤
        (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) *
          factorialNormSq ρ (coupledPlainSynthesis N Unit.unit K c).val +
          factorialNormSq ρ S.val + 4 * factorialNormSq ρ F.val := by
  rw [molecularFiniteSource_energy_identity]
  have hsub : (S - dataFiniteTransport N K P t Cv hCv hv hp hb c).val =
    S.val - (dataFiniteTransport N K P t Cv hCv hv hp hb c).val := rfl
  have hadd : (F + dataFiniteFlux N K P t c).val =
      F.val + (dataFiniteFlux N K P t c).val := rfl
  rw [hsub, hadd]
  simp only [sub_eq_add_neg, factorialWeightedJet_add, factorialWeightedJet_neg,
    inner_add_left, inner_neg_left]
  rw [dataFiniteFlux, molecularMetric_factorial_pairing,
    ← coupledPlainGradientHk_factorialNormSq N c Unit.unit K ρ]
  have hh := molecularHigher_spatial_flux_energy K ρ hρ P.G P.metric_coercive t
    (P.v t) Cv hCv hv hp hb (coupledPlainSynthesis N Unit.unit K c) S F
    (coupledPlainGradientHk N c Unit.unit K)
  dsimp only [dataFiniteTransport]
  convert hh using 1
  ring

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Every fixed native history has smooth spacetime metric entries before quantitative restrictions. -/

section
open Homogenization AVRegularity.EntryWeakProofs

theorem jacMatrix_spacetime_entry_smooth {f : ℝ → Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => f p.1 p.2)) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => jacMatrix (f p.1) p.2 i j) := by
  have he : (fun p : ℝ × Vec 2 => jacMatrix (f p.1) p.2 i j) =
      fun p => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) p (0, basisVec j) i := by
    funext p
    change fderiv ℝ (f p.1) p.2 (basisVec j) i = _
    exact congrArg (fun z => z i) (StrainPhysical.fderiv_slice_gen
      (hf.differentiable (by simp)) p.1 p.2 (basisVec j))
  rw [he]
  exact (contDiff_apply ℝ ℝ i).comp
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const)

theorem planar_inverse_entry_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Matrix (Fin 2) (Fin 2) ℝ)
    (hf : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => F X i j))
    (hd : ∀ X, (F X).det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun X => (F X)⁻¹ i j) := by
  have hdet : ContDiff ℝ (⊤ : ℕ∞) (fun X => (F X).det) := by
    simp_rw [Matrix.det_fin_two]
    exact ((hf 0 0).mul (hf 1 1)).sub ((hf 0 1).mul (hf 1 0))
  have hadj : ContDiff ℝ (⊤ : ℕ∞) (fun X => (F X).adjugate i j) := by
    simp_rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hf 1 1
    · exact (hf 0 1).neg
    · exact (hf 1 0).neg
    · exact hf 0 0
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact (hdet.inv hd).mul hadj

theorem familyLiftData_metric_spacetime_smooth {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (A : RealChain)
    (hl : A.slots.length = A.children.length + 1) (ρ : ℝ) (edge : ConstituentEdges Dm h) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => (familyLiftData D m slot A ρ edge).G p.1 p.2 i j) := by
  let J := fun p : ℝ × Vec 2 => jacMatrix
    (fun y => (A.geom D).1 p.1 y (A.geom D).2.2) p.2
  have hJ v w : ContDiff ℝ (⊤ : ℕ∞) (fun p => J p v w) :=
    jacMatrix_spacetime_entry_smooth (f := fun u y => (A.geom D).1 u y (A.geom D).2.2)
      (geom_spacetime_smooth_geom D hζ A (A.geom D).2.2) v w
  have hdet p : (J p).det ≠ 0 :=
    (jac_isUnit_det (actualOffset_inverse_law D A) (geomC1_geom D hζ A)
      p.1 (A.geom D).2.2 p.2).ne_zero
  have hInv v w := planar_inverse_entry_contDiff J hJ hdet v w
  have hs v w : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => (J (D.cellScaleSq m * p.1, (A.geom D).2.1 + ρ • p.2))⁻¹ v w) :=
    (hInv v w).comp ((contDiff_const.mul contDiff_fst).prodMk
      (contDiff_const.add (contDiff_snd.const_smul ρ)))
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × Vec 2 => (A.recenter D (ρ • p.2)).famMetric D (D.cellScaleSq m * p.1) i j)
  simp_rw [metric_recenter_formula D A hl]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  exact ((hs i 0).mul (hs j 0)).add ((hs i 1).mul (hs j 1))
end

/-! The actual weak construction can be rerooted at any common witness inflation. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A further size inflation composes with the factor already present in an encoding. -/
theorem weakEncoding_scaleSeedStage (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι) (C : ℝ) (hC : 1 ≤ C) :
    IsWeakEncoding N J η rootM rootR G (scaleWeakSeedStage Gw C (by positivity)) ι := by
  obtain ⟨hl, hb, hw, ha, hp, hc, C₀, e, idx, hC₀, hi, hd⟩ := he
  refine ⟨hl, hb, hw, ha, hp, hc, C * C₀, e, idx, ?_, hi, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC hC₀
  · intro v u γ
    obtain ⟨⟨tag, hs, ht⟩, hm, hsize, hbl, hbe, hlen, hwidth, hbirths, ho, hf⟩ := hd v u γ
    refine ⟨⟨tag, hs, ?_⟩, hm, ?_, hbl, hbe, hlen, hwidth, hbirths, ho, hf⟩
    · change scaleWeakSeedProv C (Gw.prov (ι v) (ι u) (e v u γ)) = _
      rw [ht]
      simp only [scaleWeakSeedProv, ← mul_assoc]
    · change C * (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.size = _
      rw [hsize, mul_assoc]

/-- Every edge of an encoded family has seed provenance, including with inflated sizes. -/
theorem weakEncoding_seedProvenance (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι) :
    ∀ v u (γ : Gw.fam.Γ v u), ∃ k tag, Gw.prov v u γ = .seed k tag := by
  obtain ⟨C, e, idx, _, _, hd⟩ := he.2.2.2.2.2.2
  intro v' u' γ'
  obtain ⟨v, rfl⟩ := ι.surjective v'
  obtain ⟨u, rfl⟩ := ι.surjective u'
  obtain ⟨γ, rfl⟩ := (e v u).surjective γ'
  obtain ⟨tag, _, ht⟩ := (hd v u γ).1
  exact ⟨idx v u γ, { tag with size := C * tag.size }, ht⟩

/-- The common factor is chosen before laws and observation windows. The stage keeps the
original exports, which may subsequently be replaced by the certified registry producer. -/
def weakScaledRootStage (G : GenStage D ScalarH Dm b j₀) (C : ℝ) (hC : 1 ≤ C) :
    GenStage D ScalarH Dm b j₀ :=
  scaleWeakSeedStage (relabelWeakStage G (weakRootComps G.comps) (weakRootEquiv G.comps))
    C (by positivity)

theorem weakConstruction_scaledRootEncoding (P : ProvParams) (Mn : WeakMenu)
    (M J : ℕ) (rW : ℝ) (r : ℕ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hJ : 1 ≤ J)
    (C : ℝ) (hC : 1 ≤ C) :
    IsWeakEncoding Mn.N J Mn.η0
      (weakRootWeight (stage M).comps (fun v => weakMass D Mn.N J Mn.η0 v.1))
      (weakRootWeight (stage M).comps (fun v => weakReadoutWeight D Mn.η0 v.1))
      (stage M) (weakScaledRootStage (stage M) C hC) (weakRootEquiv (stage M).comps) :=
  weakEncoding_scaleSeedStage _ _ _ _ _ _ _ _
    (weakConstruction_hasRootEncoding P Mn M J rW r stage hc hJ) C hC

theorem weakConstruction_scaledRootLaws (P : ProvParams) (Mn : WeakMenu)
    (M J : ℕ) (rW : ℝ) (r : ℕ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hJ : 1 ≤ J)
    (C : ℝ) (hC : 1 ≤ C) :
    ((stage M).IsNatural (M + J) → (weakScaledRootStage (stage M) C hC).IsNatural (M + J)) ∧
    ((stage M).HasTags P → (weakScaledRootStage (stage M) C hC).HasTags P) ∧
    ((stage M).IsShiftInvariant → (weakScaledRootStage (stage M) C hC).IsShiftInvariant) ∧
    ((stage M).IsSlotTransverse → (weakScaledRootStage (stage M) C hC).IsSlotTransverse) := by
  have hpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have he := weakConstruction_hasRootEncoding P Mn M J rW r stage hc hJ
  have hs := weakEncoding_seedProvenance _ _ _ _ _ _ _ _ he
  have hh := relabelWeakStage_laws (stage M) _ (weakRootEquiv (stage M).comps) (M + J) P
  exact ⟨fun h => scaleWeakSeedStage_isNatural _ C hpos _ (hh.1 h),
    fun h => scaleWeakSeedStage_hasTags _ C hpos.le P (hh.2.1 h) hs,
    fun h => scaleWeakSeedStage_isShiftInvariant _ C hpos.le (hh.2.2.1 h),
    fun h => scaleWeakSeedStage_isSlotTransverse _ C hpos.le (hh.2.2.2 h)⟩
end

/-! Earlier coefficient reserves produce the literal full-cell slow flux. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def fluxFromEarlierReserves (H : ℕ) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (hn : 2 ≤ n) (hhpos : hh ≠ 0) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) (k : Fin 2)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve H (fun t z Y => γ.coeff α t Y z)) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      (liftFluxX Q Cc (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n t Y z k) v) := by
  let Qt := fun p q (hpq : p < hh ∨ (p = hh ∧ q < n)) K (hK : K ≤ H + D + 2) w =>
    normalizedScalarLiftTestReserve K q (Cc p q) A w u
      (fun m α x => (Qc p q hpq m α w x).mono K hK)
  let Q1 := fun w => Qt hh (n - 1) (Or.inr ⟨rfl, by omega⟩) (H + 1) (by omega) w
  let Q2 := fun w => Qt hh (n - 2) (Or.inr ⟨rfl, by omega⟩) (H + 1) (by omega) w
  let QT := fun j (_hj : j ∈ Finset.Icc 1 (min D n)) =>
    inheritedTaylorReserve H hD Q Cc A hh n u v k j
      (fun w => Qt (hh - 1) (n - j) (Or.inl (by omega)) (H + D) (by omega) w) Qedge
  exact (normalizedLiftFluxX_reserve_assembly H Q Cc A hh n hn hhpos u v k
    QG Qv Q1 Q2 QT).choose
end

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Both weak mass budgets survive the literal rerooting used at entry. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakEncoding_mass_sums_le (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (hη : 0 ≤ Mn.η0)
    (heps : ∀ i, 0 ≤ D.eps i ∧ D.eps i ≤ 1)
    (rootM rootR : ℕ → ℝ) (Gw : GenStage D ScalarH Dm b j₀)
    (ι : CompIn (stage M).comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding Mn.N J Mn.η0 rootM rootR (stage M) Gw ι)
    (law : BirthLaw) (hm : law.rootMass = rootM) (hr : law.rootReadout = rootR) :
    (∑ v, Gw.mass law v) ≤ 2 / 3 ∧
      (∑ v, Gw.readoutWeight law v ^ 2 * Gw.mass law v) ≤ 2 / 3 := by
  classical
  have hmass := weakConstruction_mass_sum_le P Mn M J r rW stage hc hN hJ hη heps
  constructor
  · rw [← Equiv.sum_comp ι]
    simp_rw [weakEncoding_mass Mn.N J Mn.η0 rootM rootR (stage M) Gw ι he law hm]
    rw [Finset.sum_coe_sort]
    exact hmass
  · rw [← Equiv.sum_comp ι]
    simp_rw [weakEncoding_readoutWeight Mn.N J Mn.η0 rootM rootR (stage M) Gw ι he law hr,
      weakEncoding_mass Mn.N J Mn.η0 rootM rootR (stage M) Gw ι he law hm]
    rw [Finset.sum_coe_sort (stage M).comps
      (fun v => weakReadoutWeight D Mn.η0 v ^ 2 * weakMass D Mn.N J Mn.η0 v)]
    exact (weakReadout_mass_sum_le D Mn.N J Mn.η0 hη heps (stage M).comps).trans hmass

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! On compact slow labels and a compact clock window every fixed native metric has a positive lower bound. -/

open Homogenization Set AVRegularity.EntryWeakProofs
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem native_metric_compact_elliptic (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm h) (a b : ℝ)
    (S : Set (Vec 2)) (hS : IsCompact S) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ t ∈ Icc a b, ∀ Y ∈ S, ∀ ξ : Vec 2,
      lo * ∑ i, ξ i ^ 2 ≤
        ∑ i, ∑ j, (familyLiftData D m slot A ρ edge).G t Y i j * ξ i * ξ j := by
  let J := fun p : ℝ × Vec 2 => jacMatrix
    (fun y => (A.geom D).1 (D.cellScaleSq m * p.1) y (A.geom D).2.2)
      ((A.geom D).2.1 + ρ • p.2)
  have hJ i j : Continuous (fun p : ℝ × Vec 2 => J p i j) := by
    have hs := jacMatrix_spacetime_entry_smooth
      (f := fun u y => (A.geom D).1 u y (A.geom D).2.2)
      (geom_spacetime_smooth_geom D hζ A (A.geom D).2.2) i j
    exact hs.continuous.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.add (continuous_snd.const_smul ρ)))
  have hb i j : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, ∀ Y ∈ S, |J (t, Y) i j| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn (hJ i j).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun t ht Y hY => ?_⟩
    have hh : |J (t, Y) i j| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM (t, Y) ⟨ht, hY⟩
    exact hh.trans (le_max_left _ _)
  choose M hM hMb using hb
  let B := ∑ i : Fin 2, ∑ j : Fin 2, M i j
  have hB i j : M i j ≤ B :=
    (Finset.single_le_sum (fun k _ => hM i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hM k l)) (Finset.mem_univ i))
  refine ⟨(4 * B ^ 2 + 1)⁻¹, by positivity, ?_⟩
  intro t ht Y hY ξ
  have hdet := jac_isUnit_det (actualOffset_inverse_law D A) (geomC1_geom D hζ A)
    (D.cellScaleSq m * t) (A.geom D).2.2 ((A.geom D).2.1 + ρ • Y)
  have he := metric_elliptic (Matrix.nonsing_inv_mul (J (t, Y)) hdet)
    (fun i j => (hMb i j t ht Y hY).trans (hB i j)) ξ
  change (4 * B ^ 2 + 1)⁻¹ * ∑ i, ξ i ^ 2 ≤
    ∑ i, ∑ j, (A.recenter D (ρ • Y)).famMetric D (D.cellScaleSq m * t) i j * ξ i * ξ j
  rw [metric_recenter_formula D A hl]
  exact he

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs

/-! Every quiet time of the weak reduction (`IsWeakReduction`) belongs to its solution window. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams}
  {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {n : ℕ+} {M J K r : ℕ} {a T : ℝ}
  {θ : ℝ → Vec 2 → ℝ} {stage : ℕ → GenStage D ScalarH Dm b j₀} {tq : ℕ → ℝ}
  {U : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk K (ScalarH v.1.root)}
  {Uw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root)}
  {Uk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u),
    ℝ → TorusHk (K + Dm - 1) (ScalarH u.1.root)}

theorem weakReduction_quietTimes_mem_window (hΛ : 1 ≤ D.Λ)
    (h : IsWeakReduction P φ₀ hφ₀ n M J K r a T θ stage tq U Uw Uk)
    (i : ℕ) (hli : M + 1 ≤ i) (hih : i ≤ M + J + 1) : tq i ∈ Set.Icc a T := by
  apply quietTimes_mem_window tq (M + 1) (M + J + 1) a T _ h.1 h.2.1 i hli hih
  intro k hklo hkhi
  have hc := (h.2.2.2 k (by omega) (by omega)).2.1
  have ht := Velocity.Jets.ocTauP_pos (α := D.α) (q := D.q) (Λ := D.Λ) (m := k) hΛ
  exact (le_add_of_nonneg_right ht.le).trans hc

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! The finest weak family is the actual natural one-root stage with no constituent identities. -/

def weakRootStage (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ Mtop r : ℕ)
    (hi : 1 ≤ Mtop) (hj : j₀ ≤ Mtop) (hτ : 0 < ocTau D.α D.q D.Λ Mtop) :
    GenStage D ScalarH Dm b j₀ where
  level := Mtop
  comps := {⟨r, []⟩}
  fam :=
    { Γ := fun _ _ => Empty
      fintypeΓ := fun _ _ => inferInstance
      identity := fun _ _ γ => Empty.elim γ
      piece := fun p => weakNaturalPiece D Mtop Mtop p.1
      flux := fun _ _ _ _ γ => Empty.elim γ
      flux_periodic := fun _ _ _ _ γ => Empty.elim γ
      flux_zero := fun _ _ _ _ γ => Empty.elim γ
      weight := fun p => ocCutoff D.α D.q D.Λ Mtop p.1
      weight_nonneg := fun _ _ => Real.smoothTransition.nonneg _
      weight_zero := fun p t ht => ocCutoff_zero_off_output D.α D.q D.Λ Mtop hτ p.1 t ht
      locally_finite := weak_output_locally_finite D.α D.q D.Λ Mtop hτ
      weight_sum := fun t _ => ocCutoff_finsum_one D.α D.q D.Λ Mtop hτ t }
  prov := fun _ _ γ => Empty.elim γ
  actual := fun p => ⟨nativeChain Mtop p.1,
    nativeChain_isCarrier D b j₀ Mtop p.1 2 hi hj p.2 0⟩
  exports := fun {_ _} _ => False

theorem weakRootStage_isNatural (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ Mtop r : ℕ)
    (hi : 1 ≤ Mtop) (hj : j₀ ≤ Mtop) (hτ : 0 < ocTau D.α D.q D.Λ Mtop) :
    (weakRootStage D Dm b j₀ Mtop r hi hj hτ).IsNatural Mtop := by
  refine ⟨fun p => weakNaturalPiece_isNatural D Mtop Mtop p.1, fun _ _ => rfl,
    fun _ => rfl, ?_⟩
  intro v u γ
  exact Empty.elim γ

theorem weakRootStage_isWeakRoot (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ Mtop r : ℕ)
    (hi : 1 ≤ Mtop) (hj : j₀ ≤ Mtop) (hτ : 0 < ocTau D.α D.q D.Λ Mtop) :
    IsWeakRoot Mtop r (weakRootStage D Dm b j₀ Mtop r hi hj hτ) :=
  ⟨rfl, rfl, fun _ _ => (inferInstance : IsEmpty Empty), weakRootStage_isNatural D Dm b j₀ Mtop r hi hj hτ⟩

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

/-! The original finite equation retains the full high-gradient dissipation with divergence forcing. -/

open AVRegularity.EntryWeakProofs

theorem molecularFinite_flux_gradient_production (N K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (u du : CellGalerkinSpace (E := ℂ) N) (S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (heq : ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N du) (cellGalerkinValue N z) =
        dataGeneratorForm P t u.val z.val + inner ℝ (S.val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ k : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
              2 (volume.restrict AVenhance.unitCube)) (F.val (valueIndex2 K)))
            (cellDerivativeCLM k z.val))
 :
    2 * inner ℝ (dataWeightedFourierCLM N K ρ (cellGalerkinValue N u))
      (dataWeightedFourierCLM N K ρ (cellGalerkinValue N du)) +
      gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1)
        (dataFourierCoordinatesCLM N (cellGalerkinValue N u))).val / 2 ≤
        (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) *
          ‖dataWeightedFourierCLM N K ρ (cellGalerkinValue N u)‖ ^ 2 +
          factorialNormSq ρ S.val + 4 * factorialNormSq ρ F.val := by
  let c := dataFourierCoordinatesCLM N (cellGalerkinValue N u)
  have hh := molecularFiniteSource_flux_energy N K ρ hρ P t Cv hCv hv hp hb c S F
  have hd := dataFinite_flux_dual_coordinates N K P t Cv hCv hv hp hb u du S F heq
  simp only [dataWeightedFourierCLM, ContinuousLinearMap.comp_apply,
    plainWeightedSynthesisCLM_apply, hd]
  rw [real_inner_comm, factorialWeightedJet_normSq]
  exact hh

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.WeakEntryProofs

/-! The full-cell source reserve allows lift degree above the constituent degree. -/

open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedFullCellSourceReserve (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + n + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff α t Y z)) :
    JointSourceReserve H (fun t z Y => normalizedLiftCellSource Q Cc
      (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n A t z Y v) := by
  let f := fun (_ : ℝ) X => Real.exp (A X) • (Pi.single u (1 : ℝ) : ι → ℝ)
  let QA := fun w => normalizedLiftAFromEarlierCoefficients H hH hD Q Cc hh n hn A w u
    (fun i j => (QG i j).mono (H + 1) (by omega))
    (fun i => (Qv i).mono H (by omega))
    (fun p q hpq m α v u => (Qc p q hpq m α v u).mono (H + D + 2) (by omega))
    (fun v u d γ hγ α => (Qedge v u d γ hγ α).mono (H + 1) (by omega))
  have QT (j : ℕ) (hj : j ∈ Finset.Icc 1 (n - 2))
      (p : ℕ × ℕ) (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
        liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t Y z v) := by
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hpre : p.1 < hh ∨ (p.1 = hh ∧ j < n) := by
      by_cases hlt : p.1 < hh
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
    let QC := fun m α w => (Qc p.1 j hpre m α v w).mono H (by omega)
    have hmeanPre (r s : ℕ) (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
        r < hh ∨ (r = hh ∧ s < n) := by
      rcases hrs with hrs | ⟨hrs, hsn⟩
      · exact Or.inl (by omega)
      · by_cases hlt : r < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩
    let QM := fun w => normalizedLiftAFromEarlierCoefficients (H + j) (by omega) hD Q Cc
      p.2 (n - j) (by omega) A w u
      (fun i k => (QG i k).mono (H + j + 1) (by omega))
      (fun i => (Qv i).mono (H + j) (by omega))
      (fun r s hrs m α v u => (Qc r s (hmeanPre r s hrs) m α v u).mono
        ((H + j) + D + 2) (by omega))
      (fun v u d γ hγ α => (Qedge v u d γ hγ α).mono (H + j + 1) (by omega))
    exact normalizedLiftCompositionComponentReserve H j Q Cc f p.1 p.2 (n - j) A v QC QM
  exact normalizedLiftCellSourceComponentReserve H Q Cc f hh n A v QA QT

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Finite ordered-word equations are produced recursively on the actual time window. -/

open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
variable {I : Type*}

theorem word_window_inverse_family_exists {a b : ℝ} (hab : a ≤ b)
    (K : ℕ) (P : MolecularData)
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B : List I → ℝ)
    (src : List I → ℝ → Vec 2 → ℂ)
    (F : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hdata : ∀ w : List I, w.length ≤ K →
      0 ≤ B w ∧ (∀ i j, Measurable (fun t => G w t i j)) ∧
      (∀ t i j, |G w t i j| ≤ B w) ∧
      MemLp (Function.uncurry (src w)) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) ∧
      MemLp (Function.uncurry (F w)) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    ∃ c : List I → ℝ → RawJet2 1 ℂ, ∀ w, w.length ≤ K →
      IsCellSolution (Icc a b) (dataCoefficients P) (src w)
        (F w + independentWordMetricFlux (fun p t _ => G p t) c w) (c w) ∧
      cellValue (c w) a =ᵐ[volume.restrict AVenhance.unitCube] (fun _ => 0) := by
  classical
  revert hdata
  induction K with
  | zero =>
    intro hdata
    have hh := hdata [] (by simp)
    obtain ⟨D, hD, hi⟩ := molecular_exists_zero_raw_ae hab P (src []) (F [])
      hh.2.2.2.1 hh.2.2.2.2
    refine ⟨fun _ => D, ?_⟩
    intro w hw
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    simpa only [independentWordMetricFlux_nil, add_zero] using And.intro hD hi
  | succ n ih =>
    intro hdata
    obtain ⟨old, hold⟩ := ih (fun w hw => hdata w (hw.trans (Nat.le_succ n)))
    have hex (w : List I) (hw : w.length = n + 1) :
        ∃ D : ℝ → RawJet2 1 ℂ,
          IsCellSolution (Icc a b) (dataCoefficients P) (src w)
            (F w + independentWordMetricFlux (fun p t _ => G p t) old w) D ∧
          cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] (fun _ => 0) := by
      have hh := hdata w (by omega)
      have hg (p : List I × List I) (hp : p ∈ independentWordForcing w) :
          p.1.length ≤ n + 1 := by
        have hl := (independentWordForcing_lengths w p hp).2.1
        omega
      have hc (p : List I × List I) (hp : p ∈ independentWordForcing w) :
          p.2.length ≤ n := by
        have hl := (independentWordForcing_lengths w p hp).2.2
        omega
      have hp := word_metric_flux_window_memLp hab G old w B
        (fun p hp => (hdata p.1 (hg p hp)).1)
        (fun p hp => (hdata p.1 (hg p hp)).2.1)
        (fun p hp => (hdata p.1 (hg p hp)).2.2.1)
        (dataCoefficients P) src
        (fun u => F u + independentWordMetricFlux (fun p t _ => G p t) old u)
        (fun p hp => (hold p.2 (hc p hp)).1)
      exact molecular_exists_zero_raw_ae hab P (src w)
        (F w + independentWordMetricFlux (fun p t _ => G p t) old w)
        hh.2.2.2.1 (by exact hh.2.2.2.2.add hp)
    let c := fun w : List I => if hw : w.length = n + 1 then (hex w hw).choose else old w
    refine ⟨c, ?_⟩
    intro w hw
    have hf : independentWordMetricFlux (fun p t _ => G p t) c w =
        independentWordMetricFlux (fun p t _ => G p t) old w := by
      apply independentWordMetricFlux_congr_lower
      intro u hu
      have hn : u.length ≠ n + 1 := by omega
      simp only [c, dite_eq_right hn]
    rw [hf]
    by_cases hn : w.length = n + 1
    · simp only [c, dite_eq_left hn]
      exact (hex w hn).choose_spec
    · simp only [c, dite_eq_right hn]
      exact hold w (by omega)

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.WeakEntryProofs

/-! Earlier centered coefficients center the full-cell source at arbitrary lift degree. -/

open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem normalizedFullCellSource_mean_zero (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (u : ι)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + n + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (t : ℝ) (Y : Vec 2) (v : ι) :
    fieldCellMean (fun z => normalizedLiftCellSource Q Cc
      (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n A t z Y v) = 0 := by
  let f := fun (_ : ℝ) X => Real.exp (A X) • (Pi.single u (1 : ℝ) : ι → ℝ)
  let QA := fun w => normalizedLiftAFromEarlierCoefficients H hH hD Q Cc hh n hn A w u
    (fun i j => (QG i j).mono (H + 1) (by omega))
    (fun i => (Qv i).mono H (by omega))
    (fun p q hpq m α v u => (Qc p q hpq m α v u).mono (H + D + 2) (by omega))
    (fun v u d γ hγ α => (Qedge v u d γ hγ α).mono (H + 1) (by omega))
  let Qwhole := jointSourcePiReserve H (fun w t z Y => normalizedLiftASource Q Cc f hh n A t z Y w) QA
  apply normalizedLiftCellSource_component_mean_zero_of_predecessors H Q Cc f hh n A Qwhole _ t Y v
  intro j hj p hp m hm α t Y v w
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hpre : p.1 < hh ∨ (p.1 = hh ∧ j < n) := by
    by_cases hlt : p.1 < hh
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, by omega⟩
  constructor
  · apply realLinearMap_field_continuous_of_value_one
    exact (Qc p.1 j hpre ⟨m, by omega⟩ α v w).fast_contDiff t Y |>.continuous
  · exact hmean p.1 j hpre hj'.1 m hm α t Y v w

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Pinning positive coefficients off the carrier preserves the genuine interior inverse. -/

open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakLiftCarrierRestriction_isInverse
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n sZ : ℕ) (hn : 1 ≤ n) (a b : ℝ) (hab : a ≤ b)
    (X : Vec 2) (hX : X ∈ Ω)
    (hc : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => liftCellSource Q Cc f hh n t X z)
      (fun t z => liftApply n (Cc hh n) f t X z)) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => liftCellSource Q (weakLiftCarrierRestriction Ω Cc) f hh n t X z)
      (fun t z => liftApply n (weakLiftCarrierRestriction Ω Cc hh n) f t X z) := by
  have hs := CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _
    (fun t _ => funext (fun z => (weakLiftCarrierRestriction_source Ω hΩ Q Cc f hh n hn
      t X hX z).symm)) hc
  apply cellFieldInverse_field_congr_on _ _ sZ a b hab 0 _ _ _ hs
  intro t _
  funext z
  exact (weakLiftCarrierRestriction_apply Ω hΩ Cc f hh n t X hX z).symm

end AVRegularity.WeakEntryProofs
end
end
