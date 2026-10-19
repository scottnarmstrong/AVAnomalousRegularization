-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.SuccessorGeneration.Setup
import AVRegularity.Proofs.GenSem.LiftOn.Omega
public import AVRegularity.Proofs.GenSem.Finer.CovLetterRep
public import AVRegularity.Definitions.Construction.Gen.Majorant
import AVRegularity.Proofs.GenSem.Transfer.Assemble
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import Mathlib.RingTheory.PicardGroup

section
section
/-! Real smoothness of a holomorphically extended context function along recenterings.

If `F` is a holomorphic extension of `f` on the outer carrier, then
`(X, ζ) ↦ f t (A.recenter (ρ • X)) ζ` is `C^∞` on the set of `X` for which the recentered chain
is admissible: it agrees there with `Re (F ∘ Pm)`, where `Pm` is an explicit smooth parameter map
(`PmShift`, `PmBase`), and `F` is `C^∞` on the open complex carrier
(`contDiffOn_top_of_differentiableOn`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity

namespace AVRegularity.Providers.GenSem

section Smooth

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem contDiff_ofReal_comp {f : Y → ℝ} (h : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => (f x : ℂ) :=
  Complex.ofRealCLM.contDiff.comp h

theorem contDiff_vec_apply {W : Y → Vec 2} (hW : ContDiff ℝ (⊤ : ℕ∞) W) (a : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => (W y a : ℂ) :=
  contDiff_ofReal_comp ((contDiff_apply ℝ ℝ a).comp hW)

theorem contDiff_shiftC (n : ℕ) (k : Fin n) (a : Fin 2) {W : Y → Vec 2}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) : ContDiff ℝ (⊤ : ℕ∞) fun y => shiftC n k (W y) a := by
  by_cases h : (k : ℕ) + 1 = n
  · simpa only [shiftC, h, ite_true] using contDiff_vec_apply hW a
  · simpa only [shiftC, h, ite_false] using contDiff_const

theorem contDiff_PmShift (A : RealChain) (e : ℝ) {W Z : Y → Vec 2}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hZ : ContDiff ℝ (⊤ : ℕ∞) Z) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => PmShift A (W y) e (Z y) := by
  refine ContDiff.prodMk (contDiff_pi.2 fun a => contDiff_const)
    (ContDiff.prodMk (contDiff_pi.2 fun k => ContDiff.prodMk ?_ ?_)
      (contDiff_pi.2 fun a => contDiff_vec_apply hZ a))
  · exact contDiff_pi.2 fun a => contDiff_const.add (contDiff_shiftC _ k a hW)
  · exact contDiff_pi.2 fun a => contDiff_const.add (contDiff_shiftC _ k a (hW.const_smul e))

theorem contDiff_PmBase (A : RealChain) {W Z : Y → Vec 2}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hZ : ContDiff ℝ (⊤ : ℕ∞) Z) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => PmBase A (W y) (Z y) := by
  refine ContDiff.prodMk (contDiff_pi.2 fun a => ?_)
    (ContDiff.prodMk (contDiff_pi.2 fun k => ContDiff.prodMk
      (contDiff_pi.2 fun a => contDiff_const) (contDiff_pi.2 fun a => contDiff_const))
      (contDiff_pi.2 fun a => contDiff_vec_apply hZ a))
  · refine contDiff_ofReal_comp ?_
    exact contDiff_const.add ((contDiff_apply ℝ ℝ a).comp hW)

theorem contDiff_shiftOf {g : ChainGeom} (hg : EntryWeakProofs.GeomSpatialSmooth g) (s' : ℝ)
    (cen : Vec 2) : ContDiff ℝ (⊤ : ℕ∞) fun h => shiftOf g s' cen h := by
  unfold shiftOf
  exact (((hg g.2.2 s').comp (contDiff_const.add contDiff_id)).sub contDiff_const).sub
    contDiff_const

end Smooth

theorem recenter_children_length (D : OCData) (A : RealChain) (h : Vec 2) :
    (A.recenter D h).children.length = A.children.length := by
  rcases List.eq_nil_or_concat A.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D A hc]
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D A cs c hc]
    simp [hc]

theorem recenter_data (D : OCData) (A : RealChain) (h : Vec 2) :
    (A.recenter D h).data = A.data := by
  unfold RealChain.data
  rw [(recenter_baseLevel D A h).1, (recenter_baseLevel D A h).2]

/-- An explicit smooth parameter map for the recentered chains. -/
theorem exists_recenter_model (D : OCData) (A : RealChain) (ρ : ℝ) :
    ∃ Pm : Vec 2 → Vec 2 → ChainParamsC A.children.length,
      ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec 2 × Vec 2 => Pm q.1 q.2) ∧
      ∀ X (hl : (A.recenter D (ρ • X)).children.length = A.children.length) z,
        (A.recenter D (ρ • X)).paramsN _ hl z = Pm X z := by
  rcases List.eq_nil_or_concat A.children with hc | ⟨cs, c, hc⟩
  · refine ⟨fun X z => PmBase A (ρ • X) z, ?_, fun X hl z => ?_⟩
    · exact contDiff_PmBase A ((contDiff_fst).const_smul ρ) contDiff_snd
    · exact paramsN_base A _ (ρ • X) (recenter_nil D A hc _) hl z
  · rw [List.concat_eq_append] at hc
    refine ⟨fun X z => PmShift A (recenterShift D A c (ρ • X)) (D.eps A.lastLevel)⁻¹ z,
      ?_, fun X hl z => ?_⟩
    · refine contDiff_PmShift A _ ?_ contDiff_snd
      have := contDiff_shiftOf (EntryWeakProofs.geomSpatialSmooth_geom D A.dropLastChild)
        (D.slotAnchor (A.lastLevel + 1) A.slot) c.center
      exact this.comp (contDiff_fst.const_smul ρ)
    · exact paramsN_snoc A _ cs c hc _ _ (recenter_snoc D A cs c hc _) hl z

/-- Real smoothness of a holomorphically extended context function along recenterings. -/
theorem contDiffOn_holExtension_recenter {D : OCData} (hΛ : 1 ≤ D.Λ) {b : ℝ} (hb : 0 < b)
    {j₀ i : ℕ} {p : ℤ} {f : GenSort.Sem .ctx}
    {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D b j₀ i p f F) (A : RealChain) (ρ : ℝ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Vec 2 × Vec 2 => f t (A.recenter D (ρ • q.1)) q.2)
      ({X | IsAdmissibleChain D b j₀ i p (A.recenter D (ρ • X))} ×ˢ Set.univ) := by
  obtain ⟨Pm, hPm, hPmeq⟩ := exists_recenter_model D A ρ
  have hU := isOpen_carrierC D b A.data A.children.length 2
  have hFU : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (F A.data A.children.length t x).re)
      (carrierC D b A.data A.children.length 2) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      ((contDiffOn_top_of_differentiableOn hU (hF.1 A.data A.children.length t ht)).restrict_scalars ℝ)
  have hΦ := hFU.comp hPm.contDiffOn (Set.mapsTo_preimage _ _)
  have key : ∀ q ∈ ({X | IsAdmissibleChain D b j₀ i p (A.recenter D (ρ • X))} ×ˢ
      Set.univ : Set (Vec 2 × Vec 2)),
      Pm q.1 q.2 ∈ carrierC D b A.data A.children.length 2 ∧
      f t (A.recenter D (ρ • q.1)) q.2 = (F A.data A.children.length t (Pm q.1 q.2)).re := by
    intro q hq
    have hadm : IsAdmissibleChain D b j₀ i p (A.recenter D (ρ • q.1)) := hq.1
    have hd := recenter_data D A (ρ • q.1)
    have hn := recenter_children_length D A (ρ • q.1)
    have hP := hPmeq q.1 hn q.2
    have hmem := paramsC_mem_carrierC hΛ hb hadm q.2
    have hmem' := paramsC_transport _ A.data A.children.length hd hn _ q.2 hP
      (fun dd n x => x ∈ carrierC D b dd n 2) hmem
    have hval := hF.2.2 (A.recenter D (ρ • q.1)) t ht q.2 hadm
    have hval' := paramsC_transport _ A.data A.children.length hd hn _ q.2 hP
      (fun dd n x => F dd n t x = (f t (A.recenter D (ρ • q.1)) q.2 : ℂ)) hval
    refine ⟨hmem', ?_⟩
    have := congrArg Complex.re hval'
    simpa using this.symm
  refine (hΦ.mono fun q hq => (key q hq).1).congr fun q hq => (key q hq).2

end AVRegularity.Providers.GenSem
end
end

section
/-! The context strain is `C^∞` along recentering: for a well-slotted chain `ch`,
`y ↦ contextStrain D i pc t (ch.recenter D y) (z + ε_i⁻¹ y)` has smooth entries. -/

@[expose] public noncomputable section

open Homogenization AVenhance AVRegularity AVRegularity.EntryWeakProofs

namespace AVRegularity.Providers.GenSem

theorem contDiff_contextStrain_recenter (D : OCData) (hζ : IsFastProfile D.ζ)
    (i : ℕ) (pc : ℤ) (t : ℝ) (ch : RealChain) (hl : ch.WellSlotted) (z : Vec 2) (a c : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Vec 2 => contextStrain D i pc t (ch.recenter D y) (z + (D.eps i)⁻¹ • y) a c) := by
  set g := ch.geom D with hg
  set J : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun x => jacMatrix (fun y => g.1 t y g.2.2) x with hJ
  have hJs : MatSmooth J := matSmooth_jac (geomSpatialSmooth_geom D ch t g.2.2)
  have hJi : MatSmooth (fun x => (J x)⁻¹) := fun p q =>
    offsetJacobian_inverse_entry_smooth (geomSpatialSmooth_geom D ch)
      (actualOffset_inverse_law D ch) t g.2.2 p q
  have hT : MatSmooth (fun x => Matrix.of (fun a b =>
      deriv (fun u => jacMatrix (fun y => g.1 u y g.2.2) x a b) t)) :=
    geomTimeSmooth_geom D hζ ch t g.2.2
  have hadd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => g.2.1 + y) :=
    contDiff_const.add contDiff_id
  have hζy : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => z + (D.eps i)⁻¹ • y) :=
    contDiff_const.add (contDiff_id.const_smul _)
  have hLs : ContDiff ℝ (⊤ : ℕ∞) (labelShear D i pc t) := by
    unfold labelShear
    exact ((ocShearVel_spatial_smooth _ _ _ _ _).comp (contDiff_id.const_smul _)).const_smul _
  have hJL : MatSmooth (fun y => jacMatrix (labelShear D i pc t) (z + (D.eps i)⁻¹ • y)) :=
    (matSmooth_jac hLs).comp hζy
  have hD : MatSmooth (fun y : Vec 2 => Matrix.of (fun p q =>
      fderiv ℝ (fun x => J x p q) (g.2.1 + y) (labelShear D i pc t (z + (D.eps i)⁻¹ • y)))) := by
    intro p q
    simp only [Matrix.of_apply]
    exact (((hJs p q).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp hadd).clm_apply
      (hLs.comp hζy)
  have hS : MatSmooth (fun y : Vec 2 =>
      Matrix.of (fun a b => deriv (fun u => jacMatrix (fun y' => g.1 u y' g.2.2) (g.2.1 + y) a b) t) *
        (J (g.2.1 + y))⁻¹ +
      (Matrix.of (fun p q => fderiv ℝ (fun x => J x p q) (g.2.1 + y)
          (labelShear D i pc t (z + (D.eps i)⁻¹ • y))) +
        J (g.2.1 + y) * ((D.eps i)⁻¹ • jacMatrix (labelShear D i pc t) (z + (D.eps i)⁻¹ • y))) *
        (J (g.2.1 + y))⁻¹) :=
    ((hT.comp hadd).mul (hJi.comp hadd)).add
      ((hD.add ((hJs.comp hadd).mul (hJL.const_smul _))).mul (hJi.comp hadd))
  have hEq : ∀ y : Vec 2, contextStrain D i pc t (ch.recenter D y) (z + (D.eps i)⁻¹ • y) =
      Matrix.of (fun a b => deriv (fun u => jacMatrix (fun y' => g.1 u y' g.2.2) (g.2.1 + y) a b) t) *
        (J (g.2.1 + y))⁻¹ +
      (Matrix.of (fun p q => fderiv ℝ (fun x => J x p q) (g.2.1 + y)
          (labelShear D i pc t (z + (D.eps i)⁻¹ • y))) +
        J (g.2.1 + y) * ((D.eps i)⁻¹ • jacMatrix (labelShear D i pc t) (z + (D.eps i)⁻¹ • y))) *
        (J (g.2.1 + y))⁻¹ := by
    intro y
    unfold contextStrain
    rw [famStrain_recenter D hζ ch hl y t, famJac_recenter D hζ ch hl y t]
    have hfun : ∀ p q, (fun h : Vec 2 => ((ch.recenter D y).recenter D h).famJac D t p q) =
        fun h => (fun x => J x p q) ((g.2.1 + y) + h) := by
      intro p q
      funext h
      rw [recenter_recenter D hζ ch y h, famJac_recenter D hζ ch hl (y + h) t]
      simp only [hJ, hg, add_assoc]
    have hfd : ∀ p q, fderiv ℝ (fun h : Vec 2 => ((ch.recenter D y).recenter D h).famJac D t p q) 0 =
        fderiv ℝ (fun x => J x p q) (g.2.1 + y) := by
      intro p q
      have e := fderiv_comp_add_left (𝕜 := ℝ) (f := fun x => J x p q) (x := (0 : Vec 2)) (g.2.1 + y)
      rw [hfun p q, e, add_zero]
    simp only [hfd]
    rfl
  simp only [hEq]
  exact hS a c

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation: locality of the path-mean flux in the lift data.** The slow flux `liftFluxX` and the
path mean flux at `y` read the lift data (metric, drift, contrast, source edges) and the lift
coefficients only at the slow offset `ρ⁻¹ y`: data agreeing on an open set `Ω` and coefficients
agreeing there give the same values (`liftFluxX_agree`, `pathMeanFlux_eq_of_dataAgree`). In
particular the finer outputs of the cut-off lift data are those of the true lift data at the
offset `0` (`fluxCoeff_pathMeanFlux_agree`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Uniqueness

open AVRegularity

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Ω : Set (Vec 2)}

/-- The slow flux of the lift reads the data and the coefficients only on `Ω`. -/
theorem liftFluxX_agree {Dm : ℕ} {Q Q' : LiftOperatorData ι h Dm} (hQ : DataAgreeOn Ω Q Q')
    {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (τ : ℝ)
    (hΩ : IsOpen Ω)
    (hP : ∀ hh' ≤ hh, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α τ X = Cc' hh' n' m' α τ X) (κ : Fin 2) :
    LocEq Ω (fun X z => liftFluxX Q Cc a hh n τ X z κ)
      (fun X z => liftFluxX Q' Cc' a hh n τ X z κ) := by
  have e := liftFluxX_locEq (Ω := Ω) Q a hh n τ hΩ hP κ
  intro X hX z
  refine (e X hX z).trans ?_
  show liftFluxX Q Cc' a hh n τ X z κ = liftFluxX Q' Cc' a hh n τ X z κ
  unfold liftFluxX
  rw [hQ.eta, hQ.drift, hQ.metric τ X hX]
  have hs : ∀ j, (fun ε : ℝ =>
      sourceFlux Q.edge Q'.η ε τ (liftApply (n - j) (Cc' (hh - 1) (n - j)) a τ) κ X z) =
      fun ε => sourceFlux Q'.edge Q'.η ε τ (liftApply (n - j) (Cc' (hh - 1) (n - j)) a τ) κ X z :=
    fun j => funext fun ε => (sourceFlux_agree hΩ hQ.edge Q'.η ε τ
      (fun _ _ _ => rfl) κ) X hX z
  simp only [hs]

/-- The path mean flux at `y` reads the data and the coefficients only on `Ω ∋ ρ⁻¹ y`. -/
theorem pathMeanFlux_eq_of_dataAgree (D : OCData) (m : ℕ) (ρ : ℝ) {Dm h : ℕ}
    {Q Q' : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm} (hQ : DataAgreeOn Ω Q Q')
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (hΩ : IsOpen Ω)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X)
    (f : Vec 2 → ℝ) (y : Vec 2) (hy : ρ⁻¹ • y ∈ Ω) :
    pathMeanFlux D m ρ Q Cc n t f y = pathMeanFlux D m ρ Q' Cc' n t f y := by
  funext κ
  unfold pathMeanFlux
  rw [show (fun z => liftFluxX Q Cc (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
      ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) =
      (fun z => liftFluxX Q' Cc' (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
      ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) from
    funext fun z => liftFluxX_agree hQ _ h n _ hΩ hP κ _ hy z]

/-- **The finer output of the path mean flux at the offset `0`** is that of any lift data and
coefficients agreeing with it on an open `Ω ∋ 0`. -/
theorem fluxCoeff_pathMeanFlux_agree (D : OCData) (m : ℕ) (ρ : ℝ) {Dm h : ℕ}
    {Q Q' : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm} (hQ : DataAgreeOn Ω Q Q')
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (hΩ : IsOpen Ω)
    (h0 : (0 : Vec 2) ∈ Ω)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    fluxCoeff (pathMeanFlux D m ρ Q Cc n t) d I 0 = fluxCoeff (pathMeanFlux D m ρ Q' Cc' n t) d I 0 := by
  unfold fluxCoeff
  rw [pathMeanFlux_eq_of_dataAgree D m ρ hQ Cc Cc' n t hΩ hP _ 0 (by rw [smul_zero]; exact h0)]

end AVRegularity.Uniqueness
end
end

section
/-! **Generation: family expressions on the admissible families of a slot.** `SlotFamRep D b j₀ 𝒮 m k ψ`:
the function `ψ t A` of the physical time and the base family is denoted, for the admissible
families `A` over the odd slot `k` of level `m` and the times of the pulse window, by one scheduled,
seed-provenanced family expression. This is the form of the finer outputs read by the transfer.
* constants, sums and negatives (`SlotFamRep.const`, `.add`, `.neg`, `.sub`), congruence;
* from the uniform representations over the lift window (`SlotFamRep.of_famURep`: the lift window
  in cell time is the pulse window);
* `mem_ocPulseWindow_of_ocCutoff_ne_zero`: the glueing cutoff of a slot vanishes off its pulse
  window. -/

@[expose] public noncomputable section

open Set Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.Providers.GenSem

/-- `ψ` is denoted by one scheduled, seed-provenanced family expression on the admissible families
over the slot `k` of level `m` and the pulse window. -/
def SlotFamRep (D : OCData) (b : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (m : ℕ) (k : ℤ)
    (ψ : ℝ → RealChain → ℝ) : Prop :=
  ∃ c : Gen .fam m k, Gen.IsScheduled D c ∧ Gen.FromSeed 𝒮 c ∧
    ∃ fc : GenSort.Sem .fam, Gen.Denotes D b j₀ c fc ∧
      ∀ A, IsAdmissibleChain D b j₀ m k A → ∀ t ∈ ocPulseWindow D.α D.q D.Λ m k, fc t A = ψ t A

namespace SlotFamRep

variable {D : OCData} {b : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ}

theorem congr {ψ ψ' : ℝ → RealChain → ℝ} (h : SlotFamRep D b j₀ 𝒮 m k ψ)
    (hψ : ∀ A, IsAdmissibleChain D b j₀ m k A → ∀ t ∈ ocPulseWindow D.α D.q D.Λ m k,
      ψ t A = ψ' t A) : SlotFamRep D b j₀ 𝒮 m k ψ' := by
  obtain ⟨c, hs, hf, fc, hd, hv⟩ := h
  exact ⟨c, hs, hf, fc, hd, fun A hA t ht => (hv A hA t ht).trans (hψ A hA t ht)⟩

theorem const (a : ℝ) : SlotFamRep D b j₀ 𝒮 m k (fun _ _ => a) :=
  ⟨Gen.time (s := .fam) (i := m) (p := k) (.const a), .timeConst a, .time _,
    GenSort.ofTime .fam (TimeLetter.eval D (.const a)), .time _, fun _ _ _ _ => rfl⟩

theorem add {ψ φ : ℝ → RealChain → ℝ} (hψ : SlotFamRep D b j₀ 𝒮 m k ψ)
    (hφ : SlotFamRep D b j₀ 𝒮 m k φ) : SlotFamRep D b j₀ 𝒮 m k (fun t A => ψ t A + φ t A) := by
  obtain ⟨a, sa, fa, f, hf, hva⟩ := hψ
  obtain ⟨c, sc, fcs, g, hg, hvc⟩ := hφ
  refine ⟨Gen.add a c, .add sa sc, .add fa fcs, GenSort.add .fam f g, .add hf hg,
    fun A hA t ht => ?_⟩
  show f t A + g t A = _
  rw [hva A hA t ht, hvc A hA t ht]

theorem mul {ψ φ : ℝ → RealChain → ℝ} (hψ : SlotFamRep D b j₀ 𝒮 m k ψ)
    (hφ : SlotFamRep D b j₀ 𝒮 m k φ) : SlotFamRep D b j₀ 𝒮 m k (fun t A => ψ t A * φ t A) := by
  obtain ⟨a, sa, fa, f, hf, hva⟩ := hψ
  obtain ⟨c, sc, fcs, g, hg, hvc⟩ := hφ
  refine ⟨Gen.mul a c, .mul sa sc, .mul fa fcs, GenSort.mul .fam f g, .mul hf hg,
    fun A hA t ht => ?_⟩
  show f t A * g t A = _
  rw [hva A hA t ht, hvc A hA t ht]

theorem sub {ψ φ : ℝ → RealChain → ℝ} (hψ : SlotFamRep D b j₀ 𝒮 m k ψ)
    (hφ : SlotFamRep D b j₀ 𝒮 m k φ) : SlotFamRep D b j₀ 𝒮 m k (fun t A => ψ t A - φ t A) :=
  (hψ.add ((const (-1)).mul hφ)).congr fun _ _ _ _ => by ring

/-- **From a uniform representation over the lift window.** For the admissible families and
the lift window `[slotStart/ℓ², (k + 61/48)τ/ℓ²]` (the pulse window in cell time). -/
theorem of_famURep (hc : 0 < D.cellScaleSq m) {ρ : ℝ} {U : RealChain → Set (Vec 2)}
    {φ : RealChain × ℝ → ℝ} {c : Gen .fam m k}
    (h : (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).FamURep φ c) :
    SlotFamRep D b j₀ 𝒮 m k (fun t A => φ (A, (D.cellScaleSq m)⁻¹ * t)) := by
  obtain ⟨hs, hf, fc, hd, hv⟩ := h
  refine ⟨c, hs, hf, fc, hd, fun A hA t ht => ?_⟩
  have hmem : (A, (D.cellScaleSq m)⁻¹ * t) ∈ (liftEnv D b j₀ 𝒮 m k ρ
      {A | IsAdmissibleChain D b j₀ m k A} U (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).W := by
    refine ⟨hA, ?_, ?_⟩
    · rw [div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hc.le)
      exact ht.1
    · rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hc.le)
  have := hv _ hmem
  simp only [liftEnv] at this
  show fc t A = φ (A, (D.cellScaleSq m)⁻¹ * t)
  rw [this, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

end SlotFamRep

/-- The glueing cutoff of a slot vanishes off its pulse window. -/
theorem mem_ocPulseWindow_of_ocCutoff_ne_zero {α q : ℝ} {Λ m : ℕ} {k : ℤ} {t : ℝ}
    (hτ : 0 < ocTau α q Λ m) (h : ocCutoff α q Λ m k t ≠ 0) : t ∈ ocPulseWindow α q Λ m k := by
  by_contra hn
  apply h
  unfold ocCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have hfar : 61 / 48 * ocTau α q Λ m < |t - (k : ℝ) * ocTau α q Λ m| := by
    unfold ocPulseWindow at hn
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · rw [abs_of_neg (by nlinarith)]; nlinarith
    · rw [abs_of_pos (by nlinarith)]; nlinarith
  rw [sub_nonpos, le_div_iff₀ hτ]
  nlinarith

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation, restricted parallel invariance: the induction.** -/

@[expose] public noncomputable section

open Homogenization AVRegularity MeasureTheory

namespace AVRegularity.Providers.GenSem

theorem parInvOn_of_export {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {f : GenSort.Sem .ctx}
    (hx : IsSlotParInvCtx D b j₀ i p f) : ParInvOn D b j₀ i p f :=
  fun t ht ch hA => ⟨fun ch' ζ h => (hx t ht ch hA).1 ch' ζ ((parEq_iff_isParShift ch ch').1 h),
    (hx t ht ch hA).2⟩

theorem recenter_eventually (D : OCData) (hζ : IsFastProfile D.ζ) (b : ℝ) (j₀ i : ℕ) (p : ℤ)
    {ch : RealChain} (hA : IsAdmissibleChain D b j₀ i p ch) :
    ∀ᶠ h in nhds (0 : Vec 2), IsAdmissibleChain D b j₀ i p (ch.recenter D h) := by
  refine (isOpen_admissible_recenter D b j₀ i p ch).mem_nhds ?_
  show IsAdmissibleChain D b j₀ i p (ch.recenter D 0)
  rw [recenter_zero D hζ]; exact hA

theorem IsScheduled.cellInv_inv {D : OCData} {i : ℕ} {p : ℤ} {F : Fin 2 → Gen .cell i p}
    {t₀ : ℝ} {ι : Gen .cell i p} (h : Gen.IsScheduled D (Gen.cellInv F t₀ ι)) :
    t₀ = D.slotStart i p ∧ (∀ k, Gen.IsScheduled D (F k)) ∧ Gen.IsScheduled D ι := by
  cases h with
  | cellInv hF => exact ⟨rfl, hF, Gen.IsScheduled.timeConst 0⟩

section Aux

variable {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {b : ℝ} (hb : 0 < b) {j₀ : ℕ}
  (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
  {𝒮 : SeedExports}
  (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → ∀ f, Gen.Denotes D b j₀ e f →
      IsSlotParInvCtx D b j₀ i p f)

include hΛ hζ hb hstart hexp in
/-- Auxiliary form of `denotes_parInvOn_of_odd`. -/
theorem denotes_parInvOn_aux {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p} {f : s.Sem}
    (hd : Gen.Denotes D b j₀ e f) :
    Gen.FromSeed 𝒮 e → Gen.IsScheduled D e → e.EvalOdd → s.ParInvOn' D b j₀ i p f := by
  induction hd with
  | @geo i p fr L =>
    intro _ _ _
    cases fr with
    | own =>
      exact fun t ht ch hA => ⟨fun ch' ζ hp => evalAt_parEq D hp t L, fun _ _ => rfl⟩
    | child p' =>
      refine fun t ht ch hA => ⟨fun ch' ζ hp => ?_, fun ζ s => ?_⟩
      · simp only [GeoLetter.eval]
        rw [evalAt_parEq D (hp.appendChild D hA.2.2.1 p' t ζ) t L]
      · have := parEq_appendChild_shift D ch hA.2.2.1 p' t ζ s
        rw [hA.2.2.2.1] at this
        simp only [GeoLetter.eval]
        rw [evalAt_parEq D this t L]
  | @drift i p c =>
    intro _ _ _
    exact fun t ht ch hA => ⟨fun _ _ _ => rfl, fun ζ s => driftSem_phase D i p c t ch ζ s⟩
  | @time s i p L =>
    intro _ _ _
    cases s
    · exact fun t ht ch hA => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
    · exact fun t ht ch hA ch' _ => rfl
    · exact fun t ht ch hA => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  | @add s i p a b' fa fb ha hb' iha ihb =>
    intro hfs hsch hod
    cases hfs with
    | «export» hx => exact parInvOn_of_export (hexp _ hx _ (Gen.Denotes.add ha hb'))
    | add hfa hfb =>
      cases hsch with
      | add hsa hsb =>
        cases s
        · exact ParInvOn.zipWith (· + ·) (iha hfa hsa hod.1) (ihb hfb hsb hod.2)
        · exact FamInvOn.zipWith (· + ·) (iha hfa hsa hod.1) (ihb hfb hsb hod.2)
        · exact ParInvOn.zipWith (· + ·) (iha hfa hsa hod.1) (ihb hfb hsb hod.2)
  | @mul s i p a b' fa fb ha hb' iha ihb =>
    intro hfs hsch hod
    cases hfs with
    | «export» hx => exact parInvOn_of_export (hexp _ hx _ (Gen.Denotes.mul ha hb'))
    | mul hfa hfb =>
      cases hsch with
      | mul hsa hsb =>
        cases s
        · exact ParInvOn.zipWith (· * ·) (iha hfa hsa hod.1) (ihb hfb hsb hod.2)
        · exact FamInvOn.zipWith (· * ·) (iha hfa hsa hod.1) (ihb hfb hsb hod.2)
        · exact ParInvOn.zipWith (· * ·) (iha hfa hsa hod.1) (ihb hfb hsb hod.2)
  | @dOld i p j a fa ha iha =>
    intro hfs hsch hod
    cases hfs with
    | «export» hx => exact parInvOn_of_export (hexp _ hx _ (Gen.Denotes.dOld j ha))
    | dOld _ hfa =>
      cases hsch with
      | dOld _ hsa =>
        have ih : ParInvOn D b j₀ i p fa := iha hfa hsa hod
        intro t ht ch hA
        have hN := recenter_eventually D hζ b j₀ i p hA
        refine ⟨fun ch' ζ hp => ?_, fun ζ s => ?_⟩
        · have hev : (fun h : Vec 2 => fa t (ch'.recenter D h) (ζ + (D.eps i)⁻¹ • h)) =ᶠ[nhds 0]
              (fun h : Vec 2 => fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) :=
            hN.mono fun h hh => (ih t ht _ hh).1 _ _ (hp.recenter D hA.2.2.1 h)
          show fderiv ℝ _ 0 _ = fderiv ℝ _ 0 _
          rw [hev.fderiv_eq]
        · have hev : (fun h : Vec 2 => fa t (ch.recenter D h) (ζ + s • basisVec (parIdx p) +
              (D.eps i)⁻¹ • h)) =ᶠ[nhds 0]
              (fun h : Vec 2 => fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) :=
            hN.mono fun h hh => by
              dsimp only
              rw [add_right_comm]; exact (ih t ht _ hh).2 _ s
          show fderiv ℝ _ 0 _ = fderiv ℝ _ 0 _
          rw [hev.fderiv_eq]
  | @dPhase i p a fa ha iha =>
    intro hfs hsch hod
    cases hfs with
    | «export» hx => exact parInvOn_of_export (hexp _ hx _ (Gen.Denotes.dPhase ha))
    | dPhase hfa =>
      cases hsch with
      | dPhase hsa =>
        have ih : ParInvOn D b j₀ i p fa := iha hfa hsa hod
        intro t ht ch hA
        refine ⟨fun ch' ζ hp => ?_, fun ζ s => ?_⟩
        · have : fa t ch' = fa t ch := funext fun z => (ih t ht ch hA).1 ch' z hp
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [this]
        · have h1 : (fun z => fa t ch (z + s • basisVec (parIdx p))) = fa t ch :=
            funext fun z => (ih t ht ch hA).2 z s
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [← fderiv_comp_add_right (s • basisVec (parIdx p)), h1]
  | @dSlowFam i p j c fc hc ihc =>
    intro hfs hsch hod
    cases hfs with
    | dSlowFam _ hfa =>
      cases hsch with
      | dSlowFam _ hsa =>
        have ih : FamInvOn D b j₀ i p fc := ihc hfa hsa hod
        intro t ht ch hA ch' hp
        have hN := recenter_eventually D hζ b j₀ i p hA
        have hev : (fun h : Vec 2 => fc t (ch'.recenter D h)) =ᶠ[nhds 0]
            (fun h : Vec 2 => fc t (ch.recenter D h)) :=
          hN.mono fun h hh => ih t ht _ hh _ (hp.recenter D hA.2.2.1 h)
        show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
        rw [hev.fderiv_eq]
  | @dSlowCell i p j w fw hw ihw =>
    intro hfs hsch hod
    cases hfs with
    | dSlowCell _ hfa =>
      cases hsch with
      | dSlowCell _ hsa =>
        have ih : ParInvOn D b j₀ i p fw := ihw hfa hsa hod
        intro t ht ch hA
        have hN := recenter_eventually D hζ b j₀ i p hA
        refine ⟨fun ch' η hp => ?_, fun η s => ?_⟩
        · have hev : (fun h : Vec 2 => fw t (ch'.recenter D h) η) =ᶠ[nhds 0]
              (fun h : Vec 2 => fw t (ch.recenter D h) η) :=
            hN.mono fun h hh => (ih t ht _ hh).1 _ _ (hp.recenter D hA.2.2.1 h)
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [hev.fderiv_eq]
        · have hev : (fun h : Vec 2 => fw t (ch.recenter D h) (η + s • basisVec (parIdx p))) =ᶠ[nhds 0]
              (fun h : Vec 2 => fw t (ch.recenter D h) η) :=
            hN.mono fun h hh => (ih t ht _ hh).2 η s
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [hev.fderiv_eq]
  | @dInternal i p w fw hw ihw =>
    intro hfs hsch hod
    cases hfs with
    | dInternal hfa =>
      cases hsch with
      | dInternal hsa =>
        have ih : ParInvOn D b j₀ i p fw := ihw hfa hsa hod
        intro t ht ch hA
        refine ⟨fun ch' η hp => ?_, fun η s => ?_⟩
        · have : fw t ch' = fw t ch := funext fun z => (ih t ht ch hA).1 ch' z hp
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [this]
        · have h1 : (fun z => fw t ch (z + s • basisVec (parIdx p))) = fw t ch :=
            funext fun z => (ih t ht ch hA).2 z s
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [← fderiv_comp_add_right (s • basisVec (parIdx p)), h1]
  | @restrict i p a fa ha iha =>
    intro hfs hsch hod
    cases hfs with
    | restrict hfa =>
      cases hsch with
      | restrict hsa => exact iha hfa hsa hod
  | @cellInv i p F t₀ ι fF fι hF hι ihF ihι =>
    intro hfs hsch hod
    cases hfs with
    | cellInv _ hFa hιa =>
      obtain ⟨h0, hFs, hιs⟩ := IsScheduled.cellInv_inv hsch
      subst h0
      have ihF' : ∀ k, ParInvOn D b j₀ i p (fF k) := fun k => ihF k (hFa k) (hFs k) (hod.1 k)
      have ihι' : ParInvOn D b j₀ i p fι := ihι hιa hιs hod.2
      intro t ht ch hA
      have ht' : t ∈ Set.Icc (D.slotStart i p) (((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) := ht
      obtain ⟨hw1, hw2⟩ := ht'
      have hwin : ∀ u, D.slotStart i p ≤ u → u ≤ t → u ∈ ocPulseWindow D.α D.q D.Λ i p :=
        fun u h1 h2 => by
          show u ∈ Set.Icc _ _
          exact ⟨h1, h2.trans hw2⟩
      refine ⟨fun ch' η hp => ?_, fun η s => transverseInverseSem_phase D i p fF _ fι t ch η s⟩
      exact transverseInverseSem_chain_on D i p fF _ fι t η hw1
        (fun k u hu => funext fun z => (ihF' k u (hwin u hu.1 hu.2) ch hA).1 ch' z hp)
        (funext fun z => (ihι' _ (hwin _ le_rfl hw1) ch hA).1 ch' z hp)
        (famMetric_parEq D hp)
  | @transPrim i p w fw hw ihw =>
    intro hfs hsch hod
    cases hfs with
    | transPrim hfa =>
      cases hsch with
      | transPrim hsa =>
        have ih : ParInvOn D b j₀ i p fw := ihw hfa hsa hod
        intro t ht ch hA
        refine ⟨fun ch' η hp => ?_, fun η s => transversePrimitiveSem_phase p fw t ch η s⟩
        have : fw t ch' = fw t ch := funext fun z => (ih t ht ch hA).1 ch' z hp
        simp only [transversePrimitiveSem, this]
  | @solved i p G v F q t₀ t₁ c sZ ι fG fv fF fq fι ω h1 h2 hG hv hF hq hι hsol hzero ihG ihv ihF
      ihq ihι =>
    intro hfs _ _
    cases hfs
  | @mean i p w fw hw ihw =>
    intro hfs hsch hod
    cases hfs with
    | mean hfa =>
      cases hsch with
      | mean hsa =>
        have ih : ParInvOn D b j₀ i p fw := ihw hfa hsa hod
        intro t ht ch hA ch' hp
        have : fw t ch' = fw t ch := funext fun z => (ih t ht ch hA).1 ch' z hp
        simp only [cellMeanSem, this]
  | @famCell i p c fc hc ihc =>
    intro hfs hsch hod
    cases hfs with
    | famCell hfa =>
      cases hsch with
      | famCell hsa =>
        have ih : FamInvOn D b j₀ i p fc := ihc hfa hsa hod
        exact fun t ht ch hA => ⟨fun ch' η hp => ih t ht ch hA ch' hp, fun _ _ => rfl⟩
  | @evalChild i p p' c fc hc ihc =>
    intro hfs hsch hod
    cases hfs with
    | «export» hx => exact parInvOn_of_export (hexp _ hx _ (Gen.Denotes.evalChild p' hc))
    | evalChild _ hfa =>
      cases hsch with
      | evalChild _ _ hsi hsa =>
        have ih : FamInvOn D b j₀ (i + 1) p' fc := ihc hfa hsa hod.2
        intro t ht ch hA
        by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
        · exact ⟨fun ch' ζ hp => by
              show _ * _ = _ * _
              rw [hcut, zero_mul, zero_mul],
            fun ζ s => by
              show _ * _ = _ * _
              rw [hcut, zero_mul, zero_mul]⟩
        · have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) :=
            Construction.Stream.ocTau_pos (α := D.α) (q := D.q) (m := i + 1) hΛ
          have htw := mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
          have hl := hA.2.2.1
          have hs := hA.2.2.2.1
          refine ⟨fun ch' ζ hp => ?_, fun ζ s => ?_⟩
          · have hA1 := appendChild_admissible D hΛ hζ hb hstart i p ch hA p' hod.1 hsi t hcut ζ
            show _ * fc t (ch'.appendChild D p' t ζ) = _ * fc t (ch.appendChild D p' t ζ)
            rw [ih t htw _ hA1 _ (hp.appendChild D hl p' t ζ)]
          · have hA1 := appendChild_admissible D hΛ hζ hb hstart i p ch hA p' hod.1 hsi t hcut ζ
            have := parEq_appendChild_shift D ch hl p' t ζ s
            rw [hs] at this
            show _ * fc t (ch.appendChild D p' t (ζ + s • basisVec (parIdx p))) =
              _ * fc t (ch.appendChild D p' t ζ)
            rw [ih t htw _ hA1 _ this]

end Aux

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation, restricted parallel invariance: the theorems**. A scheduled expression
with seed provenance, whose seed exports are certified `IsSlotParInvCtx`, denotes a function that is
invariant under parallel shifts of the final phase and of the child phases, on the pulse window and
the admissible chains of its slot (`denotes_parInvOn_of_odd`). In particular every function
generated from such exports is slotwise structurally transverse (`slotTransverse_of_generated`).
The child slots
of the `evalChild` nodes are odd (`Gen.IsScheduled.evalOdd`), so the appended children
stay admissible. -/

@[expose] public noncomputable section

open Homogenization AVRegularity

namespace AVRegularity.Providers.GenSem

/-- The child slots of the `evalChild` nodes of a scheduled expression are odd. -/
theorem _root_.AVRegularity.Gen.IsScheduled.evalOdd {D : OCData} {s : GenSort} {i : ℕ} {p : ℤ}
    {e : Gen s i p} (h : Gen.IsScheduled D e) : e.EvalOdd := by
  induction h <;> simp_all [Gen.EvalOdd]

theorem denotes_parInvOn_of_odd {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {b : ℝ}
    (hb : 0 < b) {j₀ : ℕ}
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → ∀ f, Gen.Denotes D b j₀ e f →
      IsSlotParInvCtx D b j₀ i p f)
    {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p} (hfs : Gen.FromSeed 𝒮 e)
    (hsch : Gen.IsScheduled D e) (hodd : e.EvalOdd) {f : s.Sem} (hd : Gen.Denotes D b j₀ e f) :
    s.ParInvOn' D b j₀ i p f :=
  denotes_parInvOn_aux hΛ hζ hb hstart hexp hd hfs hsch hodd

theorem slotTransverse_of_generated_odd {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    {b : ℝ} (hb : 0 < b) {j₀ : ℕ}
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → ∀ f, Gen.Denotes D b j₀ e f →
      IsSlotParInvCtx D b j₀ i p f)
    {i : ℕ} {p : ℤ} {f : GenSort.Sem .ctx}
    (hf : ∃ e : Gen .ctx i p, Gen.IsScheduled D e ∧ Gen.FromSeed 𝒮 e ∧ e.EvalOdd ∧
      Gen.Denotes D b j₀ e f) :
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
      ∀ ζ (s : ℝ), f t ch (ζ + s • basisVec (slotParallel p)) = f t ch ζ := by
  obtain ⟨e, hsch, hfs, hodd, hd⟩ := hf
  intro t ht ch hA
  exact (denotes_parInvOn_of_odd hΛ hζ hb hstart hexp hfs hsch hodd hd t ht ch hA).2

/-- **Generated functions are slotwise structurally transverse**. -/
theorem slotTransverse_of_generated {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    {b : ℝ} (hb : 0 < b) {j₀ : ℕ}
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → ∀ f, Gen.Denotes D b j₀ e f →
      IsSlotParInvCtx D b j₀ i p f)
    {i : ℕ} {p : ℤ} {f : GenSort.Sem .ctx} (hf : IsGeneratedCtxFrom D b j₀ 𝒮 i p f) :
    IsSlotTransverseCtx D b j₀ i p f := by
  obtain ⟨e, hsch, hfs, hd⟩ := hf
  exact slotTransverse_of_generated_odd hΛ hζ hb hstart hexp ⟨e, hsch, hfs, hsch.evalOdd, hd⟩

end AVRegularity.Providers.GenSem
end
end

section
/-! Facade: restricted parallel invariance of generated functions. -/
end
end

section
@[expose] public noncomputable section
open Set Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Generation: the cut-off lift setup of the path family of a source.** For a generated, slotwise
transverse stage `G` of level `m`, a path `π` of `G` and an odd slot `k`, the lift sequences of the
scalar path family (`IsLiftSequenceOn (ladderOmega …)`, as in `SuccSource.IsLiftFamily`) with
the reserve `R` and source edges `C^R` on the admissible offsets give the cut-off lift setup of
the family `pathEdgesAt G π k` (`cutoffLiftSetup_of_path`). The edge aggregate is represented by
`edgeURep_of_generated`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem pathEdgesAt_of_admissible (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) {A : RealChain} (hA : IsAdmissibleChain D b j₀ G.level p.1 A) :
    pathEdgesAt G π p A = pathEdges G π p ⟨A, hA⟩ := by
  simp [pathEdgesAt, hA]

/-- The lift window maps into the pulse window. -/
theorem cellScaleSq_mul_mem_ocPulseWindow {m : ℕ} {k : ℤ} (hc : 0 < D.cellScaleSq m) {τ : ℝ}
    (hτ : τ ∈ Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)) :
    D.cellScaleSq m * τ ∈ ocPulseWindow D.α D.q D.Λ m k := by
  obtain ⟨h1, h2⟩ := hτ
  rw [div_le_iff₀ hc] at h1
  rw [le_div_iff₀ hc] at h2
  refine ⟨?_, ?_⟩
  · have : D.slotStart m k = ((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ m := rfl
    linarith
  · linarith

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The cut-off lift setup of the path family of a source.** -/
theorem cutoffLiftSetup_of_path (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (G : GenStage D hr Dm b j₀)
    (hG : G.IsGenerated) (hT : G.IsSlotTransverse) {h : ℕ} (π : StagePath G h) (k : ℤ)
    (hk : Odd k) (ρ : ℝ) (hlam : ρ / D.eps (G.level - 1) ≠ 0)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) {sX sZ N R : ℕ}
    (hRX : R ≤ sX) (hRZ : R ≤ sZ) (hNR : N + Dm + 2 ≤ R)
    (hC : ∀ A (hA : IsAdmissibleChain D b j₀ G.level k A),
      IsLiftSequenceOn (ladderOmega D b j₀ G.level k A ρ)
        (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) sX sZ
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h (Cc A))
    (hedge : ∀ A (hA : IsAdmissibleChain D b j₀ G.level k A),
      ∀ τ ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ),
        γ ∈ (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge v u d →
        ∀ α c, ContDiffOn ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α τ p.1 p.2 c)
          (ladderOmega D b j₀ G.level k A ρ ×ˢ univ)) :
    CutoffLiftSetup D b j₀ G.exports G.level k ρ (pathEdgesAt G π ⟨k, hk⟩) Cc sX sZ N R := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  refine exists_liftGenSetup D hΛ hζ hκ b j₀ G.exports G.level k hk ρ hlam
    (pathEdgesAt G π ⟨k, hk⟩) Cc hRX hRZ hNR (fun A hA => ?_) (fun A hA => ?_) (fun U hU => ?_)
  · rw [pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
    exact hC A hA
  · rw [pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
    exact hedge A hA
  · exact edgeURep_of_generated G hG hT π ⟨k, hk⟩ rfl rfl hε _ U _ _ (fun A hA => hA)
      (fun A hA X hX => hU A hA hX) fun τ hτ => cellScaleSq_mul_mem_ocPulseWindow hc hτ

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Generation, slotwise structural transversality of the successor**. The exports of a
cascade stage are those of the seed (`exports_iff_of_cascade`). A stage whose coefficients are given
by generated expressions (`IsExprFor`) denoting slotwise transverse functions is slotwise
transverse (`isSlotTransverse_of_exprFor`). With the certified seed exports (`IsSlotParInvCtx`) and
the restricted parallel invariance (`slotTransverse_of_generated`), every actual successor of a cascade stage whose
coefficients are generated is slotwise transverse (`successorGeneration_slotTransverse`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The exports of a cascade stage are those of the seed. -/
theorem exports_iff_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm b j₀}
    (h : IsCascadeStage D P Mn seed G) :
    ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), G.exports e ↔ seed.exports e := by
  induction h with
  | seed => exact fun _ _ _ => Iff.rfl
  | step _ hS ih =>
    obtain ⟨-, -, -, -, -, hexp, -⟩ := hS
    exact fun i p e => (hexp i p e).trans (ih i p e)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- A stage whose coefficients are generated expressions denoting slotwise transverse functions is
slotwise transverse. -/
theorem isSlotTransverse_of_exprFor (G : GenStage D hr Dm b j₀)
    (h : ∀ v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (p : OddSlot) → Gen .ctx G.level p.1, G.IsExprFor v u γ d I c e)
    (hT : ∀ (p : OddSlot) (e : Gen .ctx G.level p.1) (f : GenSort.Sem .ctx),
      Gen.IsScheduled D e → Gen.FromSeed G.exports e → Gen.Denotes D b j₀ e f →
        IsSlotTransverseCtx D b j₀ G.level p.1 f) :
    G.IsSlotTransverse := by
  intro p ctx v u γ d I t ht X z s
  funext c
  obtain ⟨e, he⟩ := h v u γ d I c
  obtain ⟨hs, hf, f, hd, hv⟩ := he p
  rw [hv ctx t ht X (z + s • basisVec (slotParallel p.1)), hv ctx t ht X z]
  split_ifs with hA
  · exact hT p (e p) f hs hf hd t ht _ hA z s
  · rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **Generation, transversality, at any menu and any parent with certified exports.** An actual
successor whose coefficients are generated is slotwise structurally transverse when every
denotation of an export of its parent is slotwise parallel invariant (the cascade:
the seed exports; terminal entry: `HasCertifiedExports` of the weak stage). -/
theorem successor_slotTransverse_of_exports (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (hpar : ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), G.exports e →
      ∀ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f → IsSlotParInvCtx D b j₀ i p f)
    (hSucc : IsActualSuccessor D P Mn G G')
    (h : ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1, G'.IsExprFor v u γ d I c e) :
    G'.IsSlotTransverse := by
  obtain ⟨-, -, -, -, -, hexpIff, -⟩ := hSucc
  have hexp : ∀ {i p} (e : Gen .ctx i p), G'.exports e → ∀ f, Gen.Denotes D b j₀ e f →
      IsSlotParInvCtx D b j₀ i p f := fun e he f hd => hpar _ _ e ((hexpIff _ _ e).mp he) f hd
  exact isSlotTransverse_of_exprFor G' h fun p e f hs hf hd =>
    slotTransverse_of_generated hΛ hζ hb hstart hexp ⟨e, hs, hf, hd⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **Generation, transversality.** An actual successor of a cascade stage of a certified seed, whose
coefficients are generated, is slotwise structurally transverse. -/
theorem successorGeneration_slotTransverse (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {P : ProvParams} {Mn : SuccMenu} {seed G G' : GenStage D hr Dm b j₀}
    (hseed : ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e →
      ∀ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f → IsSlotParInvCtx D b j₀ i p f)
    (hcas : IsCascadeStage D P Mn seed G) (hSucc : IsActualSuccessor D P Mn G G')
    (h : ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1, G'.IsExprFor v u γ d I c e) :
    G'.IsSlotTransverse :=
  successor_slotTransverse_of_exports hΛ hζ hb hstart
    (fun i p e he f hd => hseed i p e ((exports_iff_of_cascade hcas i p e).mp he) f hd) hSucc h

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Set Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Generation: a transferred coefficient is generated.** If a new edge of `G'` has the coefficient
`transferAt (fop)` on the admissible recenterings (orders `d ≥ 2`, as in `IsActualSuccessor`) and
the finer outputs of `fop` are family expressions on the admissible families of the finer level
(`SlotFamRep`), then the edge has generated expressions (`isExprFor_of_transfer`):
`transferAt_ctxRep` writes the transfer as one context expression on the admissible contexts and
the pulse window, the appended children read by the transfer being admissible
(`appendChild_admissible`) and their times in the finer pulse window. Orders `d < 2`
have the zero coefficient. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Seed provenance is monotone in the exports. -/
theorem fromSeed_mono {𝒮 𝒮' : SeedExports} (h : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → 𝒮' e) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p}, Gen.FromSeed 𝒮 e → Gen.FromSeed 𝒮' e := by
  intro s i p e he
  induction he with
  | «export» h' => exact .«export» (h _ h')
  | geo fr L => exact .geo fr L
  | drift c => exact .drift c
  | time L => exact .time L
  | add _ _ iha ihb => exact .add iha ihb
  | mul _ _ iha ihb => exact .mul iha ihb
  | dOld j _ ih => exact .dOld j ih
  | dPhase _ ih => exact .dPhase ih
  | dSlowFam j _ ih => exact .dSlowFam j ih
  | dSlowCell j _ ih => exact .dSlowCell j ih
  | dInternal _ ih => exact .dInternal ih
  | restrict _ ih => exact .restrict ih
  | cellInv t₀ _ _ ihF ihι => exact .cellInv t₀ ihF ihι
  | transPrim _ ih => exact .transPrim ih
  | mean _ ih => exact .mean ih
  | famCell _ ih => exact .famCell ih
  | evalChild p' _ ih => exact .evalChild p' ih

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **A transferred coefficient is generated.** -/
theorem isExprFor_of_transfer (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G' : GenStage D hr Dm b j₀) {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → G'.exports e)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1))
    (c : Fin 2) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp)
    (hflux : 2 ≤ d → ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (t : ℝ) (X z : Vec 2),
      G'.fam.flux p ctx v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D (G'.level + 1) p.1 lam Dγ fop t
          (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    (hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
      SlotFamRep D b j₀ 𝒮 (G'.level + 1) k (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀)) :
    ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1, G'.IsExprFor v' u' γ' d I c e := by
  classical
  by_cases hd : 2 ≤ d
  swap
  · -- the zero coefficient
    refine ⟨fun p => Gen.time (s := .ctx) (i := G'.level) (p := p.1) (.const 0), fun p =>
      ⟨.timeConst 0, .time _, GenSort.ofTime .ctx (TimeLetter.eval D (.const 0)), .time _,
        fun ctx t _ X z => ?_⟩⟩
    have hz := G'.fam.flux_zero p ctx v' u' γ' d I (fun h => hd h.1)
    rw [hz]
    split_ifs <;> simp [GenSort.ofTime, TimeLetter.eval]
  have hτ : ∀ k, 0 < ocTau D.α D.q D.Λ k := fun _ => Construction.Stream.ocTau_pos hΛ
  have key : ∀ p : OddSlot, ∃ e : Gen .ctx G'.level p.1, CtxRep D b j₀ 𝒮
      (fun t ch _ => IsAdmissibleChain D b j₀ G'.level p.1 ch ∧
        t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1)
      (fun t ch z => transferAt D (G'.level + 1) p.1 lam Dγ fop t ch z d I c) e := by
    intro p
    refine transferAt_ctxRep hζ G'.level p.1 _ lam Dγ fop d I c
      (scheduledSlots_finite D G'.level p.1 (hτ _)) ?_
    intro k hk hsch d₁ hd₁ I₁ i₀
    obtain ⟨c₁, hs, hf, fc, hden, hv⟩ := hfine k hk d₁
      (by simp only [Finset.mem_Icc] at hd₁; omega) I₁ i₀
    refine ⟨c₁, hs, hf, fc, hden, fun t ch z hP hcut => ?_⟩
    exact hv _ (appendChild_admissible D hΛ hζ hb hstart G'.level p.1 ch hP.1 k hk hsch t hcut z)
      t (mem_ocPulseWindow_of_ocCutoff_ne_zero (hτ _) hcut)
  choose e he using key
  refine ⟨e, fun p => ?_⟩
  obtain ⟨hs, hf, f, hden, hv⟩ := he p
  refine ⟨hs, fromSeed_mono hexp hf, f, hden, fun ctx t ht X z => ?_⟩
  rw [hflux hd p ctx t X z]
  split_ifs with hadm
  · exact (hv t _ z ⟨hadm, ht⟩).symm
  · rfl
end

/-! **Generation: the source edges of the lifts are regular on the admissible offsets.** The lifted
edges of the path family of a context-certified stage are old fluxes at the recentered contexts:
on the admissible offsets `ladderOmega` they are the real semantics of a holomorphically extended
context function along the recentering, hence `C^∞` there (`contDiffOn_holExtension_recenter`).
`contDiffOn_liftedPathEdge` is the `hedge` premise of `cutoffLiftSetup_of_path`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The lifted path edges are `C^∞` on the admissible offsets.** -/
theorem contDiffOn_liftedPathEdge (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ}
    (hcert : G.OldCert 𝒮 μ L Cθ) {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ) {A : RealChain}
    (hA : IsAdmissibleChain D b j₀ G.level k A) {τ : ℝ}
    (hτ : τ ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ)
    (hγ : γ ∈ (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge v u d)
    (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2) (R : ℕ) :
    ContDiffOn ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α τ p.1 p.2 c)
      (ladderOmega D b j₀ G.level k A ρ ×ˢ univ) := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have ht := cellScaleSq_mul_mem_ocPulseWindow hc hτ
  simp only [familyLiftData, liftEdges, List.mem_map] at hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  simp only [pathEdges] at hγ₀
  split_ifs at hγ₀ with hvu hd
  · simp only [List.mem_singleton] at hγ₀
    subst hγ₀
    obtain ⟨θ, -, -, hcert'⟩ := hcert _ _ (π.step ⟨u, hvu.2⟩).2.2
    obtain ⟨f, F, hfF, -⟩ := hcert' d.1 α c
    obtain ⟨-, hhol, hval⟩ := hfF ⟨k, hk⟩
    have htop : ((R : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    refine ((contDiffOn_holExtension_recenter hΛ hb hhol A ρ ht).of_le htop).congr fun p hp => ?_
    show G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α (D.cellScaleSq G.level * τ)
      ((ρ / D.eps (G.level - 1)) • p.1) p.2 c = f ⟨k, hk⟩ _ (A.recenter D (ρ • p.1)) p.2
    have hadm : IsAdmissibleChain D b j₀ G.level k (A.recenter D (ρ • p.1)) := hp.1
    rw [hval ⟨A, hA⟩ _ ht, smul_smul, mul_div_cancel₀ _ hε]
    simp only [hadm, ↓reduceIte]
  · simp at hγ₀
  · simp at hγ₀
end

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.GenSem

/-! **Generation: locality of the covariance letter in the lift data.** The finer output of the
covariance letter at the label `0` (`covLetterFlux`, the `letterCov` branch of `fluxOp`) reads the
path mean flux only through its germ at `0`, which reads the lift data and coefficients only on
an open `Ω ∋ 0` (`pathMeanFlux_germ_dataAgree`, `fluxCoeff_covLetterFlux_agree`). -/

variable {Ω : Set (Vec 2)}

theorem pathMeanFlux_germ_dataAgree (D : OCData) (m : ℕ) (ρ : ℝ) {Dm h : ℕ}
    {Q Q' : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm} (hQ : Uniqueness.DataAgreeOn Ω Q Q')
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (hΩ : IsOpen Ω)
    (h0 : (0 : Vec 2) ∈ Ω)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X)
    (f : Vec 2 → ℝ) :
    pathMeanFlux D m ρ Q Cc n t f =ᶠ[𝓝 0] pathMeanFlux D m ρ Q' Cc' n t f := by
  have hO : IsOpen {y : Vec 2 | ρ⁻¹ • y ∈ Ω} := hΩ.preimage (continuous_const_smul _)
  have h00 : (0 : Vec 2) ∈ {y : Vec 2 | ρ⁻¹ • y ∈ Ω} := by
    show ρ⁻¹ • (0 : Vec 2) ∈ Ω
    rw [smul_zero]; exact h0
  filter_upwards [hO.mem_nhds h00] with y hy
  exact Uniqueness.pathMeanFlux_eq_of_dataAgree D m ρ hQ Cc Cc' n t hΩ hP f y hy

/-- **The finer output of the covariance letter at the label `0`** is that of any lift data and
coefficients agreeing with it on an open `Ω ∋ 0` (the inverse chart map fixing `0`
continuously). -/
theorem fluxCoeff_covLetterFlux_agree (D : OCData) (m : ℕ) (ρ s₀ : ℝ) {Dm h : ℕ}
    {Q Q' : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm} (hQ : Uniqueness.DataAgreeOn Ω Q Q')
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain)
    (hΩ : IsOpen Ω) (h0 : (0 : Vec 2) ∈ Ω)
    (hΦ : ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    fluxCoeff (covLetterFlux D m ρ s₀ Q Cc n a a' t A) d I 0 =
      fluxCoeff (covLetterFlux D m ρ s₀ Q' Cc' n a a' t A) d I 0 := by
  unfold fluxCoeff covLetterFlux pullFlux
  have hgerm := Uniqueness.covOperator_iterate_germ
    (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) a
    (Uniqueness.pushFlux_germ (Ψ := A.famMap D t) hΦ.1 hΦ.2
      (fun g => pathMeanFlux_germ_dataAgree D m ρ hQ Cc Cc' n t hΩ h0 hP g)
      ((SuccSource.covAt D m s₀ t)^[a'] ((fun Y => ∏ j, (Y - 0) (I j)) ∘ A.famMapInv D t)))
  have hΦ0 : A.famMap D t 0 = 0 := by simp [RealChain.famMap]
  simp only [SuccSource.covAtFlux]
  rw [hΦ0, hgerm.eq_of_nhds]

end AVRegularity.Providers.GenSem
end
end
