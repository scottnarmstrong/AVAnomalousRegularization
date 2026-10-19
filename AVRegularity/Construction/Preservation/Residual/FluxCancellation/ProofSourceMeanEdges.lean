-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFirstSourcePieceSteps
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.CycleComparison.Reconstruction.InvPiola
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFirstSourceConstGrade0
import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.Proofs.GenSem.Op.FamChart

section
section
/-! The first-source-flux step, sub-step Algebra, chart part: at the native actual context of a piece the
recentred context is `⟨i-1, [p], Y, []⟩` with `Y = Φ_p(t,·)⁻¹ x`, its centred map is
`h ↦ Φ_p(t, Y + h) - x`, the Piola factor cancels the Jacobian of the pull-back, and the
physical point of the recentred context at the label `Y + 𝒜⁻¹(w)` is `x + w`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

section Pure
variable (D : OCData)

/-- The centred map of a native context. -/
theorem fsAlg_famMap_native {i : ℕ} (hi : 1 ≤ i) (pc : ℤ) (Y : Vec 2) (t : ℝ) (h : Vec 2) :
    (⟨i - 1, [pc], Y, []⟩ : RealChain).famMap D t h =
      D.flowOf (i - 1) t (Y + h) (D.slotAnchor i pc) - D.flowOf (i - 1) t Y (D.slotAnchor i pc) := by
  unfold RealChain.famMap
  rw [StrainPhysical.geom_native D i hi]

/-- The inverse of the centred map of a native context. -/
theorem fsAlg_famMapInv_native {i : ℕ} (hi : 1 ≤ i) (pc : ℤ) (Y : Vec 2) (t : ℝ) (w : Vec 2) :
    (⟨i - 1, [pc], Y, []⟩ : RealChain).famMapInv D t w =
      D.flowOf (i - 1) (D.slotAnchor i pc) (D.flowOf (i - 1) t Y (D.slotAnchor i pc) + w) t - Y := by
  unfold RealChain.famMapInv
  rw [StrainPhysical.geom_native D i hi]

/-- The label `Y + 𝒜⁻¹(w)` is the flow back of the point `x + w`, and its physical point is
`x + w`, when `Y` is the flow back of `x`. -/
theorem fsAlg_physPoint {i : ℕ} (hi : 1 ≤ i) (pc : ℤ) (t : ℝ) (x w : Vec 2) :
    D.flowOf (i - 1) t
        (D.flowOf (i - 1) (D.slotAnchor i pc) x t +
          (⟨i - 1, [pc], D.flowOf (i - 1) (D.slotAnchor i pc) x t, []⟩ : RealChain).famMapInv D t w)
        (D.slotAnchor i pc) = x + w := by
  rw [fsAlg_famMapInv_native D hi, add_sub_cancel, flowOf_inv, flowOf_inv]

/-- The Jacobian of the centred map of a native context at `0` is the Jacobian of the material
map at `Y`. -/
theorem fsAlg_famMap_jac {i : ℕ} (hi : 1 ≤ i) (pc : ℤ) (Y : Vec 2) (t : ℝ) :
    jacMatrix ((⟨i - 1, [pc], Y, []⟩ : RealChain).famMap D t) 0 =
      jacMatrix (fun y => D.flowOf (i - 1) t y (D.slotAnchor i pc)) Y := by
  have hfun : (⟨i - 1, [pc], Y, []⟩ : RealChain).famMap D t = fun h =>
      D.flowOf (i - 1) t (Y + h) (D.slotAnchor i pc) - D.flowOf (i - 1) t Y (D.slotAnchor i pc) :=
    funext (fsAlg_famMap_native D hi pc Y t)
  rw [hfun]
  unfold jacMatrix
  ext a c
  simp only [Matrix.of_apply, fderiv_sub_const, fderiv_comp_add_left (f := fun y =>
    D.flowOf (i - 1) t y (D.slotAnchor i pc)), add_zero]

/-- **The Piola factor cancels the Jacobian of the pull-back.** -/
theorem fsAlg_piola_cancel {i : ℕ} (hi : 1 ≤ i) (pc : ℤ) (t : ℝ) (x : Vec 2) :
    chartInvJacobian (fun x' => D.flowOf (i - 1) (D.slotAnchor i pc) x' t) x *
      (jacMatrix ((⟨i - 1, [pc], D.flowOf (i - 1) (D.slotAnchor i pc) x t, []⟩ : RealChain).famMap
        D t) 0)⁻¹ = 1 := by
  have hμ : Differentiable ℝ (fun y => D.flowOf (i - 1) t y (D.slotAnchor i pc)) :=
    (Providers.QuietAtlas.flowOf_contDiff D _ _ _).differentiable (by simp)
  have hψ : Differentiable ℝ (fun x' => D.flowOf (i - 1) (D.slotAnchor i pc) x' t) :=
    (Providers.QuietAtlas.flowOf_contDiff D _ _ _).differentiable (by simp)
  have hK : chartInvJacobian (fun x' => D.flowOf (i - 1) (D.slotAnchor i pc) x' t) x =
      jacMatrix (fun y => D.flowOf (i - 1) t y (D.slotAnchor i pc))
        (D.flowOf (i - 1) (D.slotAnchor i pc) x t) := by
    ext a c
    rw [CycleComparison.Reconstruction.chartInvJacobian_apply_of_inverse hμ hψ
      (fun y => flowOf_inv D _ _ _ y) (fun y => flowOf_inv D _ _ _ y)]
    rfl
  rw [hK, fsAlg_famMap_jac D hi]
  exact Matrix.mul_nonsing_inv _ (by rw [Providers.QuietAtlas.flowOf_det]; exact isUnit_one)

end Pure

section Unfold

/-- The commutator flux `𝒥_H` of `firstSourceFlux`, with the context strain read at the recentred
context of each point. -/
def fsAlgJH (D : OCData) (m : ℕ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) : (Vec 2 → ℝ) → Vec 2 → Vec 2 := fun g x =>
  -((contextStrain D (m - 1) ch.slot t (ch.recenter D (ch.famMapInv D t x))
          (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x) * Hc +
        Hc * Matrix.transpose (contextStrain D (m - 1) ch.slot t
          (ch.recenter D (ch.famMapInv D t x)) (ζ + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x))).mulVec
        (gradField g x))

/-- The commutator sum `∑_l (1/l!) ∑_{a<l} 𝒞^a 𝒥 𝒞^{l-1-a}` for a commutator flux `J`. -/
def fsAlgSum (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (J : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (g : Vec 2 → ℝ) : Vec 2 → Vec 2 := fun z =>
  ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
    (covOperator Hc)^[a] (J ((covOperator Hc)^[l - 1 - a] g)) z

/-- `firstSourceFlux` unfolded. -/
theorem fsAlg_firstSourceFlux_eq (D : OCData) (b : ℝ) (j₀ : ℕ) (Dm m : ℕ) (ρ : ℝ) (N p : ℕ)
    (s₀ : ℝ) (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (u : Vec 2 → ℝ) (y : Vec 2) :
    firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t ch ζ u y =
      ((jacMatrix (ch.famMap D t) y)⁻¹).mulVec
        (covPolyQ (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p (fun x' =>
          -(fsAlgSum (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p
              (fsAlgJH D m (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) t ch ζ)
              (u ∘ ch.famMapInv D t) x') +
            diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ
              (covPolyP (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p
                (u ∘ ch.famMapInv D t)) x') (ch.famMap D t y)) := rfl

end Unfold

section Generic
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} {depth : ℕ}
  {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The recentred actual context of a piece is the native context at the label `Φ_p(t,·)⁻¹ x`. -/
theorem fsAlg_ctx_native (hin : SplitInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2) :
    fsCtx G' p t x = ⟨G'.level - 1, [p.1],
      D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t, []⟩ := by
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  unfold fsCtx
  rw [hnat.2.2.1 p, nativeChain_recenter, tc_material_symm hnat]

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
theorem fsAlg_level_pos (hin : SplitInput P Mn G G' depth CcT) :
    1 ≤ G'.level ∧ j₀ ≤ G'.level ∧ G'.level = G.level - 1 := by
  have hL : G'.level = G.level - 1 := hin.successor.2.1
  have := hin.stage.level
  omega

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The recentred actual context is admissible. -/
theorem fsAlg_ctx_adm (hin : SplitInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2) :
    IsAdmissibleChain D b j₀ G'.level p.1 (fsCtx G' p t x) := by
  obtain ⟨h1, h2, -⟩ := fsAlg_level_pos hin
  rw [fsAlg_ctx_native hin]
  exact nativeChain_isCarrier D b j₀ G'.level p.1 2 h1 h2 p.2 _

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The hypothesis of the strain step, read at the native context. -/
theorem fsAlg_strain_native (hin : SplitInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ)
    (hSS : ∀ Y : Vec 2, contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2))) (Y : Vec 2) :
    contextStrain D G'.level p.1 t ⟨G'.level - 1, [p.1], Y, []⟩ ((D.eps G'.level)⁻¹ • Y) =
      jacMatrix (streamVel (D.Φ G'.level) t)
        (D.flowOf (G'.level - 1) t Y (D.slotAnchor G'.level p.1)) := by
  obtain ⟨h1, -, hL⟩ := fsAlg_level_pos hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have := hSS Y
  rw [← hL, hnat.2.2.1 p, nativeChain_recenter, StrainPhysical.geom_native D _ h1] at this
  exact this

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The commutator flux of `firstSourceFlux` at the recentred actual context is that of the
physical velocity, translated to the centre `x`.** -/
theorem fsAlg_JH_rel (hin : SplitInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2)
    (hSS : ∀ Y : Vec 2, contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2)))
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) :
    fsAlgJH D G.level Hc t (fsCtx G' p t x)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) =
      commutatorFluxJH (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) Hc := by
  obtain ⟨h1, -, hL⟩ := fsAlg_level_pos hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hS := fsAlg_strain_native hin p t hSS
  funext g z
  unfold fsAlgJH commutatorFluxJH
  have key : contextStrain D (G.level - 1) (fsCtx G' p t x).slot t
      ((fsCtx G' p t x).recenter D ((fsCtx G' p t x).famMapInv D t z))
      ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x +
        (D.eps (G.level - 1))⁻¹ • (fsCtx G' p t x).famMapInv D t z) =
      jacMatrix (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) z := by
    rw [← hL, tc_material_symm hnat, fsAlg_ctx_native hin, StrainPhysical.recenter_native,
      ← smul_add]
    beta_reduce
    change contextStrain D G'.level p.1 t _ _ = _
    rw [hS, fsAlg_physPoint D h1 p.1 t x z]
    unfold jacMatrix
    ext a c
    simp only [Matrix.of_apply, fderiv_comp_add_left (f := streamVel (D.Φ G'.level) t)]
  rw [key]

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The three chart facts used by the unfolding: the centre is fixed, the pull-back of a
relabelled field is the translated field, the Piola factor cancels the Jacobian. -/
theorem fsAlg_chart_facts (hin : SplitInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2)
    (f : Vec 2 → ℝ) :
    (fsCtx G' p t x).famMap D t 0 = 0 ∧
    ((fun y => f (((G'.fam.piece p).material t) (((G'.fam.piece p).material t).symm x + y))) ∘
        (fsCtx G' p t x).famMapInv D t) = (fun w => f (x + w)) ∧
    chartInvJacobian ⇑((G'.fam.piece p).material t).symm x *
      (jacMatrix ((fsCtx G' p t x).famMap D t) 0)⁻¹ = 1 := by
  obtain ⟨h1, -, -⟩ := fsAlg_level_pos hin
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hmat : ⇑((G'.fam.piece p).material t) =
      fun y => D.flowOf (G'.level - 1) t y (D.slotAnchor G'.level p.1) := by
    exact (hnat.1 p).2.2.2.2 t
  refine ⟨?_, ?_, ?_⟩
  · rw [fsAlg_ctx_native hin, fsAlg_famMap_native D h1]
    simp
  · funext w
    simp only [Function.comp_apply]
    rw [tc_material_symm hnat, hmat, fsAlg_ctx_native hin]
    beta_reduce
    rw [fsAlg_physPoint D h1 p.1 t x w]
  · rw [tc_material_symm hnat, fsAlg_ctx_native hin]
    exact fsAlg_piola_cancel D h1 p.1 t x

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The Eulerian reading, unfolded.** Given the strain step, `fsEulerRead` is `𝖰_p` of the
translated commutator sum plus the diagonal flux of `𝖯_p` of the translated field, at the centre. -/
theorem fsAlg_unfold (hin : SplitInput P Mn G G' depth CcT) (p : OddSlot) (t : ℝ) (x : Vec 2)
    (hSS : ∀ Y : Vec 2, contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2)))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (f : Vec 2 → ℝ) :
    fsEulerRead Mn G G' Cc0 p t x f =
      covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p (fun x' =>
        -(fsAlgSum (menuCovPrimitive D Mn G.level t) Mn.p
            (commutatorFluxJH (fun y => streamVel (D.Φ (G.level - 1)) t (x + y))
              (menuCovPrimitive D Mn G.level t))
            (fun y => f (x + y)) x') +
          diagFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Cc0 t
            (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)
            (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (fun y => f (x + y))) x') 0 := by
  obtain ⟨h0, hU, hK⟩ := fsAlg_chart_facts hin p t x f
  unfold fsEulerRead
  simp only [fsAlg_ctx_adm hin p t x, ↓reduceIte]
  unfold fsLabelOp
  rw [fsAlg_firstSourceFlux_eq, fsAlg_JH_rel hin p t x hSS, h0, hU, Matrix.mulVec_mulVec]
  rw [hK, Matrix.one_mulVec]
  rfl

end Generic

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, sub-step Piola: split and assembly.

`FSStepPiola` follows from the Piola-transport step (`piecePiolaFiniteOrder`), the order bound
`N + 1 + 4p ≤ Dm` (proved here from `letter_orders`), and two statements about the label operator
`fsLabelOp` of the first source at the recentred actual context:
* `FSPiolaOperator`: on a field of class `C^K`, `K ≥ N + Dm + 4p`, it is, at the centre, the
  differential operator of its symmetric coefficients of the orders `1 .. N + 1 + 4p`
  (finite-regularity form of `firstSourceFlux_applyArr` and `arrOp_eq_sum_fluxCoeff`);
* `FSPiolaConstant`: its order-`1` coefficient vanishes (it kills constants). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Lemma Piola-A.** The label operator is a finite-order differential operator at the centre
on fields of class `C^K`. -/
def FSPiolaOperator : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ u : Vec 2 → ℝ, ContDiff ℝ (K : ℕ∞) u →
      fsLabelOp Mn G G' W.Cc0 p t x u 0 =
        ∑ d ∈ Finset.Icc 1 (Mn.N + 1 + 4 * Mn.p), ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I u 0 • fluxCoeff (fsLabelOp Mn G G' W.Cc0 p t x) d I 0

/-- **Lemma Piola-B.** The label operator kills constants (no zeroth-order term). -/
def FSPiolaConstant : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (I : DerivativeWord2 (1 - 1)),
      fluxCoeff (fsLabelOp Mn G G' W.Cc0 p t x) 1 I 0 = 0

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The order of the first-source identity is at most `Dm`. -/
theorem fsPiola_deg_le {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) : Mn.N + 1 + 4 * Mn.p ≤ Dm := by
  have hdiagA : WordLetter.diag ∈ Mn.A := by
    obtain ⟨Dord, nMax, hMax, npad, hA, -⟩ := hin.range
    rw [hA]; simp [succAlphabet]
  have := (hin.stage.letter_orders _ hdiagA).2
  simp only [letterOrder] at this
  rwa [hin.stage.cutoff_eq, hin.stage.covariance_eq] at this

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The scalar reading of the physical flux of the first source through a piece. -/
theorem fsPiola_phys_scalar (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (p : OddSlot)
    (t : ℝ) (x : Vec 2) (κ : Fin 2) (ℓ : hr v.1.root →L[ℝ] ℝ)
    (hg : ContDiff ℝ (Dm : ℕ∞) (fun y => g t y v)) :
    ℓ (fsPiecePhys Mn G G' Cc0 g v p t x κ) =
      ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (Mn.N + 1 + 4 * Mn.p) (fsPieceArray Mn G G' Cc0 p t x) (d - 1) A x κ *
          orderedDerivative A (fun y => ℓ (g t y v)) x := by
  have e : fsPiecePhys Mn G G' Cc0 g v p t x κ =
      ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (Mn.N + 1 + 4 * Mn.p) (fsPieceArray Mn G G' Cc0 p t x) (d - 1) A x κ •
          orderedDerivative A (fun y => g t y v) x := rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  have hd' := (Finset.mem_Icc.mp hd).2
  have hg' : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) (fun y => g t y v) :=
    hg.of_le (by exact_mod_cast (by omega : d - 1 ≤ Dm))
  exact (congrFun (AVRegularity.orderedDerivative_clm_comp ℓ A hg') x).symm

theorem fsPiola_reindex (F : ℕ → ℝ) (Dγ Dm : ℕ) (hD : Dγ ≤ Dm) (hF1 : F 1 = 0)
    (hFhi : ∀ d, Dγ < d → F d = 0) :
    ∑ d ∈ Finset.Icc 2 Dm, F d = ∑ d ∈ Finset.Icc 1 Dγ, F d := by
  have a : ∑ d ∈ Finset.Icc 2 Dγ, F d = ∑ d ∈ Finset.Icc 2 Dm, F d :=
    Finset.sum_subset (Finset.Icc_subset_Icc_right hD) (fun d hd hnot => hFhi d (by
      simp only [Finset.mem_Icc] at hd hnot; omega))
  have c : ∑ d ∈ Finset.Icc 2 Dγ, F d = ∑ d ∈ Finset.Icc 1 Dγ, F d :=
    Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) (fun d hd hnot => by
      have : d = 1 := by simp only [Finset.mem_Icc] at hd hnot; omega
      rw [this, hF1])
  rw [← a, c]

theorem fsPiola_mulVec (K : Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 2) (S : Finset ℕ)
    (a : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (c : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) :
    (K.mulVec (∑ d ∈ S, ∑ I : DerivativeWord2 (d - 1), a d I • c d I)) κ =
      ∑ d ∈ S, ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2, (K κ i * c d I i) * a d I := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Sub-step Piola from the two statements on the label operator.** -/
theorem fsStepPiola_of_lemmas (PA : FSPiolaOperator) (PB : FSPiolaConstant) : FSStepPiola := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ
  have hdeg := fsPiola_deg_le hin
  obtain ⟨hK, hgg⟩ := hg
  have hgt : ContDiff ℝ (K : ℕ∞) (fun y => g t y v) := by exact_mod_cast (hgg v t ht).1
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  set f : Vec 2 → ℝ := fun y => ℓ (g t y v) with hf
  have hfK : ContDiff ℝ (K : ℕ∞) f := ℓ.contDiff.comp hgt
  rw [fsPiola_phys_scalar Mn G G' W.Cc0 g v p t x κ ℓ
    (hgt.of_le (by exact_mod_cast (by omega : Dm ≤ K)))]
  set B := fsPieceArray Mn G G' W.Cc0 p t x with hB
  set ψ : Vec 2 → Vec 2 := ⇑((G'.fam.piece p).material t).symm with hψ
  set Dγ := Mn.N + 1 + 4 * Mn.p with hDγ
  have hB1 : ∀ I, B 1 I = 0 := fun I => by
    simp only [hB, fsPieceArray]
    split_ifs
    · exact PB P Mn G G' depth CcT hin W p t hp x I
    · rfl
  rw [fsPiola_reindex (fun d => ∑ A : DerivativeWord2 (d - 1),
      transportedCoeff (chartInvJacobian ψ) Dγ B (d - 1) A x κ * orderedDerivative A f x) Dγ Dm
    hdeg ?_ ?_]
  · have hmat : ⇑((G'.fam.piece p).material t) =
        fun y => D.flowOf (G'.level - 1) t y (D.slotAnchor G'.level p.1) :=
      (hnat.1 p).2.2.2.2 t
    have hsymm : ψ = fun x' => D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x' t :=
      tc_material_symm hnat p t
    have hχ : ContDiff ℝ (⊤ : ℕ∞) ⇑((G'.fam.piece p).material t) := by
      rw [hmat]; exact Providers.QuietAtlas.flowOf_contDiff D _ _ _
    have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      rw [hsymm]; exact Providers.QuietAtlas.flowOf_contDiff D _ _ _
    have h1 : ∀ y, ψ (((G'.fam.piece p).material t) y) = y := fun y =>
      ((G'.fam.piece p).material t).symm_apply_apply y
    have h2 : ∀ x, ((G'.fam.piece p).material t) (ψ x) = x := fun x =>
      ((G'.fam.piece p).material t).apply_symm_apply x
    have hV : ContDiff ℝ ((Dγ - 1 : ℕ) : ℕ∞) (fun y => f (((G'.fam.piece p).material t) y)) :=
      (hfK.of_le (by exact_mod_cast (by omega : Dγ - 1 ≤ K))).comp (hχ.of_le (by exact_mod_cast le_top))
    have hP2 := @piecePiolaFiniteOrder ℝ _ _ ⇑((G'.fam.piece p).material t) ψ hχ hψc h1 h2 Dγ
      (fun y => f (((G'.fam.piece p).material t) y)) hV B x κ
    have hVψ : (fun y => f (((G'.fam.piece p).material t) y)) ∘ ψ = f :=
      funext fun y => by simp only [Function.comp_apply, h2]
    rw [hVψ] at hP2
    simp only [smul_eq_mul] at hP2
    refine hP2.trans ?_
    have hadm := fsAlg_ctx_adm hin p t x
    have hu : ContDiff ℝ (K : ℕ∞) (fun y => f (((G'.fam.piece p).material t) (ψ x + y))) :=
      hfK.comp ((hχ.of_le (by exact_mod_cast le_top)).comp (contDiff_const.add contDiff_id))
    unfold fsEulerRead
    simp only [hadm, ↓reduceIte]
    rw [PA P Mn G G' depth CcT hin W p t hp x K hK _ hu, fsPiola_mulVec]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun I _ =>
      Finset.sum_congr rfl fun i _ => ?_
    have hB' : B d I = fluxCoeff (fsLabelOp Mn G G' W.Cc0 p t x) d I 0 := by
      have hadm' : IsAdmissibleChain D b j₀ G'.level p.1
          (RealChain.recenter D (G'.actual p).1 (((G'.fam.piece p).material t).symm x)) := hadm
      simp only [hB, fsPieceArray, hadm', ↓reduceIte]
      rfl
    have hod : orderedDerivative I (fun y => f (((G'.fam.piece p).material t) (ψ x + y))) 0 =
        orderedDerivative I (fun y => f (((G'.fam.piece p).material t) y)) (ψ x) := by
      rw [Providers.QuietAtlas.orderedDerivative_comp_add_left I
        (fun y => f (((G'.fam.piece p).material t) y)) (ψ x)]
      simp only [add_zero]
    rw [hB', hod]
  · refine Finset.sum_eq_zero fun A _ => ?_
    rw [CycleComparison.Reconstruction.transportedCoeff_low_eq_zero _ _ _ (r := 1 - 1) rfl A x κ hB1]
    simp
  · intro d hd
    refine Finset.sum_eq_zero fun A _ => ?_
    rw [transportedCoeff_eq_zero_of_le _ (by omega : Dγ ≤ d - 1) B A x]
    simp

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, the per-pulse identity: the appended child against the native family.

For a coarser slot `p` of level `m` and a finer slot `k` of level `L = m + 1`, both of nonzero
cut-off at the time `t`, the child `𝒜^♮_k` appended to the native context of `p` at the label `Y`
(phase `Y/ε_m`) is admissible, and with `x = Φ_p(t, Y)` the physical point and
`Y₁ = Φ_k(t, ·)⁻¹ x` its finer label:

* `fsd_child_facts`: the child has the history geometry of the native chain of `k` recentred at
  `Y₁` (`tc_appendChild_histEq`), hence the same grade-zero label flux
  (`fsd_diagLabelFlux_eq_of_histEq`), the same centred map at the time `t`, and the same inverse
  (the inverse of a centred map is determined by the map);
* `fsd_native_push`: the push-forward by the centred map of the recentred native chain of its
  label flux, on the field translated to the centre `x`, is the push-forward by the natural chart
  of the label flux of the native chain, at the point `x + x'` (`fsd_diagLabelFlux_recenter`; the
  centred map is `h ↦ Φ_k(t, Y₁ + h) - x`, its Jacobian that of the chart);
* `fsd_child_push`: the two together.

For a constant field `F` both fluxes vanish. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.QuietAtlas Providers.GenSem

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The Jacobian of the centred map of a native context is that of the natural chart. -/
theorem fsd_jac_native {L : ℕ} (hL1 : 1 ≤ L) (k : ℤ) (Y₁ : Vec 2) (t : ℝ) (w : Vec 2) :
    jacMatrix ((⟨L - 1, [k], Y₁, []⟩ : RealChain).famMap D t) w =
      jacMatrix (fun y => D.flowOf (L - 1) t y (D.slotAnchor L k)) (Y₁ + w) := by
  have hfun : (⟨L - 1, [k], Y₁, []⟩ : RealChain).famMap D t = fun h =>
      D.flowOf (L - 1) t (Y₁ + h) (D.slotAnchor L k) - D.flowOf (L - 1) t Y₁ (D.slotAnchor L k) :=
    funext (fsAlg_famMap_native D hL1 k Y₁ t)
  rw [hfun]
  unfold jacMatrix
  ext a c
  simp only [Matrix.of_apply, fderiv_sub_const, fderiv_comp_add_left (f := fun y =>
    D.flowOf (L - 1) t y (D.slotAnchor L k))]

/-- **The pushed label flux of the recentred native chain is the pushed label flux of the native
chain by its natural chart.** -/
theorem fsd_native_push (hζ : IsFastProfile D.ζ) {Mn : SuccMenu} {L : ℕ} (hL1 : 1 ≤ L)
    (hj : j₀ ≤ L) (hc : 0 < D.cellScaleSq L)
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hDL : IsDiagLifts D Dm b j₀ Mn L Cc0) {k : ℤ} (hk : Odd k)
    (hρ : Mn.lenFactor * liftLength D L ≠ 0) (n : ℕ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ L k) (Y₁ : Vec 2) (F : Vec 2 → ℝ) (x' : Vec 2) :
    pushFlux ((⟨L - 1, [k], Y₁, []⟩ : RealChain).famMap D t)
        ((⟨L - 1, [k], Y₁, []⟩ : RealChain).famMapInv D t)
        (diagLabelFlux D Dm L (Mn.lenFactor * liftLength D L) Cc0 k ⟨L - 1, [k], Y₁, []⟩ n t)
        (fun y => F (D.flowOf (L - 1) t Y₁ (D.slotAnchor L k) + y)) x' =
      pushFlux (fun y => D.flowOf (L - 1) t y (D.slotAnchor L k))
        (fun y => D.flowOf (L - 1) (D.slotAnchor L k) y t)
        (diagLabelFlux D Dm L (Mn.lenFactor * liftLength D L) Cc0 k (nativeChain L k) n t) F
        (D.flowOf (L - 1) t Y₁ (D.slotAnchor L k) + x') := by
  have hN : IsAdmissibleChain D b j₀ L k (nativeChain L k) :=
    nativeChain_isCarrier D b j₀ L k 2 hL1 hj hk 0
  have hAy : IsAdmissibleChain D b j₀ L k ((nativeChain L k).recenter D Y₁) := by
    rw [AVRegularity.nativeChain_recenter D]
    exact nativeChain_isCarrier D b j₀ L k 2 hL1 hj hk Y₁
  have hrec := fsd_diagLabelFlux_recenter hζ hc hDL hk hN Y₁ hAy hρ n ht
    (fun y => F (D.flowOf (L - 1) t y (D.slotAnchor L k)))
    (D.flowOf (L - 1) (D.slotAnchor L k) (D.flowOf (L - 1) t Y₁ (D.slotAnchor L k) + x') t - Y₁)
  rw [AVRegularity.nativeChain_recenter D, add_sub_cancel] at hrec
  have hcomp : (fun y => F (D.flowOf (L - 1) t Y₁ (D.slotAnchor L k) + y)) ∘
      (⟨L - 1, [k], Y₁, []⟩ : RealChain).famMap D t =
      fun h' => F (D.flowOf (L - 1) t (Y₁ + h') (D.slotAnchor L k)) := by
    funext h'
    simp only [Function.comp_apply, fsAlg_famMap_native D hL1 k Y₁ t h', add_sub_cancel]
  unfold pushFlux
  rw [hcomp, fsAlg_famMapInv_native D hL1 k Y₁ t x', hrec, fsd_jac_native hL1, add_sub_cancel]
  rfl

/-- **The appended child and the recentred native chain of the finer slot.** -/
theorem fsd_child_facts (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (hbw : 0 < b)
    (hstart : IsCarrierStart D.α D.q D.Λ b 1 1 j₀) {Mn : SuccMenu} {m L : ℕ} (hL : L = m + 1)
    (hm : 1 ≤ m) (hj : j₀ ≤ m) (hc : 0 < D.cellScaleSq L)
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hDL : IsDiagLifts D Dm b j₀ Mn L Cc0) {p : ℤ} (hp : Odd p) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hcp : ocCutoff D.α D.q D.Λ m p t ≠ 0) (hck : ocCutoff D.α D.q D.Λ L k t ≠ 0) (Y : Vec 2)
    (n : ℕ) :
    IsAdmissibleChain D b j₀ L k
        ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)) ∧
      diagLabelFlux D Dm L (Mn.lenFactor * liftLength D L) Cc0 k
          ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)) n t =
        diagLabelFlux D Dm L (Mn.lenFactor * liftLength D L) Cc0 k
          ⟨L - 1, [k], D.flowOf (L - 1) (D.slotAnchor L k)
            (D.flowOf (m - 1) t Y (D.slotAnchor m p)) t, []⟩ n t ∧
      ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)).famMap D t =
        (⟨L - 1, [k], D.flowOf (L - 1) (D.slotAnchor L k)
          (D.flowOf (m - 1) t Y (D.slotAnchor m p)) t, []⟩ : RealChain).famMap D t ∧
      ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)).famMapInv D t =
        (⟨L - 1, [k], D.flowOf (L - 1) (D.slotAnchor L k)
          (D.flowOf (m - 1) t Y (D.slotAnchor m p)) t, []⟩ : RealChain).famMapInv D t := by
  subst hL
  simp only [Nat.add_sub_cancel]
  have hε : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hτk : 0 < ocTau D.α D.q D.Λ (m + 1) := Construction.Stream.ocTau_pos hΛ
  have hτp : 0 < ocTau D.α D.q D.Λ m := Construction.Stream.ocTau_pos hΛ
  have hsp := tc_single_pulse_avail hseq hζ hΛ hstart 0 hm hj hp hcp hck
  have htk : t ∈ ocPulseWindow D.α D.q D.Λ (m + 1) k :=
    mem_ocPulseWindow_of_ocCutoff_ne_zero hτk hck
  have htav : t ∈ availInterval D 0 (m + 1) k := mem_availInterval_of_ocCutoff D hΛ hck
  have hsav : D.slotAnchor (m + 1) k ∈ availInterval D 0 (m + 1) k :=
    slotAnchor_mem_availInterval D 0 (m + 1) k
  have hhist := tc_appendChild_histEq hζ hm hε p k t Y
    (I := availInterval D 0 (m + 1) k)
    (fun u hu v hv => hsp v (uIcc_subset_availInterval D 0 (m + 1) k hsav hu hv))
    (fun v hv => hsp v (uIcc_subset_availInterval D 0 (m + 1) k htav hsav hv))
  have hch : IsAdmissibleChain D b j₀ m p ⟨m - 1, [p], Y, []⟩ :=
    nativeChain_isCarrier D b j₀ m p 2 hm hj hp Y
  have hsch : IsScheduledIn D m k p :=
    ⟨t, Function.mem_support.mpr hck, mem_ocPulseWindow_of_ocCutoff_ne_zero hτp hcp⟩
  have hA : IsAdmissibleChain D b j₀ (m + 1) k
      ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)) :=
    appendChild_admissible D hΛ hζ hbw (startBound_of_carrierStart hΛ le_rfl le_rfl hstart) m p _
      hch k hk hsch t hck _
  have hB : IsAdmissibleChain D b j₀ (m + 1) k ⟨m, [k], labelChange D m p k t Y, []⟩ :=
    nativeChain_isCarrier D b j₀ (m + 1) k 2 (by omega) (by omega) hk _
  have hfm : ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)).famMap D t =
      (⟨m, [k], labelChange D m p k t Y, []⟩ : RealChain).famMap D t :=
    ((histEq_iff_sameHistory D _ _ hhist.1).mp hhist t htav).1
  refine ⟨hA, fsd_diagLabelFlux_eq_of_histEq hζ hc hDL 0 hk hA hB hhist n htk, hfm, ?_⟩
  funext w
  have h1 := famMap_famMapInv hζ
    ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)) t w
  rw [hfm] at h1
  have h2 := famMapInv_famMap hζ (⟨m, [k], labelChange D m p k t Y, []⟩ : RealChain) t
    (((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)).famMapInv D t w)
  rw [h1] at h2
  exact h2.symm

/-- **The pushed label flux of the appended child is the pushed label flux of the native chain of
the finer slot by its natural chart**, at the translated point. -/
theorem fsd_child_push (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (hbw : 0 < b)
    (hstart : IsCarrierStart D.α D.q D.Λ b 1 1 j₀) {Mn : SuccMenu} {m L : ℕ} (hL : L = m + 1)
    (hm : 1 ≤ m) (hj : j₀ ≤ m) (hc : 0 < D.cellScaleSq L)
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hDL : IsDiagLifts D Dm b j₀ Mn L Cc0) (hρ : Mn.lenFactor * liftLength D L ≠ 0) {p : ℤ}
    (hp : Odd p) {k : ℤ} (hk : Odd k) {t : ℝ} (hcp : ocCutoff D.α D.q D.Λ m p t ≠ 0)
    (hck : ocCutoff D.α D.q D.Λ L k t ≠ 0) (Y : Vec 2) (n : ℕ) (F : Vec 2 → ℝ) (x' : Vec 2) :
    IsAdmissibleChain D b j₀ L k
        ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)) ∧
      pushFlux (((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)).famMap D t)
          (((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)).famMapInv D t)
          (diagLabelFlux D Dm L (Mn.lenFactor * liftLength D L) Cc0 k
            ((⟨m - 1, [p], Y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • Y)) n t)
          (fun y => F (D.flowOf (m - 1) t Y (D.slotAnchor m p) + y)) x' =
        pushFlux (fun y => D.flowOf (L - 1) t y (D.slotAnchor L k))
          (fun y => D.flowOf (L - 1) (D.slotAnchor L k) y t)
          (diagLabelFlux D Dm L (Mn.lenFactor * liftLength D L) Cc0 k (nativeChain L k) n t) F
          (D.flowOf (m - 1) t Y (D.slotAnchor m p) + x') := by
  obtain ⟨hA, h1, h2, h3⟩ := fsd_child_facts hΛ hζ hseq hbw hstart hL hm hj hc hDL hp hk hcp hck
    Y n
  refine ⟨hA, ?_⟩
  rw [h1, h2, h3]
  have htk : t ∈ ocPulseWindow D.α D.q D.Λ L k :=
    mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hck
  have hx : D.flowOf (L - 1) t (D.flowOf (L - 1) (D.slotAnchor L k)
      (D.flowOf (m - 1) t Y (D.slotAnchor m p)) t) (D.slotAnchor L k) =
      D.flowOf (m - 1) t Y (D.slotAnchor m p) := flowOf_inv D (L - 1) t (D.slotAnchor L k) _
  have key := fsd_native_push hζ (by omega : 1 ≤ L) (by omega : j₀ ≤ L) hc hDL hk hρ n htk
    (D.flowOf (L - 1) (D.slotAnchor L k) (D.flowOf (m - 1) t Y (D.slotAnchor m p)) t) F x'
  rw [hx] at key
  exact key

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! **Source mean, Right: `SourceMeanRightStatement` from the pulse-reading, regularity and linearity steps.** -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The terms of the expansion are `C^{2p}`. -/
theorem right_term_contDiff (h2 : RightPathRegStatement) (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v))
    (v : CompIn G.comps) (t : ℝ) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) :
    ∀ k ∈ rightPulses D G.level t, ∀ r ∈ Finset.Icc 1 depth,
      ∀ n ∈ Finset.Icc 2 (Mn.N + Dm), ∀ (π : StagePath G r) (a' : ℕ),
      ContDiff ℝ ((2 * Mn.p : ℕ) : WithTop ℕ∞) (fun y => rightTerm Mn W g v ℓ t j k r n π a' y) := by
  intro k hk r hr' n hn π a'
  have hk' := Finset.mem_filter.mp hk
  by_cases hπ : π.tgt = v.1 ∧ π.src ∈ G.comps
  · have := h2 P Mn G G' depth CcT hin W t k hk'.2.1 hk'.2.2 r hr' n hn π _
      (right_field_iter_smooth Mn g hg v ℓ t π hπ.2 a')
    have h := contDiff_pi.mp this j
    simpa [rightTerm, hπ] using h
  · simp only [rightTerm, hπ, dite_false]
    exact contDiff_const

open scoped Classical in
/-- **Source mean, Right, from the pulse-reading, regularity and linearity steps.** -/
theorem sourceMeanRight_of_steps (h1 : RightPulseReadStatement) (h2 : RightPathRegStatement)
    (h3 : RightPathLinearStatement) : SourceMeanRightStatement := by
  intro H5 hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W g hg v t x ℓ j
  have hME : ContDiff ℝ ((2 * Mn.p : ℕ) : WithTop ℕ∞) (fun y => menuMeanFluxE Mn G G.level Mn.N
      depth CcT (menuCovPRep Mn D G.level Mn.p (fun _ => g)) t y v) :=
    menuMeanFluxE_contDiff P Mn G G' depth CcT hin
      (fun _ => actualFluxJointSmooth P Mn G G' depth CcT hin) (Mn.N + Dm + 4 * Mn.p) le_rfl
      (fun _ => g) t (fun w => (hg w).of_le (by exact_mod_cast le_top)) v
  have hA : ℓ ((covMeanAt Mn G G.level Mn.N Mn.p depth CcT (fun _ => g) v t x) j) =
      covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p (rightU Mn W depth g v ℓ t j) x := by
    have := covProj_covPolyQ (menuCovPrimitive D Mn G.level t)
      (ℓ.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => hr v.1.root) j)) Mn.p
      (by exact_mod_cast hME) x
    refine this.trans ?_
    congr 1
    funext y
    exact rightU_eq h1 h3 H5 P Mn G G' depth CcT hin W g hg v t ℓ j y
  rw [hA, rightU_covPolyQ Mn W depth g v ℓ t j
    (right_term_contDiff h2 P Mn G G' depth CcT hin W g hg v t ℓ j) x, right_pathSide_apply]
  symm
  have hz : ∀ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, k ∉ rightPulses D G.level t →
      ocCutoff D.α D.q D.Λ G.level k t *
        ∑ h ∈ Finset.Icc 1 depth, ∑ n ∈ Finset.Icc 2 (Mn.N + Dm),
          ∑ᶠ π : StagePath G h, (if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
            ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
              dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
                (rightField g v ℓ π hπ.2) x j
          else 0) = 0 := by
    intro k hk hnot
    by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
    · rw [hcut, zero_mul]
    · have hodd : ¬ Odd k := fun ho => hnot (Finset.mem_filter.mpr ⟨hk, ho, hcut⟩)
      rw [Finset.sum_eq_zero, mul_zero]
      intro h _
      refine Finset.sum_eq_zero fun n _ => ?_
      refine finsum_eq_zero_of_forall_eq_zero fun π => ?_
      split_ifs with hπ
      · exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a' _ => by
          have h0 := right_dressed_inactive Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k
            hodd t (rightField g v ℓ π hπ.2) x
          rw [h0]; rfl
      · rfl
  rw [← Finset.sum_subset (show rightPulses D G.level t ⊆ ocObsPulses D.α D.q D.Λ G.level t t from
    Finset.filter_subset _ _) hz]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_filter.mp hk
  congr 1
  refine Finset.sum_congr rfl fun r hr' => Finset.sum_congr rfl fun n hn => ?_
  refine finsum_congr fun π => ?_
  by_cases hπ : π.tgt = v.1 ∧ π.src ∈ G.comps
  · simp only [hπ, and_self, dite_true]
    have hV : ∀ a a' : ℕ, a ≤ Mn.p → ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞)
        (pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
          ((SuccSource.covAt D G.level Mn.anchor t)^[a'] (rightField g v ℓ π hπ.2))) :=
      fun a a' ha => (h2 P Mn G G' depth CcT hin W t k hk'.2.1 hk'.2.2 r hr' n hn π _
        (right_field_iter_smooth Mn g hg v ℓ t π hπ.2 a')).of_le
        (by exact_mod_cast (by omega : 2 * a ≤ 2 * Mn.p))
    have e : ∀ a' : ℕ, covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p
        (fun y => rightTerm Mn W g v ℓ t j k r n π a' y) x =
        ∑ a ∈ Finset.range (Mn.p + 1), (((-1 : ℝ) ^ a / (a.factorial : ℝ)) *
          (covOperator (menuCovPrimitive D Mn G.level t))^[a]
            (fun y => pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
              ((SuccSource.covAt D G.level Mn.anchor t)^[a'] (rightField g v ℓ π hπ.2)) y j) x) :=
      fun a' => by
        rw [right_covPolyQ_apply]
        simp only [rightTerm, hπ, and_self, dite_true]
    simp only [e, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun a' _ => ?_
    rw [right_dressed_apply Mn G π _ n a a' k t _ x j (hV a a' (by simpa [Nat.lt_succ_iff] using ha))]
    ring
  · simp only [hπ, dite_false]
    have : ∀ a' : ℕ, covPolyQ (menuCovPrimitive D Mn G.level t) Mn.p
        (fun y => rightTerm Mn W g v ℓ t j k r n π a' y) x = 0 := fun a' => by
      simp only [rightTerm, hπ, dite_false]
      rw [right_covPolyQ_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [ccfo_covOperator_iterate_zero]
      simp
    simp [this]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, sub-step Strain: the context strain at the actual context of a piece of
nonzero weight is `D𝐛_{m-1}`, from the proved `Providers.context_strain_physical` once
`0 < D.α` and `1 < D.q` are available. They are not fields of `SplitInput`,
so the conclusion is stated with them as hypotheses. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **Sub-step Strain, given `0 < α` and `1 < q`.** -/
theorem fs_strain_of_pos {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) (hα : 0 < D.α) (hq : 1 < D.q)
    (p : OddSlot) (t : ℝ) (hp : G'.fam.weight p t ≠ 0) (Y : Vec 2) :
    contextStrain D (G.level - 1) p.1 t ((G'.actual p).1.recenter D Y)
          ((D.eps (G.level - 1))⁻¹ • Y) =
        jacMatrix (streamVel (D.Φ (G.level - 1)) t)
          (((((G'.actual p).1.recenter D Y).geom D).1 t Y
            (((G'.actual p).1.recenter D Y).geom D).2.2)) := by
  have hsucc := hin.successor
  have hnat : G'.IsNatural Mn.M := hsucc.2.2.2.1
  have hL : G'.level = G.level - 1 := hsucc.2.1
  have hlev := hin.stage.level
  have hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 := by rw [← hnat.2.1 p t]; exact hp
  have hτ : 0 < ocTau D.α D.q D.Λ G'.level := Construction.Stream.ocTau_pos hin.stage.base
  have htw : t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1 :=
    Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcp
  rw [hnat.2.2.1 p, hL] 
  rw [hL] at htw
  exact Providers.context_strain_physical D.α D.q hα hq D.Λ D.ζ hin.stage.profile D rfl rfl rfl rfl
    hin.stream (G.level - 1) (by omega) p.1 p.2 t htw Y

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean: the summand of the sum over the sources, kind by kind**.

`sourceTerm` is the summand of `sourceSide` (`sourceSide_eq_finsum`). On the sources with the empty
word it is:

* `sourceTerm_copyQuad`: for a path of `h ≥ 1` edges into `v`, the glue of the dressed terms of
  degree `2`;
* `sourceTerm_letterMean`: for a letter `𝖬_{n,h}` of the alphabet and a path into `v`, the glue of
  the dressed terms of degree `n` minus, for `h = 1`, the glue of the direct part of the order `n`
  of the edge;
* `sourceTerm_letterCov`: for a letter `𝖵_{n,h,a,a'}` of the alphabet and a path into `v`, the glue
  of the dressed terms of degree `n` and orders `(a, a')`;
* `sourceTerm_copyDir`: for an identity of maximal order `≥ 3` into `v`, the glue of its direct
  parts of the orders `3..Dm`;

each on the scalar field of the path (`pathField`: `ℓ ∘ C_π ∘ g_{src π}`) or of the identity
(`edgeField`), and `0` otherwise (`sourceTerm_of_word_ne`, `sourceTerm_letterDiag`).

For a path which does not end at `v`, a letter outside the alphabet, or `h = 0`, the
summand is `0`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The scalar field `ℓ ∘ C_π ∘ g_{src π}` of a path (zero if the source of the path is not a
component of the stage, which happens only for the empty path). -/
def pathField (G : GenStage D hr Dm b j₀) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) {h : ℕ} (π : StagePath G h) : Vec 2 → ℝ :=
  fun y => if hπ : π.src ∈ G.comps then
    ℓ (rootPathMap hr π.src.root π.mapList v.1.root (g y ⟨π.src, hπ⟩)) else 0

theorem pathField_eq (G : GenStage D hr Dm b j₀) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) {h : ℕ} (π : StagePath G h)
    (hπ : π.src ∈ G.comps) :
    (fun y => ℓ (rootPathMap hr π.src.root π.mapList v.1.root (g y ⟨π.src, hπ⟩))) =
      pathField G g v ℓ π := by
  funext y
  unfold pathField
  rw [dite_eq_left hπ]

theorem pathField_contDiff (G : GenStage D hr Dm b j₀)
    {g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root}
    (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) {h : ℕ} (π : StagePath G h) :
    ContDiff ℝ (⊤ : ℕ∞) (pathField G g v ℓ π) := by
  by_cases hπ : π.src ∈ G.comps
  · rw [← pathField_eq G g v ℓ π hπ]
    exact (ℓ.comp (rootPathMap hr π.src.root π.mapList v.1.root)).contDiff.comp (hg ⟨π.src, hπ⟩)
  · have e : pathField G g v ℓ π = fun _ => 0 := by
      funext y
      unfold pathField
      rw [dite_eq_right hπ]
    rw [e]
    exact contDiff_const

/-- The scalar field `ℓ ∘ C_γ ∘ g_u` of an identity `γ : u → v'`. -/
def edgeField (G : GenStage D hr Dm b j₀) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) {v' u : CompIn G.comps} (γ : G.fam.Γ v' u) :
    Vec 2 → ℝ :=
  fun y => ℓ (rootPathMap hr u.1.root
    [⟨u.1.root, v'.1.root, (G.fam.identity v' u γ).map⟩] v.1.root (g y u))

open scoped Classical in
/-- The summand of `sourceSide`. -/
def sourceTerm {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (s : SuccSource G) :
    Vec 2 :=
  if hs : (s.Valid Mn.A Mn.J ∧ s.word = [] ∧ ¬ s.IsDiag) ∧ s.oldTgt = v.1 ∧
      s.oldSrc ∈ G.comps then
    sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s (W.Cc s) t
      (fun y => ℓ (rootPathMap hr s.oldSrc.root s.maps v.1.root (g y ⟨s.oldSrc, hs.2.2⟩))) x
  else 0

theorem sourceSide_eq_finsum {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) :
    sourceSide W g v ℓ t x = ∑ᶠ s : SuccSource G, sourceTerm W g v ℓ t x s := rfl

variable {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}

theorem sourceTerm_of_word_ne (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (s : SuccSource G) (hw : s.word ≠ []) :
    sourceTerm W g v ℓ t x s = 0 := by
  unfold sourceTerm
  exact dite_eq_right fun hs => hw hs.1.2.1

theorem sourceTerm_letterDiag (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (w : List WordLetter) (u : CompIn G.comps) :
    sourceTerm W g v ℓ t x (SuccSource.letterDiag w u) = 0 := by
  unfold sourceTerm
  exact dite_eq_right fun hs => hs.1.2.2 trivial

/-- **The quadratic conversion of a path.** -/
theorem sourceTerm_copyQuad (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) {h : ℕ} (π : StagePath G h) :
    sourceTerm W g v ℓ t x (SuccSource.copyQuad [] h π) =
      if 1 ≤ h ∧ π.tgt = v.1 then
        ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
          dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) 2 0 0 k t
            (pathField G g v ℓ π) x
      else 0 := by
  unfold sourceTerm
  by_cases hc : 1 ≤ h ∧ π.tgt = v.1
  · have hsrc : π.src ∈ G.comps := Providers.CascadeInvariants.stagePath_src_mem π hc.1
    have hs : ((SuccSource.copyQuad [] h π).Valid Mn.A Mn.J ∧
        (SuccSource.copyQuad [] h π).word = [] ∧ ¬ (SuccSource.copyQuad [] h π).IsDiag) ∧
        (SuccSource.copyQuad [] h π).oldTgt = v.1 ∧
        (SuccSource.copyQuad [] h π).oldSrc ∈ G.comps :=
      ⟨⟨⟨Finset.mem_insert_self _ _, fun l hl => by simp [SuccSource.letter?] at hl, hc.1⟩, rfl,
        fun hd => hd⟩, hc.2, hsrc⟩
    rw [dite_eq_left hs, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    rw [← pathField_eq G g v ℓ π hsrc]
    exact sourceEulerOp_copyQuad Mn G π _ t _ x
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact dite_eq_right fun hs => hc ⟨hs.1.1.2.2, hs.2.1⟩

/-- **The letter `𝖬_{n,h}` on a path.** -/
theorem sourceTerm_letterMean (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (n : ℕ) {h : ℕ} (π : StagePath G h) :
    sourceTerm W g v ℓ t x (SuccSource.letterMean [] n h π) =
      if (WordLetter.mean n h ∈ Mn.A ∧ 1 ≤ h) ∧ π.tgt = v.1 then
        (∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
          dressedPathTerm Mn G π (W.Cc (SuccSource.letterMean [] n h π)) n 0 0 k t
            (pathField G g v ℓ π) x) -
        (if hh : h = 1 then gluedFluxOp D G.level
          (fun k => nativeDirect G (π.step ⟨0, by omega⟩).2.2 {n} k t) t
            (pathField G g v ℓ π) x else 0)
      else 0 := by
  unfold sourceTerm
  by_cases hc : (WordLetter.mean n h ∈ Mn.A ∧ 1 ≤ h) ∧ π.tgt = v.1
  · have hsrc : π.src ∈ G.comps := Providers.CascadeInvariants.stagePath_src_mem π hc.1.2
    have hs : ((SuccSource.letterMean [] n h π).Valid Mn.A Mn.J ∧
        (SuccSource.letterMean [] n h π).word = [] ∧
        ¬ (SuccSource.letterMean [] n h π).IsDiag) ∧
        (SuccSource.letterMean [] n h π).oldTgt = v.1 ∧
        (SuccSource.letterMean [] n h π).oldSrc ∈ G.comps :=
      ⟨⟨⟨Finset.mem_insert_self _ _, fun l hl => by
          simp only [SuccSource.letter?, Option.some.injEq] at hl
          subst hl
          exact ⟨Nat.zero_le _, hc.1.1⟩, hc.1.2⟩, rfl, fun hd => hd⟩, hc.2, hsrc⟩
    rw [dite_eq_left hs, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    rw [← pathField_eq G g v ℓ π hsrc]
    exact sourceEulerOp_letterMean Mn G π _ n t _ x
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact dite_eq_right fun hs => hc ⟨⟨(hs.1.1.2.1 _ rfl).2, hs.1.1.2.2⟩, hs.2.1⟩

/-- **The letter `𝖵_{n,h,a,a'}` on a path.** -/
theorem sourceTerm_letterCov (W : SplitWitness P Mn G G') (hm : 1 ≤ G.level)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (n a a' : ℕ) {h : ℕ} (π : StagePath G h) :
    sourceTerm W g v ℓ t x (SuccSource.letterCov [] n h a a' π) =
      if (WordLetter.covariance n h a a' ∈ Mn.A ∧ 1 ≤ h) ∧ π.tgt = v.1 then
        ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
          dressedPathTerm Mn G π (W.Cc (SuccSource.letterCov [] n h a a' π)) n a a' k t
            (pathField G g v ℓ π) x
      else 0 := by
  unfold sourceTerm
  by_cases hc : (WordLetter.covariance n h a a' ∈ Mn.A ∧ 1 ≤ h) ∧ π.tgt = v.1
  · have hsrc : π.src ∈ G.comps := Providers.CascadeInvariants.stagePath_src_mem π hc.1.2
    have hs : ((SuccSource.letterCov [] n h a a' π).Valid Mn.A Mn.J ∧
        (SuccSource.letterCov [] n h a a' π).word = [] ∧
        ¬ (SuccSource.letterCov [] n h a a' π).IsDiag) ∧
        (SuccSource.letterCov [] n h a a' π).oldTgt = v.1 ∧
        (SuccSource.letterCov [] n h a a' π).oldSrc ∈ G.comps :=
      ⟨⟨⟨Finset.mem_insert_self _ _, fun l hl => by
          simp only [SuccSource.letter?, Option.some.injEq] at hl
          subst hl
          exact ⟨Nat.zero_le _, hc.1.1⟩, hc.1.2⟩, rfl, fun hd => hd⟩, hc.2, hsrc⟩
    rw [dite_eq_left hs, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    rw [← pathField_eq G g v ℓ π hsrc]
    exact sourceEulerOp_letterCov Mn G hm π _ n a a' t _ x
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact dite_eq_right fun hs => hc ⟨⟨(hs.1.1.2.1 _ rfl).2, hs.1.1.2.2⟩, hs.2.1⟩

/-- **The direct transport of an identity.** -/
theorem sourceTerm_copyDir (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (v' u : CompIn G.comps) (γ : G.fam.Γ v' u) :
    sourceTerm W g v ℓ t x (SuccSource.copyDir [] v' u γ) =
      if 3 ≤ (G.fam.identity v' u γ).maxOrder ∧ v'.1 = v.1 then
        gluedFluxOp D G.level (fun k => nativeDirect G γ (Finset.Icc 3 Dm) k t) t
          (edgeField G g v ℓ γ) x
      else 0 := by
  unfold sourceTerm
  by_cases hc : 3 ≤ (G.fam.identity v' u γ).maxOrder ∧ v'.1 = v.1
  · have hs : ((SuccSource.copyDir [] v' u γ).Valid Mn.A Mn.J ∧
        (SuccSource.copyDir [] v' u γ).word = [] ∧ ¬ (SuccSource.copyDir [] v' u γ).IsDiag) ∧
        (SuccSource.copyDir [] v' u γ).oldTgt = v.1 ∧
        (SuccSource.copyDir [] v' u γ).oldSrc ∈ G.comps :=
      ⟨⟨⟨Finset.mem_insert_self _ _, fun l hl => by simp [SuccSource.letter?] at hl, hc.1⟩, rfl,
        fun hd => hd⟩, hc.2, u.2⟩
    rw [dite_eq_left hs, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    exact sourceEulerOp_copyDir G γ _ Mn.anchor (W.Cc (SuccSource.copyDir [] v' u γ)) t
      (edgeField G g v ℓ γ) x
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact dite_eq_right fun hs => hc ⟨hs.1.1.2.2, hs.2.1⟩

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The source-mean step, the one-edge paths are the identities**.

`edgePath`: the path of one edge of an identity; `edgePathEquiv`: every path of one edge is one.
For the path of an identity `γ : u → v'`: its target is `v'`, its source `u`, its first step `γ`,
and its scalar field is the scalar field of the identity (`pathField_edgePath`).

`sum_sigma_one_edge`: a sum over the grades `1..depth` and the paths of a summand supported on the
grade `1` is the sum over the identities (and `0` if `depth = 0`).

For a stage without identities both sums are empty. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Construction.Preservation.Ledger

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The path of one edge of an identity. -/
def edgePath (G : GenStage D hr Dm b j₀) (y : Σ v u : CompIn G.comps, G.fam.Γ v u) :
    StagePath G 1 :=
  ⟨fun _ => y, fun j hj => absurd hj (by omega)⟩

theorem edgePath_step (G : GenStage D hr Dm b j₀) (π : StagePath G 1) :
    edgePath G (π.step ⟨0, Nat.one_pos⟩) = π := by
  apply stagePath_step_injective G 1
  funext j
  have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
  rw [hj]
  rfl

/-- The paths of one edge are the identities. -/
def edgePathEquiv (G : GenStage D hr Dm b j₀) :
    (Σ v u : CompIn G.comps, G.fam.Γ v u) ≃ StagePath G 1 where
  toFun := edgePath G
  invFun := fun π => π.step ⟨0, Nat.one_pos⟩
  left_inv := fun _ => rfl
  right_inv := edgePath_step G

theorem edgePath_tgt (G : GenStage D hr Dm b j₀) (y : Σ v u : CompIn G.comps, G.fam.Γ v u) :
    (edgePath G y).tgt = y.1.1 := rfl

/-- The scalar field of the path of an identity is the scalar field of the identity. -/
theorem pathField_edgePath (G : GenStage D hr Dm b j₀)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (v' u : CompIn G.comps) (γ : G.fam.Γ v' u) :
    pathField G g v ℓ (edgePath G ⟨v', u, γ⟩) = edgeField G g v ℓ γ := by
  rw [← pathField_eq G g v ℓ (edgePath G ⟨v', u, γ⟩) u.2]
  rfl

/-- **A sum over the grades and the paths of a summand supported on the grade `1`** is the sum over
the identities. -/
theorem sum_sigma_one_edge {V : Type*} [AddCommMonoid V] (G : GenStage D hr Dm b j₀) (depth : ℕ)
    (Θ : ∀ h : ℕ, StagePath G h → V) :
    ∑ x ∈ (Finset.Icc 1 depth).sigma (fun h => (Finset.univ : Finset (StagePath G h))),
        (if x.1 = 1 then Θ x.1 x.2 else 0) =
      if 1 ≤ depth then ∑ y : (Σ v u : CompIn G.comps, G.fam.Γ v u), Θ 1 (edgePath G y) else 0 := by
  rw [Finset.sum_sigma]
  have e : ∀ h ∈ Finset.Icc 1 depth, ∑ π : StagePath G h, (if h = 1 then Θ h π else 0) =
      if h = 1 then ∑ π : StagePath G h, Θ h π else 0 := by
    intro h _
    by_cases hh : h = 1
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl e]
  by_cases hd : 1 ≤ depth
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd), Finset.sum_eq_single 1]
    · simp only [↓reduceIte]
      exact ((edgePathEquiv G).sum_comp (Θ 1)).symm
    · intro h _ hh
      simp only [hh, ↓reduceIte]
    · intro h1
      exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hd⟩) h1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    refine Finset.sum_eq_zero fun h hh => ?_
    have := Finset.mem_Icc.1 hh
    omega

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
