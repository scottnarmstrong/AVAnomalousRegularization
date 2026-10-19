-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.CtxAssembly
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Construction.Preservation.Seed.SeedLedgerDecayConversion
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The two stage inputs of the native route** (separable parts of the route part
`RoutePieceStatement` of the actual preparation context).

At a context `c` (request `F = c.request`, level `m`, slots `K = Slots H_pr D N_out L_pr`, radius
`ρ_* = rhoStar D k_I.c₀ m`, diffusivity `κ_m`, post-buffer window `[t_buf, t_f]`, incidence
`C_I ε_m^θ` with `θ = min(δ/4, τ_e)`):

* `CopyCoeffConcl` (copied coefficients): the edge coefficients of the neutral chain of the
  actual family of `F.G` (`CopyCoeff`) have finite seminorms, are measurable, `C^{K}` and
  `ℤ²`-periodic on the window, and their Schur matrix at the two weights has the budget
  `C_plain · C_I ε_m^θ` (`C_plain` chosen at the fixed choices).
* `SourceConcl` (plain frame and sampled source): for every native tower of `F` at the buffer
  order and every window proof pair, a plain kernel frame of the time-restricted order-zero
  operator with `φ = φ₀`, `Γ = k_I.Γ`, `L = L_pr`, the slot reserve, the widths
  `≤ (max C_wid 0) ε_m^{σ_f} ρ_*`, the coefficient identity with the actual family, and at the two
  weights a sampled envelope of the actual family at a constant `C_s` (chosen) with a nonnegative
  majorant of Schur budget `C_I ε_m^θ`.

Both in the fixed-choice callback form, with a level `m_*`. Producers:
`localPreparationCoefficientData` with the short charts and the copied envelopes (copies); the
stage kernels of the invariant,
`local_preparation_sampled_envelope` and the record Schur bounds (source).

For an empty component family the Schur sums are empty; the zero weight is not a weight. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The edge coefficients of the neutral chain of the actual family of a request. -/
abbrev CopyCoeff (F : Request hr D Dm bw j₀) (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ) :=
  edgeCoefficient (preparationNeutralChain F.G.actualFamily F.Hpr) (D.κ F.G.level)
    (D.eps F.G.level) (D.eps (F.G.level - 1)) (fun _ => ()) K

/-- The copied-coefficient clauses of a request on its post-buffer window. -/
def CopyCoeffAt (F : Request hr D Dm bw j₀) (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ)
    (Sr : ℝ) : Prop :=
  (∀ x y d, coefficientSeminorm (rhoStar D F.c₀ F.G.level) (K x) F.bufferEnd F.tf
    (CopyCoeff F K x y d) ≠ ⊤) ∧
  (∀ x y d, Measurable (fun p : Set.Icc F.bufferEnd F.tf × Vec 2 =>
    CopyCoeff F K x y d p.1 p.2)) ∧
  (∀ x y d t, t ∈ Set.Icc F.bufferEnd F.tf → ContDiff ℝ (K x : ℕ) (CopyCoeff F K x y d t)) ∧
  (∀ x y d t, t ∈ Set.Icc F.bufferEnd F.tf → IsZ2Periodic (CopyCoeff F K x y d t)) ∧
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    SchurBound Sr (schurMatrix (D.κ F.G.level) (rhoStar D F.c₀ F.G.level)
      (fun x : CompIn F.G.comps × Fin (F.Hpr + 1) => F.G.mass F.law x.1 / w x.1 ^ 2) K Dm
      F.bufferEnd F.tf (CopyCoeff F K))

/-- The plain frame and sampled source of a request at a native tower and a window. -/
def SourceAt (F : Request hr D Dm bw j₀) (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ)
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (Γk : ℝ) (Lpr : ℕ) (q Cs Sinc : ℝ) : Prop :=
  ∃ PF : PreparationPlainKernelFrame (Buffer.kernelOperator_time_restrict
      (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
      (Set.Icc_subset_Icc hac le_rfl) hcb),
    PF.φ = F.φ₀ ∧ PF.matrix_bound = Γk ∧ PF.L = Lpr ∧
    (∀ (l : Fin F.Hpr) j, PF.K j ≤ K (j, l.castSucc)) ∧
    (∀ i j γ, (PF.spec i j γ).width ≤ q * rhoStar D F.c₀ F.G.level) ∧
    (∀ i j γ d, (Buffer.kernelOperator_time_restrict
      (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
      (Set.Icc_subset_Icc hac le_rfl) hcb).B i j γ d =
        constituentPhysical F.G.actualFamily (D.κ F.G.level) (D.eps F.G.level)
          (D.eps (F.G.level - 1)) (fun _ => ()) i j γ d.val) ∧
    ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∃ (Ks : CompIn F.G.comps → ℕ) (Bm : CompIn F.G.comps → CompIn F.G.comps → ℝ),
        (∀ i j, 0 ≤ Bm i j) ∧
        IsSampledEnvelope F.G.actualFamily (fun i => F.G.mass F.law i / w i ^ 2) Ks (fun _ => ())
          F.bufferEnd F.tf (D.κ F.G.level) (D.eps F.G.level) (D.eps (F.G.level - 1))
          (rhoStar D F.c₀ F.G.level) Cs Bm ∧
        SchurBound Sinc Bm

/-- **The copied-coefficient piece at fixed choices**: `C_plain ≥ 0` and a level `m_*`
(`z.2`), then the copied-coefficient clauses at every context of level `≥ m_*`. -/
def CopyCoeffConcl (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ActualX × (ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe _lamE _σE H J N p nk _Lc _Lf Lpr _Acl Naux Nout _Kres npad σ₀ _a
      _σ Hpr sX sZ Ce kS kI CI Cw j₀ z =>
    0 ≤ z.2.1 ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
        kI CI Cw j₀ Hpr Q T₀ hr), z.2.2 ≤ c.m →
      CopyCoeffAt c.request (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr)
        (z.2.1 * (CI * ocEpsilon q Λ c.m ^ min (ocDelta α q / 4) τe))

/-- **The plain-frame and sampled-source piece at fixed choices**: `C_s ≥ 0` and a level `m_*`
(`z.2`), then the source clauses at every context of level `≥ m_*`, every native tower of the
request at the buffer order and every window. -/
def SourceConcl (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ActualX × (ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
      Hpr sX sZ Ce kS kI CI Cw j₀ z =>
    0 ≤ z.2.1 ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
        kI CI Cw j₀ Hpr Q T₀ hr), z.2.2 ≤ c.m →
      ∀ {CK : ℕ → ℝ} {Θ : ℝ}
        (T : PreparationNativeTower c.request (preparationBufferFunction α q Λ φ₀ bw Q T₀ r₀ D₀
          τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) CK Θ)
        (hac : c.request.s ≤ c.request.bufferEnd) (hcb : c.request.bufferEnd ≤ c.request.tf),
      SourceAt c.request (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr) T hac hcb
        kI.Γk Lpr (max kI.Cwid 0 * ocEpsilon q Λ c.m ^ kI.σf) z.2.1
        (CI * ocEpsilon q Λ c.m ^ min (ocDelta α q / 4) τe)

/-- **The copied-coefficient piece.** -/
def CopyCoeffPieceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ (Λg : ℕ) (g₀ : ℕ → ℝ) (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders),
    ActualCallback α s q ζ Λg g₀ orders (CopyCoeffConcl α s q ζ)

/-- **The plain-frame and sampled-source piece.** -/
def SourcePieceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ (Λg : ℕ) (g₀ : ℕ → ℝ) (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders),
    ActualCallback α s q ζ Λg g₀ orders (SourceConcl α s q ζ)
end

/-! The exact source callback from its plain-frame and sampled-source parts. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Two separate clauses of the literal source conclusion, on the same supplied tower. -/
def SourceAtPart (frame : Bool) (F : Request hr D Dm bw j₀) (K : CompIn F.G.comps × Fin (F.Hpr + 1) → ℕ)
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (Γk : ℝ) (Lpr : ℕ) (q Cs Sinc : ℝ) : Prop :=
  if frame then
  ∃ PF : PreparationPlainKernelFrame (Buffer.kernelOperator_time_restrict
      (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
      (Set.Icc_subset_Icc hac le_rfl) hcb),
    PF.φ = F.φ₀ ∧ PF.matrix_bound = Γk ∧ PF.L = Lpr ∧
    (∀ (l : Fin F.Hpr) j, PF.K j ≤ K (j, l.castSucc)) ∧
    (∀ i j γ, (PF.spec i j γ).width ≤ q * rhoStar D F.c₀ F.G.level) ∧
    (∀ i j γ d, (Buffer.kernelOperator_time_restrict
      (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
      (Set.Icc_subset_Icc hac le_rfl) hcb).B i j γ d =
        constituentPhysical F.G.actualFamily (D.κ F.G.level) (D.eps F.G.level)
          (D.eps (F.G.level - 1)) (fun _ => ()) i j γ d.val)
  else
    ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      ∃ (Ks : CompIn F.G.comps → ℕ) (Bm : CompIn F.G.comps → CompIn F.G.comps → ℝ),
        (∀ i j, 0 ≤ Bm i j) ∧
        IsSampledEnvelope F.G.actualFamily (fun i => F.G.mass F.law i / w i ^ 2) Ks (fun _ => ())
          F.bufferEnd F.tf (D.κ F.G.level) (D.eps F.G.level) (D.eps (F.G.level - 1))
          (rhoStar D F.c₀ F.G.level) Cs Bm ∧
        SchurBound Sinc Bm

/-- One source part in the same fixed-choice callback. -/
def SourcePartConcl (frame : Bool) (α s q : ℝ) (ζ : ℝ → ℝ) : PrepData (ActualX × (ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
      Hpr sX sZ Ce kS kI CI Cw j₀ z =>
    0 ≤ z.2.1 ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
        kI CI Cw j₀ Hpr Q T₀ hr), z.2.2 ≤ c.m →
      ∀ {CK : ℕ → ℝ} {Θ : ℝ}
        (T : PreparationNativeTower c.request (preparationBufferFunction α q Λ φ₀ bw Q T₀ r₀ D₀
          τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) CK Θ)
        (hac : c.request.s ≤ c.request.bufferEnd) (hcb : c.request.bufferEnd ≤ c.request.tf),
      SourceAtPart frame c.request (Slots Hpr (succSchedD D₀ N p (H + 1)) Nout Lpr) T hac hcb
        kI.Γk Lpr (max kI.Cwid 0 * ocEpsilon q Λ c.m ^ kI.σf) z.2.1
        (CI * ocEpsilon q Λ c.m ^ min (ocDelta α q / 4) τe)

/-- The frame part (`true`) or sampled-source part (`false`), before every context. -/
def SourcePartStatement (frame : Bool) (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ (Λg : ℕ) (g₀ : ℕ → ℝ) (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders),
    ActualCallback α s q ζ Λg g₀ orders (SourcePartConcl frame α s q ζ)

/-- The two source parts share one sampled constant and the maximum level floor. -/
theorem source_piece_of_parts {α s q : ℝ} {ζ : ℝ → ℝ}
    (hframe : SourcePartStatement true α s q ζ)
    (hsample : SourcePartStatement false α s q ζ) : SourcePieceStatement α s q ζ := by
  intro Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  obtain ⟨yf, hyf, hf'⟩ := hframe Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  obtain ⟨ys, hys, hs'⟩ := hsample Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  refine ⟨(ys.1, max yf.2 ys.2), hys, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CK Θ T hac hcb
  obtain ⟨PF, hφ, hΓ, hL, hK, hw, hB⟩ :=
    hf' c ((le_max_left _ _).trans hm) T hac hcb
  exact ⟨PF, hφ, hΓ, hL, hK, hw, hB,
    hs' c ((le_max_right _ _).trans hm) T hac hcb⟩
end

/-! The actual stage kernels supply the literal plain source frame of every
supplied native tower. Its moments, widths and reserve remain the invariant's. -/

/-- The source frame part, with the original specs and every coefficient retained. -/
theorem source_frame_piece {α s q : ℝ} {ζ : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) : SourcePartStatement true α s q ζ := by
  intro Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x _hx
  have hL := (preparation_context_numeric_orders hα0 hα1 hs0 hs1 hq hf).2.2.2.1
  refine ⟨(0, 0), le_rfl, ?_⟩
  intro hr _ _ _ _ _ _ _ c _hm CK Θ T hac hcb
  let op := T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩
  let op' := Buffer.kernelOperator_time_restrict op (Set.Icc_subset_Icc hac le_rfl) hcb
  let PF := preparation_native_plain_kernel_frame c.request kI c.Mnat c.tA
    (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe)
    (CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe)) c.hinv op'
    (T.kernel (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩)
    Lpr (succSchedD D₀ N p (H + 1) - 2 + Lpr) hL le_rfl
    hf.smooth hf.nonneg hf.mass hf.support
  refine ⟨PF, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro l j
    exact (preparation_descending_copy_orders (succSchedD D₀ N p (H + 1)) Nout Lpr
      _ (j, l.castSucc)).2.2
  · intro i j γ
    obtain ⟨_, _, _, _, _, _, _, _, hspec, _⟩ := c.hinv
    have hw := (hspec i j γ).2.2.1
    change (c.G.kernelOf c.request.P c.seedK c.freshK i j γ).width ≤
      (max kI.Cwid 0 * ocEpsilon q Λ c.m ^ kI.σf) * rhoStar c.D kI.c₀ c.G.level
    have hρ : 0 ≤ rhoStar c.D kI.c₀ c.G.level := op'.radius_pos.le
    calc
      _ = (c.G.fam.identity i j γ).record.width := (hspec i j γ).2.1
      _ ≤ kI.Cwid * rhoStar c.D kI.c₀ c.G.level * c.D.eps c.G.level ^ kI.σf := hw
      _ ≤ max kI.Cwid 0 * rhoStar c.D kI.c₀ c.G.level * c.D.eps c.G.level ^ kI.σf :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ)
          (Real.rpow_nonneg
            (Scales.epsilon_basic (m := c.G.level) (c.q_gt hq.1) (c.lambda_ge hf.hΛ)).1.le _)
      _ = _ := by
        rw [c.hlevel]
        simp only [OCData.eps, c.hq, c.hΛ]
        ring
  · intro i j γ d
    change op.B i j γ d = _
    rw [T.coefficient (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩]
    funext t x
    have hkap : c.D.kap c.G.level = c.D.κ c.G.level :=
      c.kap_eq.trans (congrArg c.D.κ c.hlevel.symm)
    exact (congrArg (fun ν => constituentPhysical c.G.fam ν (c.D.eps c.G.level)
      (c.D.eps (c.G.level - 1)) c.G.actual i j γ d.val t x) hkap).trans
      (c.G.constituentPhysical_actualFamily (c.D.κ c.G.level) (c.D.eps c.G.level)
        (c.D.eps (c.G.level - 1)) i j γ d.val t x).symm

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Short-window copied family inputs of the shared joint preparation.
Time restriction preserves the pointwise envelope as well as the ordinary
envelopes. The copied family retains one actual atlas and both mass budgets. -/

private theorem pointwise_molecular_jet_domain_mono {ι : Type*}
    (dom dom' : ι → Set (ℝ × Vec 2)) (hdom : ∀ i, dom i ⊆ dom' i)
    (ρ e : ℝ) (k j : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) :
    pointwiseMolecularJet ρ e k j dom f ≤ pointwiseMolecularJet ρ e k j dom' f := by
  unfold pointwiseMolecularJet
  exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ => mul_le_mul_right
    (iSup_mono fun i => pointwiseJetSupOn_le_of_eqOn (r + j) q (hdom i)
      (fun _ _ _ => rfl)) _

private theorem pointwise_molecular_domain_mono {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Part : Type*} {Ctx : Part → Type*}
    (F : ChartedFamily ι h D Part Ctx) (π : ι → ℝ) (K : ι → ℕ)
    {dom dom' : F.Domain} (hdom : ∀ p c, dom p c ⊆ dom' p c)
    (ν e E ρ : ℝ) (Cm : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (he : IsPointwiseMolecularEnvelope F π K dom' ν e E ρ Cm J b) :
    IsPointwiseMolecularEnvelope F π K dom ν e E ρ Cm J b := by
  refine ⟨Seed.smoothOn_domain_order_mono F hdom (fun _ => le_rfl) he.1,
    fun v u j hj => le_trans ?_ (he.2 v u j hj)⟩
  exact mul_le_mul_right (Finset.sum_le_sum fun γ _ => mul_le_mul_right
    (Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun I _ => mul_le_mul_left
      (mul_le_mul_left (pointwise_molecular_jet_domain_mono
        (fun x : F.Index => dom x.1 x.2) (fun x : F.Index => dom' x.1 x.2)
        (fun x => hdom x.1 x.2) ρ e (K v) j
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) _) _) _) _

section Family
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- All copied envelopes restrict to a subwindow without changing their
orders, constants, radius, copied mass or normalized majorant. -/
theorem native_copy_envelopes_subwindow (G : GenStage D hr Dm bw j₀) (k : InvConsts)
    {W W' : Set ℝ} (hW : W ⊆ W') (ρ : ℝ) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ) (hE : 0 ≤ D.eps (G.level - 1))
    (he : NativeCopyEnvelopesStatement G k W' ρ H K) :
    NativeCopyEnvelopesStatement G k W ρ H K := by
  intro π hπ
  obtain ⟨ha, hm, hp⟩ := he π hπ
  let F := preparationNeutralChain G.actualFamily H
  have hdom (p : OddSlot) (ctx : Unit) :
      ChartedFamily.Domain.onWindow F W p ctx ⊆ ChartedFamily.Domain.onWindow F W' p ctx :=
    Set.prod_mono (Set.inter_subset_inter_right _ hW) subset_rfl
  have hb := copyMajorant_nonneg G H π
  exact ⟨Seed.analyticEnvelope_mono F π hdom _ _ _ le_rfl le_rfl _ hb le_rfl ha,
    Seed.molecularEnvelope_mono F π K hdom _ _ _ _ hE _ _ le_rfl (fun _ => le_rfl) _ hb hm,
    pointwise_molecular_domain_mono F π K hdom _ _ _ _ _ _ _ hp⟩

variable [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

/-- The literal neutral family has one copied actual atlas, and the same
mass-normalized envelope matrix for both physical masses. -/
structure ModelFamilyData (G : GenStage D hr Dm bw j₀) (law : BirthLaw)
    (kenv : InvConsts) (W : Set ℝ) (ρ S : ℝ) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ) where
  T : (preparationNeutralChain G.actualFamily H).Atlas
  matrix_nonneg : ∀ v u, 0 ≤ preparationNeutralMajorant (recordMajorant (fun _ => 1) G.fam) H v u
  measurable : (preparationNeutralChain G.actualFamily H).IsTimeMeasurable
  weight_measurable : ∀ p, Measurable ((preparationNeutralChain G.actualFamily H).weight p)
  torus : IsTorusCompatible (preparationNeutralChain G.actualFamily H) (fun _ => ())
    (D.eps (G.level - 1))
  cover : W ⊆ ⋃ p, ((preparationNeutralChain G.actualFamily H).piece p).output
  transverse : (preparationNeutralChain G.actualFamily H).IsTransverseOnPulses
    (enlargedPulse D G.level W) parallelIndex
  independent : (preparationNeutralChain G.actualFamily H).IsFastIndependentOn
    (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ G.level ∩ W)
  consecutive : T.IsConsecutiveClosed W
  quiet_cover : T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) W
  quiet : T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
  envelopes : ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
    let C := preparationNeutralChain G.actualFamily H
    let π := fun v : CompIn G.comps × Fin (H + 1) => G.mass law v.1 / w v.1 ^ 2
    let A := preparationNeutralMajorant (recordMajorant (fun _ => 1) G.fam) H
    (∀ v, 0 < π v) ∧
    IsEnvelope C π K (ChartedFamily.Domain.onWindow C W) (D.kap G.level)
      (D.eps G.level) (D.eps (G.level - 1)) ρ (fun v u => Real.sqrt (π u / π v) * A v u)
      S kenv.Ca kenv.Kan kenv.Lan kenv.Cm kenv.Jm ∧
    IsPointwiseMolecularEnvelope C π K (ChartedFamily.Domain.onWindow C W) (D.kap G.level)
      (D.eps G.level) (D.eps (G.level - 1)) ρ kenv.Cm kenv.Jm
      (fun v u => Real.sqrt (π u / π v) * A v u)

/-- Existing geometry and weighted-envelope producers supply all actual
copied-family inputs on any contained invariant window. -/
theorem model_family_data (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ) (k kenv : InvConsts)
    (tA tf S θK : ℝ) (G : GenStage D hr Dm bw j₀)
    (hinv : IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat k tA tf S θK G)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (a b : ℝ) (hsub : Set.Icc a b ⊆ Set.Icc tA tf)
    (ρ : ℝ) (H : ℕ) (K : CompIn G.comps × Fin (H + 1) → ℕ)
    (he : NativeCopyEnvelopesStatement G kenv (Set.Icc a b) ρ H K) :
    Nonempty (ModelFamilyData G law kenv (Set.Icc a b) ρ S H K) := by
  obtain ⟨hm, hw, ht, hcover, htrans, hind, T, hcons, hcov, hquiet⟩ :=
    nativePreparationGeometry law P seedK freshK φ₀ hφ₀ Mnat k tA tf S θK G hinv
      a b hsub (by omega)
  obtain ⟨hm', ht', htrans', hind'⟩ := preparation_neutral_structural G.actualFamily H
    (fun _ => ()) (D.eps (G.level - 1)) (enlargedPulse D G.level (Set.Icc a b))
    parallelIndex _ hm ht htrans hind
  obtain ⟨hcons', hcov', hquiet'⟩ := preparation_neutral_atlas G.actualFamily H T
    (ocQuietTimes D.α D.q D.Λ D.ζ G.level) (Set.Icc a b)
    (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) hcons hcov hquiet
  refine ⟨{ T := preparationNeutralAtlas G.actualFamily H T
            matrix_nonneg := ?_
            measurable := hm', weight_measurable := hw, torus := ht', cover := hcover
            transverse := htrans', independent := hind', consecutive := hcons'
            quiet_cover := hcov', quiet := hquiet'
            envelopes := native_copied_weighted_envelope law P seedK freshK φ₀ hφ₀ Mnat
              k kenv tA tf S θK G hinv hq hΛ (Set.Icc a b) ρ H K he }⟩
  intro v u
  simpa only [div_self one_ne_zero, Real.sqrt_one, one_mul] using
    copyMajorant_nonneg G H (fun _ => 1) v u
end Family

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Fixed numerical choices of the model callback, before every root space,
stage, start time, route, buffer datum and mass. The facts and input prefix
are exactly the callback's binders, bundled once for the joins. -/

/-- One fixed instance of the literal actual callback. The template,
numerical requests and prefix facts precede root spaces and actual stages. -/
structure ModelChoices (α s q : ℝ) (ζ : ℝ → ℝ) (Λg : ℕ) (g₀ : ℕ → ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) where
  Λ : ℕ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  bw : ℝ
  Q : ℝ
  T₀ : ℝ
  r₀ : ℕ
  D₀ : ℕ
  τe : ℝ
  lamE : ℝ
  σE : ℝ
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  nk : ℕ
  Lc : ℕ
  Lf : ℕ
  Lpr : ℕ
  Acl : ℕ
  Naux : ℕ
  Nout : ℕ
  Kres : ℕ
  npad : ℕ
  σ₀ : ℝ
  a : ℝ
  σ : ℝ
  sX : ℕ
  sZ : ℕ
  Ce : ℝ
  kS : InvConsts
  kI : InvConsts
  CI : ℝ
  Cw : ℝ
  j₀ : ℕ
  facts : PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres σ₀ a σ sX sZ Ce kS kI CI Cw j₀
  x : ActualX
  data : preparationOperatorRequestData α s q ζ Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀
    τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    (preparationDepthFunction α q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl
      Naux Nout Kres npad σ₀ a σ) sX sZ Ce kS kI CI Cw j₀ x

namespace ModelChoices
variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λg : ℕ} {g₀ : ℕ → ℝ}
  {orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders}
  (U : ModelChoices α s q ζ Λg g₀ orders)

/-- The same early request of the joint preparation used by the input prefix. -/
def early : PreparationEarlyOrderRequest :=
  ⟨U.Λ, U.Q, U.τe, U.D₀, U.H, U.N, U.p, U.Lpr, U.Nout⟩

/-- Selected insertion depth, independent of seed constants. -/
abbrev Hpr : ℕ := U.early.depth α q

/-- Selected high buffer reserve. -/
abbrev Kbuf : ℕ := U.early.buffer α q

/-- The five supplied early orders of the joint preparation. -/
abbrev gateOrders : PreparationGateNumericOrders := orders U.early

/-- Original copied envelopes at the exact supplied maximal reserves. -/
def envelopeConsts : InvConsts := preparationEnvelopeOrders U.kI
  (max U.Kbuf U.gateOrders.Ks) U.gateOrders.Ks U.gateOrders.Ls
  (max (U.Kbuf + U.early.dimension + 2) U.gateOrders.Jm)

/-- Copied envelopes at the analytic and molecular caps requested by the joint preparation. -/
def gateEnvelopeConsts : InvConsts := preparationEnvelopeOrders U.kI
  (max U.Kbuf U.gateOrders.Ks) U.gateOrders.Ks U.gateOrders.Ls U.gateOrders.Jm

/-- The literal actual contexts at this fixed callback instance. -/
abbrev Context (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] :=
  PrepCtx α s q ζ U.Λ U.φ₀ U.hφ₀ U.bw U.Ce U.τe U.kS U.r₀ U.D₀ U.H U.J U.N U.p U.nk
    U.Naux U.Nout U.npad U.sX U.sZ U.σ₀ U.kI U.CI U.Cw U.j₀ U.Hpr U.Q U.T₀ hr

/-- The same descending copied slots in the model and route parts. -/
abbrev slots {ι : Type} : ι × Fin (U.Hpr + 1) → ℕ :=
  Slots U.Hpr U.early.dimension U.Nout U.Lpr

/-- The scalar buffer price at the selected early order. -/
abbrev Cbuf : ℝ := Real.sqrt (Buffer.bufferEnergyCost U.Kbuf)

/-- Entrance coefficient already supplied by the scalar prefix. -/
abbrev cOld : ℝ := U.x.1.2.2.1

/-- Supplied molecular-to-entrance comparison price. -/
abbrev Crat : ℝ := U.x.1.2.2.2.1

/-- The conclusion of the joint-preparation certificate of the copied family at this fixed
instance. -/
def conclusion (y : ℝ × ℝ × ℕ) : Prop :=
  ModelGateConcl α s q ζ U.Λ U.φ₀ U.hφ₀ U.bw U.Q U.T₀ U.r₀ U.D₀ U.τe U.lamE U.σE
    U.H U.J U.N U.p U.nk U.Lc U.Lf U.Lpr U.Acl U.Naux U.Nout U.Kres U.npad U.σ₀ U.a U.σ
    U.Hpr U.sX U.sZ U.Ce U.kS U.kI U.CI U.Cw U.j₀ (U.x, y)

end ModelChoices

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
section
/-! Uniform actual source budgets at the same early request and incoming stage. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation
open FullLift

/-- Short native charts and the supplied copied envelope price the original source. -/
theorem source_sampled_piece {α s q : ℝ} {ζ : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) :
    SourcePartStatement false α s q ζ := by
  intro Λg g₀ orders Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ sX sZ Ce kS kI CI Cw j₀ hf x hx
  classical
  let E : PreparationEarlyOrderRequest :=
    ⟨Λ, Q, τe, D₀, H, N, p, Lpr, Nout⟩
  let Kbuf := E.buffer α q
  let Jm := max (Kbuf + E.dimension + 2) (orders E).Jm
  let Hpr := E.depth α q
  obtain ⟨Cpad, Cage, Npad, Cchart, mc, _, _, hmc, hcharts⟩ :=
    nativeShortChartCertificate hα0 hα1 hs0 hs1 hq hζ Λ hf.hΛ
  obtain ⟨Cs, hCs, hsample⟩ := local_preparation_sampled_envelope
    E.dimension Kbuf (Kbuf + E.dimension + 2) Jm le_rfl (le_max_left _ _) kI.Cm Cchart
  refine ⟨(Cs, max mc (max x.1.2.1 2)), zero_le_one.trans hCs, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CK Θ T hac hcb
  have hm2 : 2 ≤ c.m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hc0 : kI.c₀ ≤ 1 := hx.1.2.2.2.2.2.2.2
  have hdepth : 1 ≤ Hpr := by
    dsimp only [Hpr, PreparationEarlyOrderRequest.depth, preparationInsertionDepth]
    omega
  have hK : ∀ v : CompIn c.G.comps × Fin (Hpr + 1), Kbuf ≤ max Kbuf (orders E).Ks :=
    fun _ => le_max_left _ _
  have henvCopies := hx.1.2.1 c ((le_max_left _ _).trans ((le_max_right _ _).trans hm))
    (fun _ => Kbuf) hK
  have hmass := c.mass_pos hq.1 hf.hΛ
  have hmark (i : CompIn c.G.comps) : 0 < c.G.marker c.law i :=
    Buffer.birth_compMarker_pos (c.q_gt hq.1) (c.lambda_ge hf.hΛ) c.law i.1
  have hρ : 0 < rhoStar c.D kI.c₀ c.G.level :=
    (T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩).radius_pos
  have he := (Scales.epsilon_basic (m := c.G.level) (c.q_gt hq.1) (c.lambda_ge hf.hΛ)).1
  have hρe : rhoStar c.D kI.c₀ c.G.level ≤ c.D.eps c.G.level := by
    unfold rhoStar
    exact (mul_le_mul_of_nonneg_right hc0
      (le_min he.le (Real.sqrt_nonneg _))).trans ((one_mul _).trans_le (min_le_left _ _))
  have heE : c.D.eps c.G.level ≤ c.D.eps (c.G.level - 1) :=
    Providers.CascadeInvariants.eps_le_of_le (c.q_gt hq.1) (c.lambda_ge hf.hΛ) (Nat.sub_le _ _)
  have hkap : c.D.kap c.G.level = c.D.κ c.G.level :=
    c.kap_eq.trans (congrArg c.D.κ c.hlevel.symm)
  have hshort : ∀ a b : ℝ, c.s₀ ≤ a → a ≤ b → b ≤ c.tf →
      b - a ≤ 2 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level →
      ∃ (l : ℤ) (P : ℕ), IsPreparationChartCertificate c.D.α c.D.q c.D.Λ c.G.level
        (c.D.Φ (c.G.level - 1)) (c.D.hΦ (c.G.level - 1)) a b
        Cpad Cage Npad (Kbuf + E.dimension + 2) Cchart l P c.G.actualFamily := by
    intro a b _ha hab _hb hlen
    have hmM : c.m ≤ c.Mnat := c.m_le_M.trans c.hMnat
    have hn : ∀ pc, IsNaturalPiece c.D c.Mnat c.m pc.val (c.G.actualFamily.piece pc) := by
      intro pc
      exact c.hlevel ▸ c.hinv.1.1 pc
    obtain ⟨l, P, hc⟩ := hcharts c.D c.hα c.hq c.hΛ c.hseq c.Mnat c.m
      ((le_max_left _ _).trans hm) hmM c.G.actualFamily hn a b
      (Kbuf + E.dimension + 2) hab (by
        simpa only [c.hα, c.hq, c.hΛ, c.hlevel] using hlen)
    exact ⟨l, P, by simpa only [c.hα, c.hq, c.hΛ, c.hlevel] using hc⟩
  intro w hw
  have hwpos (i : CompIn c.G.comps) : 0 < w i := by
    rcases hw with rfl | rfl
    · exact zero_lt_one
    · exact hmark i
  let π : CompIn c.G.comps → ℝ := fun i => c.G.mass c.law i / w i ^ 2
  have hπ (i : CompIn c.G.comps) : 0 < π i := div_pos (hmass i) (sq_pos_of_pos (hwpos i))
  have henvC := (henvCopies (fun v => π v.1) (fun v => hπ v.1)).2.2
  have henv := source_pointwise_of_copies c.G.actualFamily Hpr hdepth
    (Set.Icc c.s₀ c.tf) π (fun _ => Kbuf) (c.D.kap c.G.level) (c.D.eps c.G.level)
    (c.D.eps (c.G.level - 1)) (rhoStar c.D kI.c₀ c.G.level) kI.Cm Jm
    (recordMajorant (fun _ => 1) c.G.fam) henvC
  rw [hkap] at henv
  let Bm := fun v u => Real.sqrt (π u / π v) * recordMajorant (fun _ => 1) c.G.fam v u
  have hB (v u : CompIn c.G.comps) : 0 ≤ Bm v u := by
    exact mul_nonneg (Real.sqrt_nonneg _) (by
      unfold recordMajorant
      exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
        mul_nonneg (norm_nonneg _) (c.G.fam.identity v u γ).record.size_nonneg))
  have hsamp := hsample c.D.α c.D.q c.D.Λ c.G.level (c.D.Φ (c.G.level - 1))
    (c.D.hΦ (c.G.level - 1)) c.s₀ c.tf Cpad Cage Npad
    (c.D.κ c.G.level) (c.D.eps c.G.level) (rhoStar c.D kI.c₀ c.G.level)
    (Construction.Stream.ocTauPP_pos (by rw [c.hΛ]; have := hf.hΛ; omega : 1 ≤ c.D.Λ))
    (c.kappa_pos (by have := hf.hΛ; omega) hζ |> fun h => c.hlevel.symm ▸ h) hρ hρe heE
    c.G.actualFamily π hπ (fun _ => Kbuf) (fun _ => le_rfl) (fun _ => ()) Bm hB hshort henv
  have hsamp' := source_sampled_restrict c.G.actualFamily π (fun _ => Kbuf) (fun _ => ())
    c.request.bufferEnd c.tf c.s₀ c.tf (c.D.κ c.G.level) (c.D.eps c.G.level)
    (c.D.eps (c.G.level - 1)) (rhoStar c.D kI.c₀ c.G.level) Cs Bm
    (Set.Icc_subset_Icc hac le_rfl) hsamp
  have hB_eq : Bm = recordMajorant π c.G.fam := by
    funext v u
    simp only [Bm, recordMajorant, div_self one_ne_zero, Real.sqrt_one, one_mul]
  obtain ⟨_, hrow, hcol, hmrow, hmcol⟩ := stage_record_schur_bounds c.hinv
  have hmarked : (∀ v, ∑ u, w v / w u * recordMajorant (c.G.mass c.law) c.G.fam v u ≤
      CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe) ∧
      (∀ u, ∑ v, w v / w u * recordMajorant (c.G.mass c.law) c.G.fam v u ≤
      CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe) := by
    rcases hw with rfl | rfl
    · constructor
      · intro v
        simp only [div_self one_ne_zero, one_mul]
        exact hrow v
      · intro u
        simp only [div_self one_ne_zero, one_mul]
        exact hcol u
    · exact ⟨hmrow, hmcol⟩
  have hschur := recordMajorant_effective_mass_schur c.G.fam (c.G.mass c.law) w hmass hwpos _
    hmarked.1 hmarked.2
  refine ⟨(fun _ => Kbuf), Bm, hB, hsamp', ?_⟩
  rw [hB_eq]
  constructor
  · intro i
    have hh := hschur.1 i
    simp only [OCData.eps, c.hq, c.hΛ] at hh
    exact hh
  · intro i
    have hh := hschur.2 i
    simp only [OCData.eps, c.hq, c.hΛ] at hh
    exact hh

/-- The exact source piece, retaining every supplied native tower and both weights. -/
theorem source_piece {α s q : ℝ} {ζ : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) : SourcePieceStatement α s q ζ :=
  source_piece_of_parts (source_frame_piece hα0 hα1 hs0 hs1 hq)
    (source_sampled_piece hα0 hα1 hs0 hs1 hq hζ)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! One mass-uniform joint preparation of the copied family at each actual context. Its
constants, the readout constants and every level floor are chosen before root spaces.
The actual enhanced radius is the parent lift radius, so its ratio to the
model radius of the joint preparation is exactly cr/c. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation
open WindowCover CycleComparison.Reconstruction

private theorem model_constant_budget {C S r : ℝ} (H N : ℕ)
    (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    jointModelConst C S H N r ≤ jointModelConst C 1 H N r := by
  have hs : (1 : ℝ) + ∑ j ∈ Finset.Icc 1 H, S ^ j ≤
      1 + ∑ j ∈ Finset.Icc 1 H, (1 : ℝ) ^ j :=
    add_le_add le_rfl (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hS hS1 j)
  exact mul_le_mul_of_nonneg_left hs
    (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) N)
      (le_max_right C 0))

/-- The root-free call of the joint preparation and uniform scalar prices yield the shared
joint-preparation certificate at every sufficiently late actual context. -/
theorem model_gate_fixed {α s q : ℝ} {ζ : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ)
    (budget : PreparationCopiedModelBudgetStatement α q ζ)
    {Λg : ℕ} {g₀ : ℕ → ℝ}
    {orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders}
    (horders : ∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
      PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q)
        (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart)
    (hΛb : budget.choose ≤ Λg) (U : ModelChoices α s q ζ Λg g₀ orders) :
    ∃ y, U.conclusion y := by
  have hfloor : Λg ≤ U.Λ := U.data.1.1
  have h128 : 128 ≤ U.Λ := budget.choose_spec.1.trans (hΛb.trans hfloor)
  have hΛ1 : 1 ≤ U.Λ := by omega
  obtain ⟨hc₀, hcr, hCI, _, _, _, _, hθ, _, _⟩ :=
    preparation_context_numeric_orders hα₀ hα₁ hs₀ hs₁ hq U.facts
  have hCI0 : 0 < U.CI := zero_lt_one.trans_le hCI
  obtain ⟨hcOld, _, hmscalar2, hscalar, _, _⟩ := U.data.1.2.2
  obtain ⟨Cpad, Cage, Npad, Cchart, _, hage, ms, hms2, hprep⟩ :=
    Assembly.preservation_preparation_chart_certificate α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ U.Λ h128
  have hg := horders U.early hfloor U.facts.hQ
  obtain ⟨C, CP, cg, mg, hcg, hrun⟩ := hg U.kI.Ca U.CI windowCoverCb U.kI.c₀
    U.cOld U.cOld U.Crat U.kI.Cm windowCoverCG Cchart Cpad Cage Npad hc₀ hcOld
  obtain ⟨mS, hmS⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq.1 h128 hθ
    (inv_pos.mpr hCI0)
  let Cjoint := ((U.Hpr : ℝ) + 1) * (max CP 0 * U.Cbuf)
  let Cjet := ((U.Hpr : ℝ) + 1) *
    (jointModelConst (max C 0) 1 U.Hpr U.Nout (U.kI.cr / cg) * U.Cbuf)
  let mStar := max U.x.1.2.1 (max U.x.1.2.2.2.2 (max ms (max mg mS)))
  have hjet0 : 0 ≤ Cjet := mul_nonneg
    (add_nonneg (Nat.cast_nonneg _) zero_le_one)
    (mul_nonneg (jointModelConst_nonneg _ zero_le_one _ _ _) (Real.sqrt_nonneg _))
  refine ⟨(Cjoint, Cjet, mStar), hjet0, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm
  dsimp only [mStar] at hm
  have hme : U.x.1.2.1 ≤ c.m := by omega
  have hmc : U.x.1.2.2.2.2 ≤ c.m := by omega
  have hm2 : 2 ≤ c.m := hmscalar2.trans hmc
  have hmSch : ms ≤ c.m := by omega
  have hmGate : mg ≤ c.m := by omega
  have hmSmall : mS ≤ c.m := by omega
  have hmM : c.m < c.M := lt_of_le_of_lt c.hmn c.hnM
  let K : CompIn c.G.comps × Fin (U.Hpr + 1) → ℕ := U.slots
  let Fc := preparationNeutralChain c.G.actualFamily U.Hpr
  let A : Matrix (CompIn c.G.comps × Fin (U.Hpr + 1))
      (CompIn c.G.comps × Fin (U.Hpr + 1)) ℝ :=
    preparationNeutralMajorant (recordMajorant (fun _ => 1) c.G.fam) U.Hpr
  let Θ := ocEpsilon q U.Λ c.m ^ min (ocDelta α q / 4) U.τe
  let S := U.CI * Θ
  let old := U.cOld * ocEpsilon q U.Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q)
  let tbuf := c.request.bufferEnd
  let tend := tbuf + 2 * ocTauPP α q U.Λ c.m
  let W := Set.Icc tbuf tend
  have heps := Scales.epsilon_basic (m := c.m) hq.1 h128
  have hΘ0 : 0 ≤ Θ := Real.rpow_nonneg heps.1.le _
  have hΘ1 : Θ ≤ 1 := Real.rpow_le_one heps.1.le heps.2.1 hθ.le
  have hS0 : 0 ≤ S := mul_nonneg hCI0.le hΘ0
  have hS1 : S ≤ 1 := (mul_le_mul_of_nonneg_left (hmS c.m hmSmall) hCI0.le).trans_eq
    (mul_inv_cancel₀ hCI0.ne')
  have hκ : 0 < c.D.κ c.m := c.kappa_pos hΛ1 hζ
  have hB : 0 < c.D.κ (c.m - 1) := c.kappa_pred_pos hΛ1 hζ
  have hT : 0 < ocTauPP α q U.Λ c.m := Stream.ocTauPP_pos hΛ1
  have hE : 0 ≤ c.D.eps (c.G.level - 1) := by
    rw [OCData.eps, c.hq, c.hΛ, c.hlevel]
    exact (Stream.ocEpsilon_pos hΛ1).le
  have hscl := hscalar c.M c.D.κ c.hband c.m hmc hmM
  obtain ⟨hρmol, holdpos, _, hρratio⟩ := hscl.1
  obtain ⟨hdelay, _, hcover⟩ := hscl.2 c.D.Φ c.hseq
  have hρ : rhoStar c.D U.kI.c₀ c.G.level =
      U.kI.c₀ * min (ocEpsilon q U.Λ c.m) (Real.sqrt (c.D.κ c.m / ocA α q U.Λ c.m)) := by
    simp only [rhoStar, OCData.eps, c.hα, c.hq, c.hΛ, c.hlevel]
  have hdelay' : c.request.s ≤ c.request.bufferEnd ∧
      c.request.bufferEnd ≤ c.request.s + 2 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level := by
    constructor
    · change c.s₀ ≤ c.s₀ + rhoStar c.D U.kI.c₀ c.G.level ^ 2 / c.D.κ c.G.level
      rw [c.hlevel]
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hκ.le)
    · change c.s₀ + rhoStar c.D U.kI.c₀ c.G.level ^ 2 / c.D.κ c.G.level ≤ _
      rw [hρ, c.hα, c.hq, c.hΛ, c.hlevel]
      exact add_le_add le_rfl hdelay
  have hbuf : c.s₀ ≤ tbuf := hdelay'.1
  have hbuf2 : tbuf ≤ c.s₀ + 2 * ocTauPP α q U.Λ c.m := by
    have hh := hdelay'.2
    change tbuf ≤ c.s₀ + 2 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level at hh
    simpa only [c.hα, c.hq, c.hΛ, c.hlevel] using hh
  have hendtf : tend ≤ c.tf := by
    dsimp only [tend]
    linarith only [hbuf2, c.htf]
  have hsub : W ⊆ Set.Icc c.s₀ c.tf := Set.Icc_subset_Icc hbuf hendtf
  have hsubInv : W ⊆ Set.Icc c.tA c.tf :=
    hsub.trans (Set.Icc_subset_Icc (c.tA_le_s₀ hΛ1) le_rfl)
  have hK (v : CompIn c.G.comps × Fin (U.Hpr + 1)) : K v ≤ U.Kbuf :=
    (preparation_descending_copy_orders U.early.dimension U.Nout U.Lpr U.Hpr v).1
  have henv := U.data.1.2.1 c hme K (fun v => (hK v).trans (le_max_left _ _))
  change NativeCopyEnvelopesStatement c.G U.envelopeConsts (Set.Icc c.s₀ c.tf)
    (rhoStar c.D U.kI.c₀ c.G.level) U.Hpr K at henv
  have henvW := native_copy_envelopes_subwindow c.G U.envelopeConsts hsub _ U.Hpr K hE henv
  have henvCaps : NativeCopyEnvelopesStatement c.G U.gateEnvelopeConsts W
      (rhoStar c.D U.kI.c₀ c.G.level) U.Hpr K :=
    nativeCopyEnvelopes_mono c.G (k := U.envelopeConsts) (k' := U.gateEnvelopeConsts)
      hE le_rfl le_rfl le_rfl (fun _ => le_rfl)
      (le_max_right _ _) henvW
  obtain ⟨Fam⟩ := model_family_data c.law _ c.seedK c.freshK U.φ₀ U.hφ₀ c.Mnat
    U.kI U.gateEnvelopeConsts c.tA c.tf _ _ c.G c.hinv (c.q_gt hq.1) (c.lambda_ge h128)
    tbuf tend hsubInv _ U.Hpr K henvCaps
  obtain ⟨l₀, P, hP, hleft, hright, hend, hcov⟩ :=
    hcover (c.D.hΦ (c.m - 1)) tbuf U.gateOrders.qJ U.Kbuf
  have hnat (pc : OddSlot) : IsNaturalPiece c.D c.Mnat c.m pc.val (Fc.piece pc) := by
    rw [← c.hlevel]
    exact c.hinv.1.1 pc
  have hcharts := hprep c.D c.hα c.hq c.hΛ c.Mnat c.m hm2 hmSch
    (c.m_le_M.trans c.hMnat) tbuf l₀ P hP hleft hright hend Fc hnat c.hseq U.gateOrders.Jchart
  have heq : c.D.eps c.G.level = ocEpsilon q U.Λ c.m := by
    rw [OCData.eps, c.hq, c.hΛ, c.hlevel]
  have hεm : c.D.eps c.m = ocEpsilon q U.Λ c.m := by
    rw [OCData.eps, c.hq, c.hΛ]
  have hEq : c.D.eps (c.G.level - 1) = ocEpsilon q U.Λ (c.m - 1) := by
    rw [OCData.eps, c.hq, c.hΛ, c.hlevel]
  have hνeq : c.D.kap c.G.level = c.D.κ c.m := c.kap_eq
  have hρeq : rhoStar c.D U.kI.c₀ c.G.level = ocRhoMol α q U.Λ c.m U.kI.c₀ (c.D.κ c.m) :=
    hρ.trans hρmol
  have htrans : Fc.IsTransverseOnPulses
      (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q U.Λ c.m)
        (((k.1 : ℝ) + 3 / 4) * ocTau α q U.Λ c.m) ∩ W) parallelIndex := by
    have hh := Fam.transverse
    change Fc.IsTransverseOnPulses (enlargedPulse c.D c.G.level W) parallelIndex at hh
    rw [c.hlevel] at hh
    have hpulse : enlargedPulse c.D c.m W =
        (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q U.Λ c.m)
          (((k.1 : ℝ) + 3 / 4) * ocTau α q U.Λ c.m) ∩ W) := by
      funext k
      change Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau c.D.α c.D.q c.D.Λ c.m)
        (((k.1 : ℝ) + 3 / 4) * ocTau c.D.α c.D.q c.D.Λ c.m) ∩ W = _
      rw [c.hα, c.hq, c.hΛ]
    exact hpulse ▸ hh
  have hind : Fc.IsFastIndependentOn (ocTrimmedQuietTimes α q U.Λ ζ c.m ∩ W) := by
    simpa only [c.hα, c.hq, c.hΛ, c.hζ, c.hlevel] using Fam.independent
  have htq : Fam.T.IsQuiet (c.D.κ c.m) (ocEpsilon q U.Λ c.m) (ocEpsilon q U.Λ (c.m - 1)) := by
    simpa only [hνeq, heq, hEq] using Fam.quiet
  have htcov : Fam.T.CoversQuiet (ocQuietTimes α q U.Λ ζ c.m) W := by
    simpa only [c.hα, c.hq, c.hΛ, c.hζ, c.hlevel] using Fam.quiet_cover
  have htorus : IsTorusCompatible Fc (fun _ => ()) (ocEpsilon q U.Λ (c.m - 1)) := by
    simpa only [hEq] using Fam.torus
  rw [hρmol] at hρratio
  obtain ⟨tp, Pd, Pg, htp, _, _, hquiet, hquietMargin, hall⟩ := hrun
    K hK c.D.Φ c.hseq c.M c.D.κ c.hband c.m hm2 hmGate hmM.le
    (c.D.κ c.m) (c.D.κ (c.m - 1)) rfl rfl (c.D.hΦ (c.m - 1))
    tbuf (windowCoverCg * (ocA α q U.Λ (c.m - 1) * ocTauPP α q U.Λ c.m))
    (windowCoverCd * ocA α q U.Λ c.m * ocEpsilon q U.Λ c.m ^ 2 / c.D.κ c.m)
    windowCoverB0 1 l₀ P 0 hcov Fc Fam.weight_measurable hcharts (fun _ => ())
    (preparation_neutral_chain_depth c.G.actualFamily U.Hpr)
    (preparation_neutral_chain_descending c.G.actualFamily U.Hpr
      (preparationPlainBaseOrder U.early.dimension U.Nout U.Lpr))
    htorus Fam.cover Fam.measurable A Θ hΘ0 hΘ1 htrans hind Fam.T
    Fam.consecutive htcov htq old ⟨le_rfl, le_rfl⟩ (by exact hρratio)
  let rmodel := cg * Real.sqrt (c.D.κ (c.m - 1) * ocTauPP α q U.Λ c.m)
  have hrmodel : 0 < rmodel := mul_pos hcg (Real.sqrt_pos.mpr (mul_pos hB hT))
  have hρenh : 0 < rhoEnh c.D U.kI.cr c.G.level := by
    rw [rhoEnh, c.hα, c.hq, c.hΛ, c.hlevel]
    exact mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hB hT))
  have hratio : rhoEnh c.D U.kI.cr c.G.level / rmodel = U.kI.cr / cg := by
    rw [rhoEnh, c.hα, c.hq, c.hΛ, c.hlevel]
    dsimp only [rmodel]
    rw [mul_comm cg, ← div_div, mul_div_cancel_right₀ _
      (Real.sqrt_pos.mpr (mul_pos hB hT)).ne']
  refine ⟨{
    tp := tp, A := A, Θ := Θ, S := S, C := max C 0, CP := max CP 0
    ρm := rmodel, Pd := Pd, Pg := Pg, matrix_nonneg := Fam.matrix_nonneg
    budget_nonneg := hS0, model_radius_pos := hrmodel
    error_scale_nonneg := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hE _)
    enhanced_radius_pos := hρenh, delay := hdelay', window := ?_, end_le := htp.2.trans hendtf
    quiet := ?_, quietMargin := ?_, weights := ?_, joint_price := le_rfl, jet_price := ?_ }⟩
  · change tp ∈ Set.Icc tbuf (tbuf + 2 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level)
    rw [c.hα, c.hq, c.hΛ, c.hlevel]
    exact ⟨htp.1.le, htp.2⟩
  · change tp ∈ ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.G.level
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.hlevel]
    exact hquiet
  · change Set.Icc (tp - ocTauP c.D.α c.D.q c.D.Λ c.G.level)
      (tp + ocTauP c.D.α c.D.q c.D.Λ c.G.level) ⊆
        ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.G.level
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.hlevel]
    exact hquietMargin
  · intro w hw
    obtain ⟨hπ, he, hp⟩ := Fam.envelopes w hw
    rw [hνeq, heq, hEq, hρeq] at he hp
    rw [hεm] at he
    obtain ⟨hmodel, herror⟩ := hall _ hπ he hp
    have hh := preparation_joint_constants_mono Fc _ K U.Nout U.Hpr A Fam.matrix_nonneg
      Θ (ocEpsilon q U.Λ (c.m - 1)) U.Q rmodel C CP (c.D.κ c.m) tbuf tp
      (ocRhoMol α q U.Λ c.m U.kI.c₀ (c.D.κ c.m)) old hΘ0
      (Stream.ocEpsilon_pos hΛ1).le (streamVel (c.D.Φ c.m))
      (edgeCoefficient Fc (c.D.κ c.m) (ocEpsilon q U.Λ c.m)
        (ocEpsilon q U.Λ (c.m - 1)) (fun _ => ()) K) Pd Pg hmodel herror
    refine ⟨fun v => hπ (v, 0), ?_, ?_, he.row_sum, he.col_sum⟩
    · change IsJointModel _ K U.Nout U.Hpr Fc A Θ (c.D.eps (c.G.level - 1)) U.Q
        rmodel (max C 0) (max CP 0) Pd Pg
      rw [hEq]
      exact hh.1
    · change IsJointError (fun v : CompIn c.G.comps × Fin (U.Hpr + 1) =>
          c.G.mass c.law v.1 / w v.1 ^ 2) K U.Nout U.Hpr U.early.dimension (c.D.κ c.G.level)
        tbuf tp (rhoStar c.D U.kI.c₀ c.G.level) old (c.D.eps (c.G.level - 1)) U.Q
        (max CP 0) (streamVel (c.D.Φ c.G.level))
        (edgeCoefficient Fc (c.D.κ c.G.level) (c.D.eps c.G.level)
          (c.D.eps (c.G.level - 1)) (fun _ => ()) K) Pd Pg
      rw [hEq, hρeq, heq, c.hlevel]
      exact hh.2
  · change ((U.Hpr : ℝ) + 1) * (jointModelConst (max C 0) S U.Hpr U.Nout
      (rhoEnh c.D U.kI.cr c.G.level / rmodel) * U.Cbuf) ≤ Cjet
    rw [hratio]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (model_constant_budget U.Hpr U.Nout hS0 hS1)
        (Real.sqrt_nonneg _))
      (add_nonneg (Nat.cast_nonneg _) zero_le_one)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The model half of the actual preparation callback. The shared joint preparation is
selected before either mass, datum, insertion route or supplied buffer;
the copied-witness join uses the route's existing copied solutions. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-- The exact model callback, with uniform prices and the same supplied
copied solutions, follows from the actual invariant and the producer of the joint preparation. -/
theorem preparation_model_piece {α s q : ℝ} {ζ : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) :
    ModelPieceStatement α s q ζ := by
  have budget := preparation_copied_model_budget hα₀ hα₁ hs₀ hs₁ hq hζ
  apply model_piece_of_gate
  refine ⟨budget.choose, budget.choose_spec.1, ?_⟩
  intro Λg g₀ orders horders hΛb Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ hf x hx
  let U : ModelChoices α s q ζ Λg g₀ orders :=
    ⟨Λ, φ₀, hφ₀, bw, Q, T₀, r₀, D₀, τe, lamE, σE, H, J, N, p, nk, Lc, Lf, Lpr, Acl,
      Naux, Nout, Kres, npad, σ₀, a, σ, sX, sZ, Ce, kS, kI, CI, Cw, j₀, hf, x, hx⟩
  exact model_gate_fixed hα₀ hα₁ hs₀ hs₁ hq hζ budget horders hΛb U

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
end
