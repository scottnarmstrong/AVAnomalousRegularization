-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.GenSem.Op.FamChart
public import AVRegularity.Proofs.CascadeInvariants.Jet.Ops
import AVRegularity.Proofs.GenSem.Jet.Chart
public import AVRegularity.Proofs.CascadeInvariants.Graded.SlotFam
public import AVRegularity.Proofs.GenSem.Finer.CovLetterRep
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, sized jets: the family instance.** Over a graded context `X`, on a window `W` of
times and base chains:
* `famAlgQ`: the sized family algebra (`repAlgQ_famAlgQ`): `F` agrees on `W` with the denotation
  of a scheduled, seed-provenanced family expression without uncertified solved node, whose
  structural norm at the reserve `mres` is at most `C` whenever `mres + rΔ ≤ μ₀`;
* `jetRepGQ_covariant_on`: a covariant label function (its value at the label `w` is a family
  function at the recentered family) has sized jets of every order: one label derivative is one
  slow family derivative, of cost `σ ≥ C_slow/(ε_{i-1}Δ)` and one reserve step;
* the chart leaves: the Jacobian letters (`jetRepGQ_famLetter`, size `K_g`), the first
  derivatives of the centered map (`jetRepGQ_dLabel_famMap`) and of its inverse
  (`jetRepGQ_dLabel_famMapInv`, by the chain rule, with the constants `invP K_g n`), the inverse
  Jacobian (`jetRepGQ_jacInv_famMap`);
* `famAlgQ_time`: a time letter, with the size of its values. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

section Nodes

variable (D : OCData) (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

theorem genNorm_dSlowFam_eq {i : ℕ} {p : ℤ} (j : Fin 2) {c : Gen .fam i p}
    (hl : leaf (Gen.dSlowFam j c) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.dSlowFam j c) a mres L t =
      if mres + Δ ≤ 2 then κc.Cslow / ENNReal.ofReal (D.eps (i - 1) * Δ) *
        genNorm D κc Δ a₀ leaf c a (mres + Δ) L t else ⊤ := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_time_eq {s : GenSort} {i : ℕ} {p : ℤ} (Lt : TimeLetter)
    (hl : leaf (Gen.time (s := s) (i := i) (p := p) Lt) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.time (s := s) (i := i) (p := p) Lt) a mres L t =
      ENNReal.ofReal |Lt.eval D t| := by
  simp only [genNorm, hl, Option.elim]

end Nodes

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
  {W : Set (ℝ × RealChain)} {X : GCtx}

variable (D bw j₀ 𝒮 i p W X) in
/-- The sized family algebra on the window `W`, over the graded context `X`. -/
def famAlgQ : (W → ℝ) → ℕ → ℝ≥0 → Prop :=
  fun F r C => ∃ c : Gen .fam i p, Gen.IsScheduled D c ∧ Gen.FromSeed 𝒮 c ∧
    (∃ fc : GenSort.Sem .fam, Gen.Denotes D bw j₀ c fc ∧ ∀ q : W, F q = fc q.1.1 q.1.2) ∧
    Gen.SolvedFree X.leaf c ∧
    ∀ t ∈ X.T, ∀ mres, mres + r * X.Δ ≤ X.μ₀ →
      genNorm D X.κ X.Δ X.a₀ X.leaf c X.a₀ mres 0 t ≤ C

theorem repAlgQ_famAlgQ (hX : X.Ok) : RepAlgQ (famAlgQ D bw j₀ 𝒮 i p W X) where
  mono := by
    rintro F r r' C C' ⟨c, hs, hf, hv, hsf, hn⟩ hr hC
    refine ⟨c, hs, hf, hv, hsf, fun t ht mres hm =>
      (hn t ht mres ?_).trans (ENNReal.coe_le_coe.mpr hC)⟩
    have hrr : (r : ℝ) * X.Δ ≤ r' * X.Δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hX.hΔ
    linarith
  const := fun a => ⟨Gen.time (.const a), .timeConst a, .time _, ⟨_, .time _, fun _ => rfl⟩,
    trivial, fun t _ mres _ => by
      rw [genNorm_const_eq _ _ _ _ _ a (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx)]
      exact le_rfl⟩
  add := by
    rintro F G r C₁ C₂ ⟨a, sa, fa, ⟨f, hf, hF⟩, hsa, hna⟩ ⟨b, sb, fb, ⟨g, hg, hG⟩, hsb, hnb⟩
    refine ⟨Gen.add a b, .add sa sb, .add fa fb, ⟨GenSort.add .fam f g, .add hf hg, fun q => ?_⟩,
      Or.inr ⟨hsa, hsb⟩, fun t ht mres hm => ?_⟩
    · show F q + G q = f q.1.1 q.1.2 + g q.1.1 q.1.2
      rw [hF q, hG q]
    · rw [genNorm_add_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), ENNReal.coe_add]
      exact add_le_add (hna t ht mres hm) (hnb t ht mres hm)
  mul := by
    rintro F G r C₁ C₂ ⟨a, sa, fa, ⟨f, hf, hF⟩, hsa, hna⟩ ⟨b, sb, fb, ⟨g, hg, hG⟩, hsb, hnb⟩
    refine ⟨Gen.mul a b, .mul sa sb, .mul fa fb, ⟨GenSort.mul .fam f g, .mul hf hg, fun q => ?_⟩,
      Or.inr ⟨hsa, hsb⟩, fun t ht mres hm => ?_⟩
    · show F q * G q = f q.1.1 q.1.2 * g q.1.1 q.1.2
      rw [hF q, hG q]
    · rw [genNorm_mul_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), ENNReal.coe_mul]
      exact mul_le_mul' (hna t ht mres hm) (hnb t ht mres hm)

/-- **Sized covariant jets on an open neighbourhood.** -/
theorem jetRepGQ_covariant_on (hX : X.Ok) (hζ : IsFastProfile D.ζ) {σ : ℝ≥0}
    (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * X.Δ) ≤ σ) :
    ∀ (n : ℕ) {g : W → Vec 2 → ℝ} {c : Gen .fam i p} {fc : GenSort.Sem .fam}
      {U : W → Set (Vec 2)} {r : ℕ} {C : ℝ≥0},
      (∀ q, IsOpen (U q)) → (∀ q, (0 : Vec 2) ∈ U q) →
      Gen.IsScheduled D c → Gen.FromSeed 𝒮 c → Gen.Denotes D bw j₀ c fc →
      Gen.SolvedFree X.leaf c →
      (∀ t ∈ X.T, ∀ mres, mres + r * X.Δ ≤ X.μ₀ →
        genNorm D X.κ X.Δ X.a₀ X.leaf c X.a₀ mres 0 t ≤ C) →
      (∀ (q : W), ∀ w ∈ U q, g q w = fc q.1.1 (q.1.2.recenter D w)) →
      JetRepGQ (famAlgQ D bw j₀ 𝒮 i p W X) σ n g r C := by
  intro n
  induction n with
  | zero =>
    intro g c fc U r C _ h0 hs hf hd hsf hn hg
    exact ⟨c, hs, hf, ⟨fc, hd, fun q => by
      show g q 0 = fc q.1.1 q.1.2
      rw [hg q 0 (h0 q), recenter_zero D hζ]⟩, hsf, hn⟩
  | succ n ih =>
    intro g c fc U r C hU h0 hs hf hd hsf hn hg
    refine ⟨⟨c, hs, hf, ⟨fc, hd, fun q => by
      show g q 0 = fc q.1.1 q.1.2
      rw [hg q 0 (h0 q), recenter_zero D hζ]⟩, hsf, hn⟩, fun j => ?_⟩
    refine ih (c := Gen.dSlowFam j c) (U := U) hU h0 (.dSlowFam j hs) (.dSlowFam j hf)
      (.dSlowFam j hd) (Or.inr hsf) (fun t ht mres hm => ?_) fun q w hw => ?_
    · rw [genNorm_dSlowFam_eq _ _ _ _ _ j (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx)]
      have hrΔ : 0 ≤ (r : ℝ) * X.Δ := mul_nonneg (Nat.cast_nonneg r) hX.hΔ
      have hm' : mres + X.Δ + (r : ℝ) * X.Δ ≤ X.μ₀ := by
        have e : ((r + 1 : ℕ) : ℝ) * X.Δ = X.Δ + (r : ℝ) * X.Δ := by push_cast; ring
        rw [e] at hm
        linarith
      have h2 : mres + X.Δ ≤ 2 := by linarith [hX.hμ]
      simp only [h2, ↓reduceIte]
      rw [ENNReal.coe_mul]
      exact mul_le_mul' hσ (hn t ht (mres + X.Δ) hm')
    · have hev : g q =ᶠ[nhds w] fun w' => fc q.1.1 (q.1.2.recenter D w') := by
        filter_upwards [(hU q).mem_nhds hw] with w' hw'
        exact hg q w' hw'
      simp only [dLabelG]
      rw [hev.fderiv_eq]
      have e2 : (fun h => fc q.1.1 ((q.1.2.recenter D w).recenter D h)) =
          fun h => (fun w' => fc q.1.1 (q.1.2.recenter D w')) (w + h) := by
        funext h; rw [recenter_recenter D hζ]
      show fderiv ℝ (fun w' => fc q.1.1 (q.1.2.recenter D w')) w (basisVec j) =
        fderiv ℝ (fun h => fc q.1.1 ((q.1.2.recenter D w).recenter D h)) 0 (basisVec j)
      rw [e2]
      set F : Vec 2 → ℝ := fun w' => fc q.1.1 (q.1.2.recenter D w')
      show fderiv ℝ F w _ = fderiv ℝ (fun h => F (w + h)) 0 _
      rw [fderiv_comp_add_left, add_zero]

/-! ### The chart leaves -/

/-- **A family letter at the recentered family has sized jets of size `K_g`.** -/
theorem jetRepGQ_famLetter (hX : X.Ok) (hζ : IsFastProfile D.ζ) {σ : ℝ≥0}
    (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * X.Δ) ≤ σ) (L : GeoLetter) (n : ℕ) :
    JetRepGQ (famAlgQ D bw j₀ 𝒮 i p W X) σ n
      (fun (q : W) w => L.evalAt D (q.1.2.recenter D w) q.1.1) 0 X.Kg := by
  obtain ⟨hs, hf, f, hd, hv⟩ := famLetter_rep (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮)
    (i := i) (p := p) L
  refine jetRepGQ_covariant_on hX hζ hσ n (U := fun _ => Set.univ) (fun _ => isOpen_univ)
    (fun _ => Set.mem_univ _) hs hf hd (Or.inr (Or.inr trivial)) (fun t _ mres _ => ?_)
    (fun q w _ => (hv _ _).symm)
  show genNorm D X.κ X.Δ X.a₀ X.leaf (Gen.mean (Gen.restrict (Gen.geo .own L))) X.a₀ mres 0 t ≤ _
  rw [genNorm_mean_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
    genNorm_restrict_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx),
    genNorm_geo_eq _ _ _ _ _ .own L (hX.hgeo _ _ _)]
  exact (le_iSup₂ (f := fun fr Lt => wsum X.a₀ 0 (X.κ.geo fr Lt)) GenFrame.own L).trans
    (hX.hKg 0 (Nat.zero_le _))

/-- **The first derivatives of the centered map** have sized jets of size `K_g`. -/
theorem jetRepGQ_dLabel_famMap (hX : X.Ok) (hζ : IsFastProfile D.ζ) {σ : ℝ≥0}
    (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * X.Δ) ≤ σ)
    (hW : ∀ q ∈ W, q.2.WellSlotted) (n : ℕ) (b j : Fin 2) :
    JetRepGQ (famAlgQ D bw j₀ 𝒮 i p W X) σ n
      (dLabelG j (fun (q : W) y => q.1.2.famMap D q.1.1 y b)) 0 X.Kg := by
  refine (jetRepGQ_famLetter (𝒮 := 𝒮) (bw := bw) (j₀ := j₀) (i := i) (p := p) (W := W) hX hζ hσ
    (.jac b j) n).congr_germ fun q => Filter.Eventually.of_forall fun w => ?_
  simp only [dLabelG]
  rw [dLabel_famMap hζ q.1.2 (hW q.1 q.2) q.1.1 b j w]
  rfl

/-- **The inverse Jacobian of the centered map** has sized jets of size `K_g`. -/
theorem jetRepGQ_jacInv_famMap (hX : X.Ok) (hζ : IsFastProfile D.ζ) {σ : ℝ≥0}
    (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * X.Δ) ≤ σ)
    (hW : ∀ q ∈ W, q.2.WellSlotted) (n : ℕ) (c k : Fin 2) :
    JetRepGQ (famAlgQ D bw j₀ 𝒮 i p W X) σ n
      (fun (q : W) x => ((jacMatrix (q.1.2.famMap D q.1.1) x)⁻¹) c k) 0 X.Kg := by
  refine (jetRepGQ_famLetter (𝒮 := 𝒮) (bw := bw) (j₀ := j₀) (i := i) (p := p) (W := W) hX hζ hσ
    (.jacInv c k) n).congr_germ fun q => Filter.Eventually.of_forall fun w => ?_
  show GeoLetter.evalAt D (q.1.2.recenter D w) q.1.1 (GeoLetter.jacInv c k) =
    (jacMatrix (q.1.2.famMap D q.1.1) w)⁻¹ c k
  rw [jacMatrix_famMap hζ q.1.2 (hW q.1 q.2) q.1.1 w]
  rfl

/-- The constants of the jets of the inverse centered map. -/
def invP (K : ℝ≥0) : ℕ → ℝ≥0
  | 0 => K
  | n + 1 => compC (invP K n) (n + 1) * K

/-- **The first derivatives of the inverse centered map** have sized jets. -/
theorem jetRepGQ_dLabel_famMapInv (hX : X.Ok) (hζ : IsFastProfile D.ζ) {σ : ℝ≥0}
    (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * X.Δ) ≤ σ)
    (hW : ∀ q ∈ W, q.2.WellSlotted) :
    ∀ (n : ℕ) (b j : Fin 2), JetRepGQ (famAlgQ D bw j₀ 𝒮 i p W X) σ n
      (dLabelG j (fun (q : W) x => q.1.2.famMapInv D q.1.1 x b)) 0 (invP X.Kg n) := by
  have hR := repAlgQ_famAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (p := p) (W := W) hX
  have heq : ∀ b j, dLabelG j (fun (q : W) x => q.1.2.famMapInv D q.1.1 x b) =
      fun (q : W) x => (fun (q : W) w => ((q.1.2.recenter D w).famJac D q.1.1)⁻¹ b j) q
        (q.1.2.famMapInv D q.1.1 x) := by
    intro b j
    funext q x
    simp only [dLabelG]
    exact dLabel_famMapInv hζ q.1.2 (hW q.1 q.2) q.1.1 b j x
  have hG : ∀ n b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 i p W X) σ n
      (fun (q : W) w => ((q.1.2.recenter D w).famJac D q.1.1)⁻¹ b j) 0 X.Kg := fun n b j =>
    jetRepGQ_famLetter hX hζ hσ (.jacInv b j) n
  intro n
  induction n with
  | zero =>
    intro b j
    rw [heq b j]
    have e : (fun q : W => (fun (q : W) w => ((q.1.2.recenter D w).famJac D q.1.1)⁻¹ b j) q
        (q.1.2.famMapInv D q.1.1 0)) =
        fun q : W => (fun (q : W) w => ((q.1.2.recenter D w).famJac D q.1.1)⁻¹ b j) q 0 :=
      funext fun q => by rw [famMapInv_zero hζ]
    show famAlgQ D bw j₀ 𝒮 i p W X _ 0 (invP X.Kg 0)
    rw [e]
    exact (hG 0 b j).value
  | succ n ih =>
    intro b j
    rw [heq b j]
    exact JetRepGQ.comp' hR (fun q => famMapInv_zero hζ q.1.2 q.1.1)
      (fun q => (contDiff_famJacInv hζ q.1.2 (hW q.1 q.2) q.1.1 b j).of_le
        (by exact_mod_cast le_top))
      (fun q => (contDiff_famMapInv q.1.2 q.1.1).of_le (by exact_mod_cast le_top))
      (hG (n + 1) b j)
      (fun b' j' => (ih b' j').mono hR le_rfl (Nat.zero_le _) le_rfl)

/-! ### Time letters -/

/-- A time letter is a sized family function with the size of its values. -/
theorem famAlgQ_time (hX : X.Ok) (Lt : TimeLetter)
    (hs : Gen.IsScheduled D (Gen.time (s := .fam) (i := i) (p := p) Lt)) {C : ℝ≥0}
    (hC : ∀ t ∈ X.T, |Lt.eval D t| ≤ C) :
    famAlgQ D bw j₀ 𝒮 i p W X (fun q : W => Lt.eval D q.1.1) 0 C :=
  ⟨Gen.time Lt, hs, .time _, ⟨_, .time _, fun _ => rfl⟩, trivial, fun t ht mres _ => by
    rw [genNorm_time_eq _ _ _ _ _ Lt (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hC t ht)⟩

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory Set
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem.LiftGenSetup

/-! **Ledger, sized jets of the path mean array.** The quantitative form of
`LiftGenSetup.jetRep_pmArr'`: the entry of order `j` of the path mean array `pmArr` of cell degree
`n` is a covariant label function, the family denotation of `C_j · ⟨f⟩` with the graded
slow-flux array `fluxXArr` (`URepArrP.fluxXArr`); its jets cost the reserve `(n - 1) - j` plus
one step per label derivative, and have the size `|C_j| · fluxXc · pathW Θ h` times `σ` per
derivative (`jetRepGQ_pmArr`). As an array of the length scale `w = ρ`, its constant is
`pmC · fluxXc · pathW Θ h` with `pmC = ℓ_m⁻² (d_*/ρ)^n ρ` (`arrJetGQ_pmArr`). -/

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

/-- The dimensional prefactor of the path mean array of cell degree `n`. -/
def pmC (D : OCData) (m : ℕ) (ρ : ℝ) (n : ℕ) : ℝ :=
  (D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ

/-- **Sized covariant jets of the path mean array.** -/
theorem jetRepGQ_pmArr (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {X : GCtx} (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ}
    (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    {σ : ℝ≥0} (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ) ≤ σ)
    (κ : Fin 2) (j : ℕ) (α : DerivativeWord2 j) (r' : ℕ) :
    JetRepGQ (famAlgQ D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁) X) σ r'
      (fun (q : liftFamW D m 𝒜 t₀ t₁) y =>
        pmArr D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 κ j α y 0)
      (n - 1 - j)
      (Real.toNNReal |-((D.cellScaleSq m)⁻¹ *
          (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) * ρ ^ j| *
        (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0)) := by
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hV
  have hok : V.Ok := hS.ok
  have hbelow : V.CoeffRepBelowP X Dm Cc (pathW Θ) (liftB X Dm) h n :=
    fun hh' k' h1 _ m'' α' v' u' =>
      hS.coeffRepP hX hSl hη0 hη1 hed hL₀ (h1.trans hhH) k' m'' α' v' u'
  have hrep := UEnv.URepArrP.fluxXArr hX hok hSl (fun A => familyLiftData D m k A ρ (edge A)) Cc
    0 hn1 (η := D.kap m / D.kap (m - 1)) (fun _ _ => rfl) hη0 hη1 (hS.metric_repP hX)
    (hS.drift_repP hX) hed (fun hh v w hh1 => pathW_succ Θ hh v w hh1) hbelow
    (fun l hl => hregn l.1 hl.1 l.2 hl.2) (Fin.last h) κ
  obtain ⟨e, ⟨hs, hf, f, hd, hv, -⟩, hsf, hn⟩ := hrep j α
  set C := -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
    ρ ^ j with hC
  refine jetRepGQ_covariant_on hX hS.hζ hσ r'
    (c := Gen.mul (Gen.time (s := .fam) (i := m) (p := k) (.const C)) (Gen.mean e))
    (fc := GenSort.mul .fam (GenSort.ofTime .fam (TimeLetter.eval D (.const C))) (cellMeanSem f))
    (U := fun q => {w | ρ⁻¹ • w ∈ U q.1.2})
    (fun q => (hS.hU q.1.2 q.2.1).preimage (continuous_const_smul _))
    (fun q => by simpa using h0 q.1.2 q.2.1)
    (.mul (.timeConst C) (.mean hs)) (.mul (.time _) (.mean hf)) (.mul (.time _) (.mean hd))
    (Or.inr ⟨trivial, Or.inr hsf⟩) (fun t ht mres hm => ?_) fun q w hw => ?_
  · rw [genNorm_mul_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
      genNorm_const_eq _ _ _ _ _ C (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), ENNReal.coe_mul]
    have hmean := genNorm_mean_eq D X.κ X.Δ X.a₀ X.leaf (w := e)
      (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx) X.a₀ mres 0 t
    exact mul_le_mul' le_rfl (hmean.le.trans (hn t ht mres 0 hm (by omega)))
  · obtain ⟨⟨t, A⟩, hq⟩ := q
    have hl : ((A, (D.cellScaleSq m)⁻¹ * t) : RealChain × ℝ) ∈ V.W := ⟨hq.1, hq.2⟩
    have htime : D.cellScaleSq m * ((D.cellScaleSq m)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ hS.hc.ne', one_mul]
    have hval : ∀ z, GenSem.fluxXArr (familyLiftData D m k A ρ (edge A)) (Cc A) 0 h n
        ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ j α (ρ⁻¹ • w) z = f t (A.recenter D w) z := by
      intro z
      have := hv _ hl _ hw z
      simp only [hV, liftEnv] at this
      rw [this, htime, smul_smul, mul_inv_cancel₀ hS.hρ, one_smul]
    simp only [pmArr, hval]
    rfl

/-- **The path mean array is a sized array** of the length scale `ρ`, with the constant
`pmC · fluxXc · pathW Θ h`. -/
theorem arrJetGQ_pmArr (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {X : GCtx} (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ}
    (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    {σ : ℝ≥0} (hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ) ≤ σ) (hρ : 0 < ρ)
    (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) (r' : ℕ)
    (hregR : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (r' + Dm + 2)) (κ : Fin 2) :
    ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁) X) σ (Real.toNNReal ρ) r'
      (fun q : liftFamW D m 𝒜 t₀ t₁ =>
        pmArr D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 κ) (n - 1)
      (Real.toNNReal (pmC D m ρ n) *
        (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0)) := by
  have hR := repAlgQ_famAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := m) (p := k)
    (W := liftFamW D m 𝒜 t₀ t₁) hX
  have hc0 : 0 ≤ pmC D m ρ n := by
    unfold pmC
    have := hS.hc
    positivity
  intro j α
  refine ⟨(hS.jetRepGQ_pmArr hX hSl hη0 hη1 hed hL₀ h0 hhH hn1 hLn hregn hσ κ j α r').mono hR
    le_rfl (Nat.sub_le _ _) (le_of_eq ?_), fun q =>
    contDiff_pmArr D m ρ _ _ n q.1.1 κ (hregR q.1.2 q.2.1 _ q.2.2) j α⟩
  have e : -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
      ρ ^ j = -(pmC D m ρ n * ρ ^ j) := by
    unfold pmC
    ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg hc0 (pow_nonneg hρ.le _)),
    Real.toNNReal_mul hc0, Real.toNNReal_pow hρ.le]
  ring

end AVRegularity.Providers.GenSem.LiftGenSetup
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Set
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem

/-! **Ledger: the covariance letter is a graded family function.** The quantitative form of
`LiftGenSetup.covLetter_famRep` and `CutoffLiftSetup.slotFamRep_covLetter`: every coefficient of
tested order `d` of the covariance letter `𝖵_{n,h,a,a'}` is a sized family function with
* the reserve cost `covLetR n a a'` (a number of reserve steps depending only on `n, a, a'`);
* the size `covLetK · c_H^{a+a'} · (pmC · fluxXc · pathW Θ h) · ρ^{d-1}`: the size of the path mean
  of cell degree `n` at the order `d` (`|c_{n,d}|(d-1)! = pmC ρ^{d-1}`), times one factor
  `c_H ≥ |𝖧_m|/ρ²` for each covariance operator, times a constant `covLetK` depending only on
  `n, a, a'` and on the constants `S, K_g` of the graded context
  (the price of the mean multiplied by `(‖H_cov‖/r²)^{a+a'}(r/E)^l`).

The array chain of `covLetterFlux_applyArr` carries sized jets over the sized family algebra on
`liftFamW`: the path mean arrays (`arrJetGQ_pmArr`), the push and pull by the chart pair
(`arrJetGQ_push`, `arrJetGQ_pull` with the chart leaves), the covariance arrays
(`arrJetGQ_covArrPow` with the time letters `covPrimitive`) and the compositions
(`arrJetGQ_compArr`). One label derivative costs `σ = S/ρ`. -/

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

/-- The reserve cost of the covariance letter. -/
def covLetR (n a a' : ℕ) : ℕ :=
  n - 1 + n + 2 * a' + n + 2 * a + 2 * a + (2 * a + (n + 2 * a'))

/-- The constant of the covariance letter. -/
def covLetK (n a a' : ℕ) (s Kg : ℝ≥0) : ℝ≥0 :=
  chartK 0 (2 * a + (n + 2 * a')) Kg
      (s + 2 ^ (2 * a + (n + 2 * a')) * invP Kg (2 * a + (n + 2 * a'))) *
    (Kg * (Real.toNNReal |((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a)| *
      (compK (2 * a) 0 s * (covK a 0 s * (compK n (2 * a) s *
        (chartK (2 * a) n (invP Kg (2 * a)) (s + 2 ^ (2 * a + n) * Kg) *
          (compC (invP Kg (2 * a)) (2 * a) * Kg) * covK a' (2 * a + n) s))))))

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

namespace LiftGenSetup

/-- **The coefficients of the covariance letter are sized family functions** over the lift
window. -/
theorem covLetter_famRepQ (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {X : GCtx} (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ}
    (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (a a' : ℕ) {s₀ : ℝ} (hs₀ : s₀ = 0) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1))
    (hreg2 : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (2 * a + Dm + 2))
    (hρ : 0 < ρ) (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) {cH : ℝ≥0}
    (hH : ∀ t ∈ X.T, ∀ i j, |covMat D m s₀ t i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    famAlgQ D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁) X (fun q =>
      fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2)
        n a a' q.1.1 q.1.2) d I 0 c) (covLetR n a a')
      (covLetK n a a' X.S X.Kg * (cH ^ (a + a') * (Real.toNNReal (pmC D m ρ n) *
        (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0))) *
        Real.toNNReal ρ ^ (d - 1)) := by
  set W := liftFamW D m 𝒜 t₀ t₁ with hWdef
  have hR := repAlgQ_famAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := m) (p := k) (W := W) hX
  have hWS : ∀ q ∈ W, q.2.WellSlotted := fun q hq => (hS.hA q.2 hq.1).1
  -- the length scale and the cost of one label derivative
  set w : ℝ≥0 := Real.toNNReal ρ with hwdef
  have hw : w ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  set σ : ℝ≥0 := X.S * w⁻¹ with hσdef
  have hσw : σ * w ≤ X.S := by
    rw [hσdef, mul_assoc, inv_mul_cancel₀ hw, mul_one]
  have hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ) ≤ σ := by
    have h1 : (w : ℝ≥0∞) * (X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ)) ≤ X.S := by
      have e : ENNReal.ofReal |ρ| = (w : ℝ≥0∞) := by
        rw [abs_of_pos hρ]
        rfl
      rw [← e]
      exact hSl
    have h2 : (σ : ℝ≥0∞) = (X.S : ℝ≥0∞) / (w : ℝ≥0∞) := by
      rw [hσdef, ENNReal.coe_mul, ENNReal.coe_inv hw, div_eq_mul_inv]
    rw [h2, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hw)) (Or.inl ENNReal.coe_ne_top),
      mul_comm]
    exact h1
  set K := 2 * a + (n + 2 * a') with hK
  set K' := max K (d - 1) with hK'
  set cE : ℝ≥0 := Real.toNNReal (pmC D m ρ n) *
    (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0) with hcE
  -- the leaves
  have hP : ∀ κ, ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w (2 * a) (fun q : W =>
      pmArr D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 κ) (n - 1) cE :=
    fun κ => hS.arrJetGQ_pmArr hX hSl hη0 hη1 hed hL₀ h0 hhH hn1 hLn hregn hσ hρ hD0 (2 * a)
      hreg2 κ
  have hHr : ∀ i j, famAlgQ D bw j₀ 𝒮 m k W X (fun q : W => covMat D m s₀ q.1.1 i j) 0
      (cH * w ^ 2) := by
    intro i j
    have e : (fun q : W => covMat D m s₀ q.1.1 i j) =
        fun q : W => (TimeLetter.covPrimitive m 0 i j).eval D q.1.1 := funext fun q => by
      simp only [covMat, TimeLetter.eval, hs₀, hκ, hκ']
    rw [e]
    refine famAlgQ_time hX (.covPrimitive m 0 i j) (.timeCov m i j) fun t ht => ?_
    have := hH t ht i j
    simpa only [covMat, TimeLetter.eval, hs₀, hκ, hκ'] using this
  have hΨ : ∀ n' r' b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ n'
      (dLabelG j (fun (q : W) y => q.1.2.famMap D q.1.1 y b)) r' X.Kg := fun n' r' b j =>
    (jetRepGQ_dLabel_famMap hX hS.hζ hσ hWS n' b j).mono hR le_rfl (Nat.zero_le _) le_rfl
  have hI : ∀ n' r' b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ n'
      (dLabelG j (fun (q : W) x => q.1.2.famMapInv D q.1.1 x b)) r' (invP X.Kg n') :=
    fun n' r' b j =>
      (jetRepGQ_dLabel_famMapInv hX hS.hζ hσ hWS n' b j).mono hR le_rfl (Nat.zero_le _) le_rfl
  -- the push-forward
  have hB1 : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w (2 * a) (fun q : W =>
      covB1 D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 q.1.2 c')
      (n - 1 + n)
      (chartK (2 * a) n (invP X.Kg (2 * a)) (X.S + 2 ^ (2 * a + n) * X.Kg) *
        (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE)) := fun c' =>
    arrJetGQ_push hR hw hσw (fun q : W => contDiff_famMap q.1.2 q.1.1)
      (hΨ (2 * a + n) (n - 1)) le_rfl (fun q : W => contDiff_famMapInv q.1.2 q.1.1)
      (fun q : W => famMapInv_zero hS.hζ q.1.2 q.1.1) (hI (2 * a) (n - 1)) hP c'
  -- composition with the inner covariance operators
  have hB2 : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w (0 + 2 * a) (fun q : W =>
      covB2 D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a' q.1.1 q.1.2 c')
      (n - 1 + n + 2 * a' + n)
      (compK n (2 * a) X.S * (chartK (2 * a) n (invP X.Kg (2 * a))
          (X.S + 2 ^ (2 * a + n) * X.Kg) * (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE) *
        (covK a' (2 * a + n) X.S * cH ^ a'))) := fun c' => by
    rw [zero_add]
    exact arrJetGQ_compArr hR hw hσw n
      (ArrJetGQ.mono hR le_rfl (hB1 c') (Nat.le_add_right _ _) le_rfl)
      (ArrJetGQ.mono hR le_rfl
        (arrJetGQ_covArrPow hR hw hσw (H := fun q : W => covMat D m s₀ q.1.1) hHr a' (2 * a + n))
        (by omega) le_rfl)
  -- composition with the outer covariance operators
  have hB4 : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w 0 (fun q : W =>
      covB4 D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 c')
      (n - 1 + n + 2 * a' + n + 2 * a + 2 * a)
      (Real.toNNReal |((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a)| *
        (compK (2 * a) 0 X.S * (covK a 0 X.S * cH ^ a *
          (compK n (2 * a) X.S * (chartK (2 * a) n (invP X.Kg (2 * a))
              (X.S + 2 ^ (2 * a + n) * X.Kg) * (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE) *
            (covK a' (2 * a + n) X.S * cH ^ a')))))) := fun c' =>
    arrJetGQ_smul hR _ (arrJetGQ_compArr hR hw hσw (2 * a)
      (ArrJetGQ.mono hR le_rfl
        (arrJetGQ_covArrPow hR hw hσw (H := fun q : W => covMat D m s₀ q.1.1) hHr a 0)
        (by omega) le_rfl)
      (ArrJetGQ.mono hR le_rfl (hB2 c') (Nat.le_add_right _ _) le_rfl))
  -- the pull-back
  have e : ∀ (q : W) (x : Vec 2) (c k : Fin 2),
      (jacMatrix (q.1.2.famMap D q.1.1) x)⁻¹ c k = ((q.1.2.recenter D x).famJac D q.1.1)⁻¹ c k :=
    fun q x c k => by rw [jacMatrix_famMap hS.hζ q.1.2 (hWS q.1 q.2) q.1.1 x]
  have hF : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w 0 (fun q : W => covFin D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 c')
      (n - 1 + n + 2 * a' + n + 2 * a + 2 * a + K)
      (chartK 0 K X.Kg (X.S + 2 ^ K * invP X.Kg K) *
        (X.Kg * (Real.toNNReal |((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a)| *
          (compK (2 * a) 0 X.S * (covK a 0 X.S * cH ^ a *
            (compK n (2 * a) X.S * (chartK (2 * a) n (invP X.Kg (2 * a))
                (X.S + 2 ^ (2 * a + n) * X.Kg) * (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE) *
              (covK a' (2 * a + n) X.S * cH ^ a')))))))) := fun c' =>
    arrJetGQ_pull hR hw hσw (fun q : W => famMap_zero q.1.2 q.1.1)
      (fun q : W => (contDiff_famMap q.1.2 q.1.1).of_le (by exact_mod_cast le_top))
      (hΨ 0 _) (fun q : W => contDiff_famMapInv q.1.2 q.1.1)
      (fun b j => by rw [Nat.zero_add]; exact hI K _ b j)
      (by rw [Nat.zero_add])
      (fun c k => (jetRepGQ_jacInv_famMap hX hS.hζ hσ hWS 0 c k).mono hR le_rfl
        (Nat.zero_le _) le_rfl)
      (fun c k q => by
        simp_rw [e]
        exact (contDiff_famJacInv hS.hζ q.1.2 (hWS q.1 q.2) q.1.1 c k).of_le
          (by exact_mod_cast le_top))
      hB4 c'
  -- the value at the label `0`
  have hval := rep_fluxCoeff_applyArrQ hR (K := K') (A := fun q : W => covFin D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2) d I
    (le_max_right _ _) c (fun m' α => (hF c m' α).1.value)
  -- the identity of the letter with its array operator
  have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) :=
    (contDiff_mono (0 : Vec 2) I).of_le le_top
  have key : (fun q : W => fluxCoeff (covLetterFlux D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2) d I 0 c) =
      fun q : W => fluxCoeff (fun g y κ => applyArr K' (covFin D m ρ s₀
        (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 κ) g y 0)
        d I 0 c := by
    funext q
    have hreg : LiftRegular (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) 0
        ((D.cellScaleSq m)⁻¹ * q.1.1) h n (2 * a + Dm + 2) := hreg2 q.1.2 q.2.1 _ q.2.2
    have hvec : covLetterFlux D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2)
        n a a' q.1.1 q.1.2 (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 =
        fun c' => applyArr K' (covFin D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2))
          (Cc q.1.2) n a a' q.1.1 q.1.2 c') (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 := by
      refine funext fun c' => ?_
      rw [covLetterFlux_applyArr hS.hζ hS.hρ q.1.2 hreg hmono 0 c',
        applyArr_eq_of_supp (le_max_left K (d - 1)) (arrSupp_covFin _ _ _ _ _ _ _ _ _ _ _ c')]
    unfold fluxCoeff
    rw [hvec]
  rw [key]
  refine hR.mono hval (le_of_eq ?_) (le_of_eq ?_)
  · simp only [covLetR, hK]
  · simp only [covLetK, hK]
    rw [pow_add]
    ring

end LiftGenSetup

variable {b : ℝ} {R : ℕ}

/-- **The covariance letters are graded slot family functions** (cascade anchor `0`, cascade
diffusivities, reserve `2a + Dm + 2 ≤ R`). -/
theorem CutoffLiftSetup.slotFamRep_covLetterP
    (hset : CutoffLiftSetup D b j₀ 𝒮 m k ρ edge Cc sX sZ N R) (hζ : IsFastProfile D.ζ)
    (hc : 0 < D.cellScaleSq m) {X : GCtx} (hX : X.Ok)
    (hSl : ENNReal.ofReal |ρ| * (X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ)) ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ U : RealChain → Set (Vec 2),
      (∀ A, IsAdmissibleChain D b j₀ m k A → U A ⊆ ladderOmega D b j₀ m k A ρ) →
      ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
        (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
          (D.slotStart m k / D.cellScaleSq m)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP X
          (fun l Y z => (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
            fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm h N ≤ X.L₀) {n : ℕ} (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hnR : n + Dm + 2 ≤ R) (a a' : ℕ) (ha : 2 * a + Dm + 2 ≤ R) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1)) (hρ : 0 < ρ)
    (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) {cH : ℝ≥0}
    (hH : ∀ t ∈ X.T, ∀ i j, |covMat D m 0 t i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    SlotFamRepP D b j₀ 𝒮 m k X (fun t A =>
      fluxCoeff (covLetterFlux D m ρ 0 (familyLiftData D m k A ρ (edge A)) (Cc A) n a a' t A)
        d I 0 κ) (covLetR n a a')
      (covLetK n a a' X.S X.Kg * (cH ^ (a + a') *
        (Real.toNNReal (LiftGenSetup.pmC D m ρ n) *
          (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0))) *
        Real.toNNReal ρ ^ (d - 1)) := by
  obtain ⟨edge', Cc', U, hS, hU⟩ := hset
  have hed' : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP X
        (fun l Y z => (((familyLiftData D m k l.1 ρ (edge' l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u) := fun v u d α c =>
    (hed U (fun A hA => (hU A hA).2.2.1) v u d α c).congr fun l hl Y hY z =>
      (Uniqueness.list_sum_map_forall₂ ((hU l.1 hl.1).2.2.2.1.edge v u d) fun γ γ' hγ => by
        rw [hγ.1, hγ.2 α l.2 Y hY z]).symm
  obtain ⟨e, hs, hf, ⟨fc, hd, hv⟩, hsf, hn⟩ := hS.covLetter_famRepQ hX hSl hη0 hη1 hed' hL₀
    (fun A hA => (hU A hA).2.1) le_rfl hn1 hLn
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ hnR τ hτ 0) a a' rfl hκ hκ'
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ ha τ hτ 0) hρ hD0 hH d I κ
  refine ⟨e, hs, hf, ⟨fc, hd, fun A hA t ht => ?_⟩, hsf, hn⟩
  have hq : ((t, A) : ℝ × RealChain) ∈ liftFamW D m {A | IsAdmissibleChain D b j₀ m k A}
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
    refine ⟨hA, ?_, ?_⟩
    · show D.slotStart m k / D.cellScaleSq m ≤ (D.cellScaleSq m)⁻¹ * t
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht.1 (inv_nonneg.mpr hc.le)
    · show (D.cellScaleSq m)⁻¹ * t ≤ _
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hc.le)
  have h1 := hv ⟨(t, A), hq⟩
  obtain ⟨hO, h0, -, hag, hCeq, -⟩ := hU A hA
  rw [← h1]
  show fluxCoeff (covLetterFlux D m ρ 0 (familyLiftData D m k A ρ (edge' A)) (Cc' A) n a a' t A)
    d I 0 κ =
    fluxCoeff (covLetterFlux D m ρ 0 (familyLiftData D m k A ρ (edge A)) (Cc A) n a a' t A)
      d I 0 κ
  rw [fluxCoeff_covLetterFlux_agree D m ρ 0 hag (Cc A) (Cc' A) n a a' t A hO h0
    ⟨(contDiff_famMapInv A t).continuous.continuousAt, famMapInv_zero hζ A t⟩
    (fun hh' _ n' m' α X hX => (hCeq hh' n' m' α _ X hX).symm) d I]

end AVRegularity.Providers.GenSem
end
end
end
