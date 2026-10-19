-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.ChainMetric
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer
public import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.GenSem.Jet.Chart
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.CycleReference.SingleModeFlux
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
section
/-! **Torus law of the construction: the geometry of a chain with a shifted base label.** The
renewal flows are lifts of torus maps (`native_flow_latticeShift`) and the pulse shears are
`ε_k ℤ²`-periodic with `ε_k⁻¹ ∈ ℕ` (`ocShearVel_add_latticeShift`), so the relative
displacements do not see a lattice shift of their phase (`relDisp_add_latticeShift`). Hence the
offset flow of every family is ℤ²-equivariant and the geometry of a chain with base label shifted
by `n ∈ ℤ²` is the translate of the geometry by `n` (`geom_shiftBase`, structure `GeomShift`).
The centered maps, their inverses, Jacobians, metrics and strains do not change; recentering and
appending children commute with the shift (`recenter_shiftBase`, `appendChild_shiftBase`); and the
context strain does not change (`contextStrain_shiftBase`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.Torus

/-! ### Periodicity of the pulse shears and of the relative displacements -/

/-- **The pulse shear velocity is ℤ²-periodic.** -/
theorem ocShearVel_add_latticeShift (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) (n : Fin 2 → ℤ) :
    ocShearVel α q Λ m k (y + latticeShift n) = ocShearVel α q Λ m k y := by
  obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast q Λ m
  have hcos : ∀ (a : ℝ) (i : Fin 2), Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
      (y i + (n i : ℝ))) = Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y i) := by
    intro _ i
    rw [hJ, show 2 * Real.pi * (J : ℝ) * (y i + (n i : ℝ)) =
      2 * Real.pi * (J : ℝ) * y i + ((J * n i : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_int_mul_two_pi _ _
  by_cases h1 : k % 4 = 1
  · rw [CycleReference.ocShearVel_horizontal h1, CycleReference.ocShearVel_horizontal h1]
    simp only [Pi.add_apply, latticeShift]
    rw [hcos 0 0]
  · by_cases h3 : k % 4 = 3
    · rw [CycleReference.ocShearVel_vertical h3, CycleReference.ocShearVel_vertical h3]
      simp only [Pi.add_apply, latticeShift]
      rw [hcos 0 1]
    · have h0 : ∀ z, ocShearVel α q Λ m k z = 0 := by
        intro z
        have hψ : ocShear α q Λ m k = fun _ => 0 := by
          funext w
          simp [ocShear, psi0, h1, h3]
        simp [ocShearVel, hψ, streamVel, spaceGrad]
      rw [h0, h0]

/-- **The relative displacement does not see a lattice shift of its phase.** -/
theorem relDisp_add_latticeShift (D : OCData) (k : ℕ) (pk : ℤ) (u s : ℝ) (θ : Vec 2)
    (n : Fin 2 → ℤ) :
    D.relDisp k pk u s (θ + (D.eps k)⁻¹ • latticeShift n) = D.relDisp k pk u s θ := by
  unfold OCData.relDisp
  by_cases hε : D.eps k = 0
  · simp [hε]
  · rw [smul_add, smul_inv_smul₀ hε]
    show (D.eps k)⁻¹ • ((∫ v in s..u, ocPulse D.α D.q D.Λ D.ζ k pk v) •
        ocShearVel D.α D.q D.Λ k pk (D.eps k • θ + latticeShift n)) = _
    rw [ocShearVel_add_latticeShift]

/-! ### Shifted geometries -/

/-- The flow of a geometry commutes with the lattice translations. -/
def GeomEquiv (g : ChainGeom) : Prop :=
  ∀ (n : Fin 2 → ℤ) (u : ℝ) (x : Vec 2) (r : ℝ), g.1 u (x + latticeShift n) r = g.1 u x r + latticeShift n

/-- The geometry `g'` is the translate of `g` by `L`. -/
structure GeomShift (g g' : ChainGeom) (L : Vec 2) : Prop where
  flow : ∀ (u : ℝ) (x : Vec 2) (r : ℝ), g'.1 u (x + L) r = g.1 u x r + L
  center : g'.2.1 = g.2.1 + L
  anchor : g'.2.2 = g.2.2

variable (D : OCData)

theorem childGeom_equiv (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild) {g : ChainGeom}
    (hg : GeomEquiv g) : GeomEquiv (D.childGeom k pk s' c g) := by
  intro n u x r
  simp only [OCData.childGeom]
  rw [hg n g.2.2 x r]
  have e : (D.eps k)⁻¹ • (g.1 g.2.2 x r + latticeShift n) +
      (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)) =
      ((D.eps k)⁻¹ • g.1 g.2.2 x r + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))) +
        (D.eps k)⁻¹ • latticeShift n := by
    rw [smul_add]; abel
  rw [e, relDisp_add_latticeShift, show g.1 g.2.2 x r + latticeShift n +
    D.eps k • D.relDisp k pk u r ((D.eps k)⁻¹ • g.1 g.2.2 x r +
      (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))) =
    (g.1 g.2.2 x r + D.eps k • D.relDisp k pk u r ((D.eps k)⁻¹ • g.1 g.2.2 x r +
      (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) + latticeShift n by abel, hg]

theorem childGeom_shift (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild) {g g' : ChainGeom}
    {n : Fin 2 → ℤ} (hs : GeomShift g g' (latticeShift n)) :
    GeomShift (D.childGeom k pk s' c g) (D.childGeom k pk s' c g') (latticeShift n) := by
  refine ⟨fun u x r => ?_, ?_, rfl⟩
  · simp only [OCData.childGeom]
    rw [hs.anchor, hs.flow, hs.center]
    have e : (D.eps k)⁻¹ • (g.1 g.2.2 x r + latticeShift n) +
        (c.phase - (D.eps k)⁻¹ • (g.2.1 + latticeShift n + c.center)) =
        (D.eps k)⁻¹ • g.1 g.2.2 x r + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)) := by
      rw [smul_add, smul_add, smul_add, smul_add]; abel
    rw [e, show g.1 g.2.2 x r + latticeShift n +
      D.eps k • D.relDisp k pk u r ((D.eps k)⁻¹ • g.1 g.2.2 x r +
        (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))) =
      (g.1 g.2.2 x r + D.eps k • D.relDisp k pk u r ((D.eps k)⁻¹ • g.1 g.2.2 x r +
        (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) + latticeShift n by abel, hs.flow]
  · simp only [OCData.childGeom]
    rw [hs.anchor, hs.center, show g.2.1 + latticeShift n + c.center =
      (g.2.1 + c.center) + latticeShift n by abel, hs.flow]

theorem geomAux_shift (n : Fin 2 → ℤ) : ∀ (k : ℕ) (sl : List ℤ) (cs : List ChainChild)
    (g g' : ChainGeom), GeomEquiv g → GeomShift g g' (latticeShift n) →
    GeomEquiv (D.geomAux k sl cs g) ∧
      GeomShift (D.geomAux k sl cs g) (D.geomAux k sl cs g') (latticeShift n)
  | k, pk :: pk1 :: rest, c :: cs, g, g', hg, hs => by
      simp only [OCData.geomAux]
      exact geomAux_shift n (k + 1) (pk1 :: rest) cs _ _ (childGeom_equiv D k pk _ c hg)
        (childGeom_shift D k pk _ c hs)
  | _, [], _, _, _, hg, hs => ⟨hg, hs⟩
  | _, [_], _, _, _, hg, hs => ⟨hg, hs⟩
  | _, _ :: _ :: _, [], _, _, hg, hs => ⟨hg, hs⟩

/-- **The geometry of a chain with a shifted base label is the translate of the geometry.** -/
theorem geom_shiftBase (ch : RealChain) (n : Fin 2 → ℤ) :
    GeomEquiv (ch.geom D) ∧ GeomShift (ch.geom D) ((ch.shiftBase n).geom D) (latticeShift n) :=
  geomAux_shift D n _ _ _ _ _
    (fun n' u x r => Construction.Preservation.FullLift.native_flow_latticeShift D _ u r n' x)
    ⟨fun u x r => Construction.Preservation.FullLift.native_flow_latticeShift D _ u r n x, rfl, rfl⟩

/-! ### The family objects of a shifted chain -/

variable (ch : RealChain) (n : Fin 2 → ℤ)

theorem famMap_shiftBase : (ch.shiftBase n).famMap D = ch.famMap D := by
  obtain ⟨-, hs⟩ := geom_shiftBase D ch n
  funext u h
  unfold RealChain.famMap
  rw [hs.center, hs.anchor, show (ch.geom D).2.1 + latticeShift n + h =
    ((ch.geom D).2.1 + h) + latticeShift n by abel, hs.flow, hs.flow]
  abel

theorem famMapInv_shiftBase : (ch.shiftBase n).famMapInv D = ch.famMapInv D := by
  obtain ⟨-, hs⟩ := geom_shiftBase D ch n
  funext u w
  unfold RealChain.famMapInv
  rw [hs.center, hs.anchor, hs.flow, show (ch.geom D).1 u (ch.geom D).2.1 (ch.geom D).2.2 +
    latticeShift n + w = ((ch.geom D).1 u (ch.geom D).2.1 (ch.geom D).2.2 + w) + latticeShift n
    by abel, hs.flow]
  abel

/-- The Jacobian of a translated map at the translated point. -/
theorem jacMatrix_translate {f g : Vec 2 → Vec 2} {L : Vec 2} (h : ∀ y, g (y + L) = f y + L)
    (x : Vec 2) : jacMatrix g (x + L) = jacMatrix f x := by
  have hg : g = fun y => f (y - L) + L := funext fun y => by
    rw [← h (y - L), sub_add_cancel]
  have hl : (fun y => f (y - L)) = fun y => f (-L + y) :=
    funext fun y => by rw [neg_add_eq_sub]
  rw [hg]
  unfold jacMatrix
  rw [fderiv_add_const, hl, fderiv_comp_add_left, show -L + (x + L) = x by abel]

theorem famJac_shiftBase : (ch.shiftBase n).famJac D = ch.famJac D := by
  obtain ⟨-, hs⟩ := geom_shiftBase D ch n
  funext u
  unfold RealChain.famJac
  rw [hs.center, hs.anchor]
  exact jacMatrix_translate (fun y => hs.flow u y _) _

theorem famMetric_shiftBase : (ch.shiftBase n).famMetric D = ch.famMetric D := by
  funext u
  simp only [RealChain.famMetric, famJac_shiftBase]

theorem famStrain_shiftBase : (ch.shiftBase n).famStrain D = ch.famStrain D := by
  funext u
  simp only [RealChain.famStrain, famJac_shiftBase]

theorem dropLastChild_shiftBase :
    (ch.shiftBase n).dropLastChild = ch.dropLastChild.shiftBase n := rfl

theorem appendChild_shiftBase (p' : ℤ) (t : ℝ) (ζ : Vec 2) :
    (ch.shiftBase n).appendChild D p' t ζ = (ch.appendChild D p' t ζ).shiftBase n := rfl

/-- **Recentering commutes with the shift of the base label.** -/
theorem recenter_shiftBase (h : Vec 2) :
    (ch.shiftBase n).recenter D h = (ch.recenter D h).shiftBase n := by
  unfold RealChain.recenter
  have hc : (ch.shiftBase n).children = ch.children := rfl
  rcases hlast : ch.children.getLast? with _ | c
  · simp only [hlast, RealChain.shiftBase]
    congr 1
    abel
  · simp only [hc, hlast]
    obtain ⟨-, hs⟩ := geom_shiftBase D ch.dropLastChild n
    rw [dropLastChild_shiftBase, hs.anchor, hs.center]
    have hlev : (ch.shiftBase n).lastLevel = ch.lastLevel := rfl
    have hslot : (ch.shiftBase n).slot = ch.slot := rfl
    rw [hlev, hslot, show (ch.dropLastChild.geom D).2.1 + latticeShift n + c.center =
      ((ch.dropLastChild.geom D).2.1 + c.center) + latticeShift n by abel, hs.flow,
      show (ch.dropLastChild.geom D).1 (D.slotAnchor (ch.lastLevel + 1) ch.slot)
        ((ch.dropLastChild.geom D).2.1 + c.center) (ch.dropLastChild.geom D).2.2 +
          latticeShift n + h =
        ((ch.dropLastChild.geom D).1 (D.slotAnchor (ch.lastLevel + 1) ch.slot)
          ((ch.dropLastChild.geom D).2.1 + c.center) (ch.dropLastChild.geom D).2.2 + h) +
          latticeShift n by abel, hs.flow]
    simp only [RealChain.shiftBase, add_sub_add_right_eq_sub]

theorem famJac_recenter_shiftBase (h : Vec 2) :
    ((ch.shiftBase n).recenter D h).famJac D = (ch.recenter D h).famJac D := by
  rw [recenter_shiftBase, famJac_shiftBase]

/-- **The context strain does not see the base label.** -/
theorem contextStrain_shiftBase (i : ℕ) (pc : ℤ) (t : ℝ) (ζ : Vec 2) :
    contextStrain D i pc t (ch.shiftBase n) ζ = contextStrain D i pc t ch ζ := by
  unfold contextStrain
  simp only [famStrain_shiftBase, famJac_shiftBase, famJac_recenter_shiftBase]

end AVRegularity.Providers.Torus
end
end

section
/-! **Torus law of the construction: the lifts of a chain with a shifted base label.**
* the lift operator data of a family do not see the base label (`familyLiftData_shiftBase`), nor
  do its admissible slow offsets (`ladderOmega_shiftBase`); the edges of a path family and the
  direct parts are the same at base-shifted contexts of a stage with the torus law
  (`pathEdges_shiftBase`, `directFlux_shiftBase`);
* the lift windows are ordered for a positive time scale and a nonnegative cell scale
  (`liftWindow_le`), and the window data of every family lift hold (`windowData_familyLiftData`);
* by the uniqueness of the lift sequences, the grade-zero lifts of a shifted admissible family
  agree with those of the family (`diagLift_shiftBase`), and the path lifts re-indexed by the
  shift form a lift family (`isLiftFamily_shiftBase`) that agrees with the given one on the
  admissible slow offsets at the times of the window (`pathLift_shiftBase`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.Torus

open AVRegularity.Providers.GenSem

variable (D : OCData)

/-! ### Lift data -/

theorem ladderOmega_shiftBase (b : ℝ) (j₀ m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (n : Fin 2 → ℤ) : ladderOmega D b j₀ m k (A.shiftBase n) ρ = ladderOmega D b j₀ m k A ρ := by
  ext X
  simp only [ladderOmega, Set.mem_ofPred_eq, recenter_shiftBase, isAdmissibleChain_shiftBase]

theorem familyLiftData_shiftBase {ι : Type*} {hv : ι → Type*} [∀ i, NormedAddCommGroup (hv i)]
    [∀ i, NormedSpace ℝ (hv i)] {Dm : ℕ} (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (E : ConstituentEdges Dm hv) (n : Fin 2 → ℤ) :
    familyLiftData D m k (A.shiftBase n) ρ E = familyLiftData D m k A ρ E := by
  simp only [familyLiftData, recenter_shiftBase, famMetric_shiftBase]

/-- Two constituents with the same map, coefficients and record are equal. -/
theorem constituent_ext {d : ℕ} {Hu Hv : Type*} [NormedAddCommGroup Hu] [NormedSpace ℝ Hu]
    [NormedAddCommGroup Hv] [NormedSpace ℝ Hv] {γ γ' : Constituent d Hu Hv} (h1 : γ.map = γ'.map)
    (h2 : γ.coeff = γ'.coeff) (h3 : γ.record = γ'.record) : γ = γ' := by
  cases γ
  cases γ'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm b j₀}

/-- **The edges of a path family at base-shifted contexts.** -/
theorem pathEdges_shiftBase (hsh : G.IsShiftInvariant) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c c' : StageCtx D b j₀ G.level p) (n : Fin 2 → ℤ) (hc : c'.1 = c.1.shiftBase n) :
    pathEdges G π p c' = pathEdges G π p c := by
  funext v u d
  unfold pathEdges
  split_ifs with h1 h2
  · exact congrArg (fun γ => [γ]) (constituent_ext rfl
      (funext fun I => hsh.1 p c c' n hc _ _ _ d.1 I) rfl)
  · rfl
  · rfl

/-- **The direct parts at base-shifted contexts.** -/
theorem directFlux_shiftBase (hsh : G.IsShiftInvariant) (p : OddSlot)
    (c c' : StageCtx D b j₀ G.level p) (n : Fin 2 → ℤ) (hc : c'.1 = c.1.shiftBase n)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ) (t : ℝ) :
    directFlux G p c' γ ords t = directFlux G p c γ ords t := by
  funext f y
  simp only [directFlux, hsh.1 p c c' n hc]

end Stage

/-! ### Windows and uniqueness -/

/-- The lift window of a slot is ordered. -/
theorem liftWindow_le {m : ℕ} (hτ : 0 < ocTau D.α D.q D.Λ m) (hcs : 0 ≤ D.cellScaleSq m) (k : ℤ) :
    D.slotStart m k / D.cellScaleSq m ≤
      (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m := by
  unfold OCData.slotStart
  apply div_le_div_of_nonneg_right _ hcs
  nlinarith

/-- The window data of the lift of a family over an odd slot. -/
theorem windowData_familyLiftData (hζ : IsFastProfile D.ζ) {ι : Type*} {hv : ι → Type*}
    [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {Dm : ℕ} (m : ℕ) {k : ℤ}
    (hk : Odd k) (A : RealChain) (ρ : ℝ) (E : ConstituentEdges Dm hv) (t₀ t₁ : ℝ) (X : Vec 2) :
    ∃ lo A' Mv : ℝ, Uniqueness.WindowData (fun t => Matrix.of ((familyLiftData D m k A ρ E).G t X))
      (familyLiftData D m k A ρ E).v t₀ t₁ lo A' Mv := by
  obtain ⟨lo, hi, hlo, hq⟩ := familyLiftData_pos_window D hζ m k A ρ E t₀ t₁ X
  obtain ⟨Mv, hMv⟩ := familyLiftData_v_bounded D hζ m hk A ρ E
  exact ⟨lo, hi, Mv, Uniqueness.windowData_of_elliptic _ _ t₀ t₁ lo hi Mv
    (fun t => familyLiftData_symm D m k A ρ E t X 0 1) hlo (fun t ht ξ => hq t ht ξ)
    (fun t _ z => hMv t z)⟩

/-- **The grade-zero lifts of a shifted admissible family agree with those of the family.** -/
theorem diagLift_shiftBase (hζ : IsFastProfile D.ζ) {Dm : ℕ} {b : ℝ} {j₀ m : ℕ} {Mn : SuccMenu}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hτ : 0 < ocTau D.α D.q D.Λ m) (hcs : 0 ≤ D.cellScaleSq m)
    (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) {k : ℤ} (hk : Odd k) {B : RealChain}
    (hB : IsAdmissibleChain D b j₀ m k B) (n : Fin 2 → ℤ) :
    ∀ τ ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
      ∀ n' m' (α : DerivativeWord2 m') X z v u,
        Cc0 k (B.shiftBase n) 0 n' m' α τ X z v u = Cc0 k B 0 n' m' α τ X z v u := by
  intro τ hτw n' m' α X z v u
  have h1 := hDL k (B.shiftBase n) hk ((isAdmissibleChain_shiftBase D b j₀ m k B n).2 hB)
  rw [familyLiftData_shiftBase] at h1
  exact lift_sequence_unique_elliptic _ _ _ (liftWindow_le D hτ hcs k)
    (fun t X i j => familyLiftData_symm D m k B _ _ t X i j)
    (fun X i j => familyLiftData_G_measurable D hζ m k B _ _ X i j)
    (fun X => familyLiftData_pos_window D hζ m k B _ _ _ _ X)
    (fun z => familyLiftData_v_measurable D hζ m k B _ _ z)
    (familyLiftData_v_bounded D hζ m hk B _ _) _ _ _ _ _ _ h1 (hDL k B hk hB) 0 le_rfl n' m' α τ
    hτw X z v u

section Paths

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm b j₀}

/-- **The path lifts re-indexed by a shift of the base label form a lift family.** -/
theorem isLiftFamily_shiftBase (hsh : G.IsShiftInvariant) {Mn : SuccMenu} (s : SuccSource G)
    {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)}
    (hLF : s.IsLiftFamily Mn Cc) (n : Fin 2 → ℤ) :
    s.IsLiftFamily Mn (fun k A => Cc k (A.shiftBase n)) := by
  have key : ∀ {h : ℕ} (π : StagePath G h) (k : ℤ) (A : RealChain)
      (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k),
      pathEdges G π ⟨k, hA.2⟩ ⟨A.shiftBase n, (isAdmissibleChain_shiftBase D b j₀ G.level k A n).2
        hA.1⟩ = pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩ :=
    fun π k A hA => pathEdges_shiftBase hsh π _ _ _ n rfl
  cases s with
  | copyDir t v u γ => trivial
  | letterDiag t u => trivial
  | copyQuad t h π =>
    intro k A hA
    have h1 := hLF k (A.shiftBase n) ⟨(isAdmissibleChain_shiftBase D b j₀ G.level k A n).2 hA.1,
      hA.2⟩
    rw [ladderOmega_shiftBase, familyLiftData_shiftBase, key π k A hA] at h1
    exact h1
  | letterMean t m h π =>
    intro k A hA
    have h1 := hLF k (A.shiftBase n) ⟨(isAdmissibleChain_shiftBase D b j₀ G.level k A n).2 hA.1,
      hA.2⟩
    rw [ladderOmega_shiftBase, familyLiftData_shiftBase, key π k A hA] at h1
    exact h1
  | letterCov t m h a a' π =>
    intro k A hA
    have h1 := hLF k (A.shiftBase n) ⟨(isAdmissibleChain_shiftBase D b j₀ G.level k A n).2 hA.1,
      hA.2⟩
    rw [ladderOmega_shiftBase, familyLiftData_shiftBase, key π k A hA] at h1
    exact h1

/-- **The shifted path lifts agree with the path lifts** on the admissible slow offsets, at the
times of the window. -/
theorem pathLift_shiftBase (hζ : IsFastProfile D.ζ) (hsh : G.IsShiftInvariant) {Mn : SuccMenu}
    (hτ : 0 < ocTau D.α D.q D.Λ G.level) (hcs : 0 ≤ D.cellScaleSq G.level) (s : SuccSource G)
    {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)}
    (hLF : s.IsLiftFamily Mn Cc) (n : Fin 2 → ℤ) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) (τ : ℝ)
    (hτw : τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    Uniqueness.LiftAgreeOn s (fun k A => Cc k (A.shiftBase n)) Cc k A τ
      (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) :=
  Uniqueness.liftAgreeOn_of_window Mn hcs hτ
    (fun _ _ _ A' hA' X => windowData_familyLiftData D hζ G.level hA'.2 A' _ _ _ _ X) s _ _
    (isLiftFamily_shiftBase hsh s hLF n) hLF k A hA (isOpen_ladderOmega _ _ _ _ _ _ _) τ hτw

end Paths

end AVRegularity.Providers.Torus
end
end
end

section
section
/-! **Torus law of the construction: the transferred coefficients** (the ingredient
`NonDiagonalTransferBaseShiftStatement`).
* `mem_liftWindow_of_cutoff`: a time of nonzero weight of the finer slot is, in cell time, in
  the lift window (`τ_m > 0`, `ℓ_m² ≥ 0`);
* `pathMeanFlux_congr`: a path mean flux reads its lift coefficients only at the cell time;
* `fluxOp_shiftBase`: the finer output of a source on a shifted family is the finer output on the
  family of the lifts re-indexed by the shift (the lift data, the edges, the direct parts and the
  chart maps do not see the base label, `Torus.Lifts`); by lift uniqueness its coefficients at the
  label `0` are those on the family (`fluxCoeff_fluxOp_shiftBase`);
* `transferAt_shiftBase`: the transfer to the coarser chart at a shifted context equals the
  transfer at the context (the child transitions do not see the base label);
* `nonDiagonalTransferBaseShift`: the ingredient. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.Torus

open AVRegularity.Providers.GenSem

/-- A time of nonzero weight of the finer slot is, in cell time, in the lift window. -/
theorem mem_liftWindow_of_cutoff (D : OCData) {m : ℕ} {k : ℤ} {t : ℝ}
    (hτ : 0 < ocTau D.α D.q D.Λ m) (hcs : 0 ≤ D.cellScaleSq m) (hk : ocCutoff D.α D.q D.Λ m k t ≠ 0) :
    (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  have hsupp := Uniqueness.cutoff_support D.α D.q D.Λ m k t hτ hk
  rcases hcs.eq_or_lt with hc0 | hcpos
  · rw [← hc0]
    simp
  · constructor
    · unfold OCData.slotStart
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hsupp.1 (inv_nonneg.mpr hcpos.le)
    · rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hsupp.2 (inv_nonneg.mpr hcpos.le)

/-- **A path mean flux reads its lift coefficients only at the cell time.** -/
theorem pathMeanFlux_congr (D : OCData) {Dm : ℕ} (m : ℕ) (ρ : ℝ) {h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (hC : ∀ hh n' m' (α : DerivativeWord2 m'), hh ≤ h →
      Cc hh n' m' α ((D.cellScaleSq m)⁻¹ * t) = Cc' hh n' m' α ((D.cellScaleSq m)⁻¹ * t)) :
    pathMeanFlux D m ρ Q Cc n t = pathMeanFlux D m ρ Q Cc' n t := by
  have hA : ∀ hh, hh ≤ h → ∀ (n' : ℕ) (a : ℝ → Vec 2 → Fin (h + 1) → ℝ),
      liftApply n' (Cc hh n') a ((D.cellScaleSq m)⁻¹ * t) =
        liftApply n' (Cc' hh n') a ((D.cellScaleSq m)⁻¹ * t) := by
    intro hh hle n' a
    funext X z v
    simp only [liftApply, hC hh n' _ _ hle]
  have hA0 := hA h le_rfl
  have hA1 := hA (h - 1) (Nat.sub_le h 1)
  funext f y k
  simp only [pathMeanFlux, liftFluxX, hA0, hA1]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm b j₀}

/-- **The finer output of a source on a shifted family** is the finer output on the family of
the lifts re-indexed by the shift. -/
theorem fluxOp_shiftBase (hsh : G.IsShiftInvariant) (ρ s₀ : ℝ) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (n : Fin 2 → ℤ) (k : ℤ) (t : ℝ) (A : RealChain) :
    s.fluxOp ρ s₀ Cc k t (A.shiftBase n) = s.fluxOp ρ s₀ (fun k A => Cc k (A.shiftBase n)) k t A := by
  unfold SuccSource.fluxOp
  by_cases hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k
  · have hA' : IsAdmissibleChain D b j₀ G.level k (A.shiftBase n) ∧ Odd k := hA
    rw [dite_eq_left hA', dite_eq_left hA]
    have hE : ∀ {h : ℕ} (π : StagePath G h),
        pathEdges G π ⟨k, hA'.2⟩ ⟨A.shiftBase n, hA'.1⟩ = pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩ :=
      fun π => pathEdges_shiftBase hsh π _ _ _ n rfl
    have hF : ∀ {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ),
        directFlux G ⟨k, hA'.2⟩ ⟨A.shiftBase n, hA'.1⟩ γ ords t =
          directFlux G ⟨k, hA.2⟩ ⟨A, hA.1⟩ γ ords t :=
      fun γ ords => directFlux_shiftBase hsh _ _ _ n rfl γ ords t
    cases s with
    | copyDir t' v u γ => exact hF γ _
    | copyQuad t' h π =>
      show pathMeanFlux D G.level ρ (familyLiftData D G.level k (A.shiftBase n) ρ
          (pathEdges G π ⟨k, hA'.2⟩ ⟨A.shiftBase n, hA'.1⟩)) (Cc k (A.shiftBase n)) 2 t = _
      rw [hE π, familyLiftData_shiftBase]
    | letterDiag t' u => rfl
    | letterMean t' m h π =>
      funext f y
      dsimp only
      rw [hE π, familyLiftData_shiftBase]
      split_ifs with hh
      · rw [hF]
      · rfl
    | letterCov t' m h a a' π =>
      show pullFlux ((A.shiftBase n).famMap D t) ((A.shiftBase n).famMapInv D t) _ = _
      rw [famMap_shiftBase, famMapInv_shiftBase, hE π, familyLiftData_shiftBase]
  · have hA' : ¬ (IsAdmissibleChain D b j₀ G.level k (A.shiftBase n) ∧ Odd k) := hA
    rw [dite_eq_right hA', dite_eq_right hA]

/-- **The coefficients at the label `0` of the finer output on a shifted family**, at a time of
nonzero weight. -/
theorem fluxCoeff_fluxOp_shiftBase (hζ : IsFastProfile D.ζ) (hsh : G.IsShiftInvariant)
    {Mn : SuccMenu} (hτ : 0 < ocTau D.α D.q D.Λ G.level) (hcs : 0 ≤ D.cellScaleSq G.level)
    (s₀ : ℝ) (s : SuccSource G)
    {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)}
    (hLF : s.IsLiftFamily Mn Cc) (n : Fin 2 → ℤ) {k : ℤ} {t : ℝ}
    (hk : ocCutoff D.α D.q D.Λ G.level k t ≠ 0) (A : RealChain) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t (A.shiftBase n)) d I 0 =
      fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t A) d I 0 := by
  rw [fluxOp_shiftBase hsh]
  exact Uniqueness.fluxOp_fluxCoeff_congr _ s₀ s _ Cc k t A
    (fun hA => ⟨isOpen_ladderOmega _ _ _ _ _ _ _, zero_mem_ladderOmega hζ hA.1 _⟩)
    ⟨((contDiff_famMapInv A t).continuous).continuousAt, famMapInv_zero hζ A t⟩
    (fun hA => pathLift_shiftBase hζ hsh hτ hcs s hLF n k A hA _
      (mem_liftWindow_of_cutoff D hτ hcs hk)) d I

/-- The child transitions do not see the base label. -/
theorem childTransition_shiftBase (D : OCData) (k : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2)
    (n : Fin 2 → ℤ) : childTransition D k t (ch.shiftBase n) z = childTransition D k t ch z := by
  unfold childTransition
  rw [appendChild_shiftBase, famJac_shiftBase, famJac_shiftBase]

/-- **The transfer at a shifted context.** -/
theorem transferAt_shiftBase (D : OCData) (m : ℕ) (pc : ℤ) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp)
    (t : ℝ) (ch : RealChain) (z : Vec 2) (n : Fin 2 → ℤ) (d' : ℕ) (β : DerivativeWord2 (d' - 1))
    (h : ∀ k : ℤ, ocCutoff D.α D.q D.Λ m k t ≠ 0 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)),
      fluxCoeff (fop k t ((ch.appendChild D k t z).shiftBase n)) d I 0 =
        fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) :
    transferAt D m pc lam Dγ fop t (ch.shiftBase n) z d' β = transferAt D m pc lam Dγ fop t ch z d' β := by
  unfold transferAt
  refine congrArg (((D.kap (m - 1) * D.eps (m - 1) ^ (d' - 2))⁻¹ * lam) • ·)
    (finsum_congr fun k => finsum_congr fun _ => ?_)
  by_cases hc : ocCutoff D.α D.q D.Λ m k t = 0
  · rw [hc, zero_smul, zero_smul]
  · have e1 : (fun h => (childTransition D k t ((ch.shiftBase n).recenter D h)
        (z + (D.eps (m - 1))⁻¹ • h))⁻¹) =
        fun h => (childTransition D k t (ch.recenter D h) (z + (D.eps (m - 1))⁻¹ • h))⁻¹ := by
      funext h
      rw [recenter_shiftBase, childTransition_shiftBase]
    have e2 : (fun d (I : DerivativeWord2 (d - 1)) =>
        fluxCoeff (fop k t ((ch.shiftBase n).appendChild D k t z)) d I 0) =
        fun d I => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0 := by
      funext d I
      rw [appendChild_shiftBase]
      exact h k hc d I
    rw [e1, e2]

/-- **Base-label invariance of the non-diagonal transferred coefficients.** -/
theorem nonDiagonalTransferBaseShift :
    Construction.Preservation.Assembly.NonDiagonalTransferBaseShiftStatement := by
  intro hr _ _ D Dm b j₀ P hζ hκ Mn M G G' hnat hold hsh hsucc p c c' n hc v u γ hnd d I hd t X z
  have hτ := Uniqueness.ocTau_pos_of_natural hnat
  have hcs : 0 ≤ D.cellScaleSq G.level := by
    unfold OCData.cellScaleSq OCData.kap
    exact div_nonneg (sq_nonneg _) (hκ _).le
  obtain ⟨-, -, -, -, -, -, e, Cc, _, hLF, -, hmain⟩ := hsucc
  obtain ⟨hp, -, hfl, -⟩ := hmain v u γ
  have hnd' : ¬ (e v u γ).1.IsDiag := by
    have hdiag : ∀ s : SuccSource G, s.prov G.level = G'.prov v u γ → ¬ s.IsDiag := by
      intro s hps hdg
      cases s <;> simp only [SuccSource.IsDiag] at hdg
      exact hnd G.level (by rw [← hps]; rfl)
    exact hdiag _ hp.symm
  rw [hfl hnd' p c' d I t X z hd, hfl hnd' p c d I t X z hd, hc, recenter_shiftBase]
  by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
  · have hadm' : IsAdmissibleChain D b j₀ G'.level p.1
        ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
    rw [ite_eq_left hadm', ite_eq_left hadm]
    exact transferAt_shiftBase D _ _ _ _ _ t _ z n d I fun k hk d' I' =>
      fluxCoeff_fluxOp_shiftBase hζ hsh hτ hcs _ _ (hLF _) n hk _ d' I'
  · have hadm' : ¬ IsAdmissibleChain D b j₀ G'.level p.1
        ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
    rw [ite_eq_right hadm', ite_eq_right hadm]

end AVRegularity.Providers.Torus
end
end

section
/-! **Torus law of the construction: the first-source coefficients** (the ingredient
`DiagonalSourceBaseShiftStatement`).
* `diagLabelFlux_shiftBase`: at a time of nonzero weight, the grade-zero label mean flux on a
  shifted admissible family is the one on the family (the lift data do not see the base label and
  the grade-zero lifts agree on the lift window, `Torus.Lifts.diagLift_shiftBase`);
* `diagMeanFluxCtx_shiftBase`, `diagFluxCtx_shiftBase`: the assembled diagonal fluxes at a shifted
  context are the ones at the context (the appended children commute with the shift and their
  chart maps do not see it);
* `firstSourceFlux_shiftBase`: the first-source flux at a shifted context is the one at the
  context (with the context strains, `Torus.Geometry.contextStrain_shiftBase`);
* `diagonalSourceBaseShift`: the ingredient. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.Torus

open AVRegularity.Providers.GenSem

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ m : ℕ} {Mn : SuccMenu}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem slot_shiftBase (ch : RealChain) (n : Fin 2 → ℤ) : (ch.shiftBase n).slot = ch.slot := rfl

/-- **The grade-zero label mean flux on a shifted family**, at a time of nonzero weight. -/
theorem diagLabelFlux_shiftBase (hζ : IsFastProfile D.ζ) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcs : 0 ≤ D.cellScaleSq m) (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) {k : ℤ} (hk : Odd k)
    {B : RealChain} (hB : IsAdmissibleChain D b j₀ m k B) (n : Fin 2 → ℤ) {t : ℝ}
    (hc : ocCutoff D.α D.q D.Λ m k t ≠ 0) (n' : ℕ) :
    diagLabelFlux D Dm m (Mn.lenFactor * liftLength D m) Cc0 k (B.shiftBase n) n' t =
      diagLabelFlux D Dm m (Mn.lenFactor * liftLength D m) Cc0 k B n' t := by
  unfold diagLabelFlux
  rw [familyLiftData_shiftBase]
  refine pathMeanFlux_congr D m _ _ _ _ n' t fun hh n'' m' α hh0 => ?_
  obtain rfl : hh = 0 := Nat.le_zero.mp hh0
  funext X z v u
  exact diagLift_shiftBase D hζ hτ hcs hDL hk hB n _ (mem_liftWindow_of_cutoff D hτ hcs hc)
    n'' m' α X z v u

/-- **The assembled diagonal mean flux at a shifted context.** -/
theorem diagMeanFluxCtx_shiftBase (hζ : IsFastProfile D.ζ) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcs : 0 ≤ D.cellScaleSq m) (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) (n : Fin 2 → ℤ) (n' : ℕ) :
    diagMeanFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Cc0 t (ch.shiftBase n) ζ n' =
      diagMeanFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Cc0 t ch ζ n' := by
  funext f x
  unfold diagMeanFluxCtx
  refine finsum_congr fun k => finsum_congr fun hk => ?_
  rw [appendChild_shiftBase]
  by_cases hadm : IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ)
  · have hadm' : IsAdmissibleChain D b j₀ m k ((ch.appendChild D k t ζ).shiftBase n) := hadm
    rw [ite_eq_left hadm', ite_eq_left hadm]
    by_cases hc : ocCutoff D.α D.q D.Λ m k t = 0
    · rw [hc, zero_smul, zero_smul]
    · rw [famMap_shiftBase, famMapInv_shiftBase,
        diagLabelFlux_shiftBase hζ hτ hcs hDL hk.1 hadm n hc]
  · have hadm' : ¬ IsAdmissibleChain D b j₀ m k ((ch.appendChild D k t ζ).shiftBase n) := hadm
    rw [ite_eq_right hadm', ite_eq_right hadm]

/-- **The assembled diagonal flux at a shifted context.** -/
theorem diagFluxCtx_shiftBase (hζ : IsFastProfile D.ζ) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcs : 0 ≤ D.cellScaleSq m) (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) (N : ℕ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (n : Fin 2 → ℤ) :
    diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) N Cc0 t (ch.shiftBase n) ζ =
      diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) N Cc0 t ch ζ := by
  unfold diagFluxCtx
  simp only [diagMeanFluxCtx_shiftBase hζ hτ hcs hDL]

/-- **The first-source flux at a shifted context.** -/
theorem firstSourceFlux_shiftBase (hζ : IsFastProfile D.ζ) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcs : 0 ≤ D.cellScaleSq m) (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) (N p : ℕ) (s₀ t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (n : Fin 2 → ℤ) :
    firstSourceFlux D b j₀ Dm m (Mn.lenFactor * liftLength D m) N p s₀ Cc0 t (ch.shiftBase n) ζ =
      firstSourceFlux D b j₀ Dm m (Mn.lenFactor * liftLength D m) N p s₀ Cc0 t ch ζ := by
  unfold firstSourceFlux
  simp only [famMap_shiftBase, famMapInv_shiftBase, recenter_shiftBase, contextStrain_shiftBase,
    slot_shiftBase, diagFluxCtx_shiftBase hζ hτ hcs hDL]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]

/-- **Base-label invariance of the first-source coefficients.** -/
theorem diagonalSourceBaseShift :
    Construction.Preservation.Assembly.DiagonalSourceBaseShiftStatement := by
  intro hr _ _ D Dm b j₀ P hζ hκ Mn M G G' hnat hold hsh hsucc p c c' n hc v u γ hdg d I hd t X z
  have hτ := Uniqueness.ocTau_pos_of_natural hnat
  have hcs : 0 ≤ D.cellScaleSq G.level := by
    unfold OCData.cellScaleSq OCData.kap
    exact div_nonneg (sq_nonneg _) (hκ _).le
  obtain ⟨-, -, -, -, -, -, e, _, Cc0, -, hDL, hmain⟩ := hsucc
  obtain ⟨hp, -, -, hfl⟩ := hmain v u γ
  have hdg' : (e v u γ).1.IsDiag := by
    obtain ⟨m, hm⟩ := hdg
    have hps : (e v u γ).1.prov G.level = Prov.letter m .diag [] := hp ▸ hm
    generalize (e v u γ).1 = s at hps ⊢
    cases s with
    | letterDiag => trivial
    | _ => simp [SuccSource.prov] at hps
  rw [hfl hdg' p c' d I t X z hd, hfl hdg' p c d I t X z hd, hc, recenter_shiftBase]
  by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
  · have hadm' : IsAdmissibleChain D b j₀ G'.level p.1
        ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
    rw [ite_eq_left hadm', ite_eq_left hadm, firstSourceFlux_shiftBase hζ hτ hcs hDL]
  · have hadm' : ¬ IsAdmissibleChain D b j₀ G'.level p.1
        ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
    rw [ite_eq_right hadm', ite_eq_right hadm]

end AVRegularity.Providers.Torus
end
end
end
