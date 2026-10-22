import Submission.Work.XHostT.TGeomW
import Submission.Work.XHostT.HFW2979.Heads
import Submission.Work.XHostT.HFW2979.GeomA23W
/-!
# (key: heads-first, warp) The heads-first certificate of p-a3's GEOMETRIC WARP network `xnetGeomW`

p-hfirst's Work/XHostT/HF/GeomInst.lean for the warp network (providers `GInvW .. Ok`, window facts `hOk`), the
network of the #2979 (and #3945) provider words, which are windowed packages (p-wgen / x-words):
* `xnetGeomW_unit`: its unit price is p-a3's `unitPriceTW Ic S`;
* `xnetGeomW_heads_first`: `GLiveKernel Sum.inl (headWord Sum.inl (headsL hb) (fun _ => 48) zGeom _ ++ body)`, `body`
  proper, `body` price `card Γ * unitPriceTW Ic S - |headsL hb| * φ 48` for every price list;
* `xnetGeomW_heads_first_auto`: the same for the canonical head set `headBins S` (no hypothesis left);
* `xnetGeomW_cut_half`: the whole chain to e-r45m1's half-cut mixed certificate (`MX.cut_heads_half`, a = b = 24).
The head data (`zGeom`, `cutA`, `cutS`, `bph_cut`, `headBins`, `headBins_eq`) are p-hfirst's, imported: they depend
only on the roles and the schedule, not on the providers.
Written by x-inst (wht45/lever2979, 19 Oct 2026) on p-hfirst's file; prepared with assistance from Claude.  No `sorry`.
-/
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostTW
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT
noncomputable section

section HeadData
variable {H T Sl : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] {nR : ℕ}

/-- the A2 head directions on every live role (only the head roles' values matter). -/
def zG2 (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Fin 16 → Space (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a2Dir base l hH (dDecD d).2.2.1 ((dDecD d).2.1, (dDecD d).2.2.2)
  | Sum.inr (_, b) => b.elim0

/-- the A3 head directions on every live role. -/
def zG3 (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Fin 32 → Space (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a3Dir base l hH (dDecD d).2.2.1 ((dDecD d).2.1, (dDecD d).2.2.2)
  | Sum.inr (_, b) => b.elim0

/-- the A4 head directions on every live role. -/
def zG4 (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Fin 48 → Space (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a4Dir base l hH (dDecD d).2.2.1 ((dDecD d).2.1, (dDecD d).2.2.2)
  | Sum.inr (_, b) => b.elim0

lemma zG2_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9)
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) : LinearIndependent F (zG2 base l hH r) := by
  rcases r with (⟨_, d⟩ | ⟨_, b⟩)
  · exact a2Dir_indep base l hH _ _
  · exact b.elim0

lemma zG3_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9)
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) : LinearIndependent F (zG3 base l hH r) := by
  rcases r with (⟨_, d⟩ | ⟨_, b⟩)
  · exact a3Dir_indep base l hH _ _
  · exact b.elim0

lemma zG4_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9)
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) : LinearIndependent F (zG4 base l hH r) := by
  rcases r with (⟨_, d⟩ | ⟨_, b⟩)
  · exact a4Dir_indep base l hH _ _
  · exact b.elim0

lemma zG2_head (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (ρ : Fin nR)
    (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : zG2 base l hH (hroleP 2 ρ g j) = a2Dir base l hH g j := by
  obtain ⟨s, t⟩ := j
  cases s <;> rfl

lemma zG3_head (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (ρ : Fin nR)
    (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : zG3 base l hH (hroleP 3 ρ g j) = a3Dir base l hH g j := by
  obtain ⟨s, t⟩ := j
  cases s <;> rfl

lemma zG4_head (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (ρ : Fin nR)
    (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : zG4 base l hH (hroleP 4 ρ g j) = a4Dir base l hH g j := by
  obtain ⟨s, t⟩ := j
  cases s <;> rfl

/-- the canonical head bins of host kind `c`: remaining climb `r` (the full rank of the kind), nothing hosted. -/
def headBinsK (S : HostSchedT nR Sl T) (c : Fin 9) (r : ℕ) : Finset (Fin nR × Bool × T) :=
  Finset.univ.filter (fun p => S.hrem p.1 c p.2 = r ∧ ∀ ρ l q, S.host ρ l q ≠ (p.1, c, p.2))

lemma headBinsK_unh (S : HostSchedT nR Sl T) (c : Fin 9) (r : ℕ) (ρ : Fin nR) (l : Fin 9) (q : Sl) (ρh : Fin nR)
    (j : Bool × T) (h : (ρh, j) ∈ headBinsK S c r) : S.host ρ l q ≠ (ρh, c, j) :=
  (Finset.mem_filter.mp h).2.2 ρ l q

lemma headBinsK_full (S : HostSchedT nR Sl T) (c : Fin 9) (r : ℕ) (ρ : Fin nR) (j : Bool × T)
    (h : (ρ, j) ∈ headBinsK S c r) : S.hrem ρ c j = r :=
  (Finset.mem_filter.mp h).2.1

/-- with positive residuals, the head bins of kind `c` are exactly the bins of kind `c` whose remaining climb is the
full rank of the kind (a fitting schedule hosts nothing there). -/
lemma headBinsK_eq (S : HostSchedT nR Sl T) (res : Fin nR → Fin 9 → Sl → ℕ)
    (hfit : S.fits res) (hpos : ∀ ρ l q, 0 < res ρ l q) (c : Fin 9) :
    headBinsK S c (rankOf c.val) = Finset.univ.filter (fun p : Fin nR × Bool × T => S.hrem p.1 c p.2 = rankOf c.val) := by
  ext ⟨ρh, j⟩
  simp only [headBinsK, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun ρ l q e => ?_⟩
    have hf := hfit ρh c j
    rw [h] at hf
    have hl : S.load res ρh c j = 0 := by omega
    have hmem : (ρ, l, q) ∈ (Finset.univ : Finset (Fin nR × Fin 9 × Sl)).filter
        (fun p => S.host p.1 p.2.1 p.2.2 = (ρh, c, j)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩
    have hle : res ρ l q ≤ S.load res ρh c j := by
      unfold HostSchedT.load
      exact Finset.single_le_sum (f := fun p : Fin nR × Fin 9 × Sl => res p.1 p.2.1 p.2.2)
        (fun _ _ => Nat.zero_le _) hmem
    have hp := hpos ρ l q
    omega

/-- the frame of every live role (only head roles matter): `a4Base` of its class and gauge. -/
def cutA3 (base : T → OBase H) (l : H) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → OBase (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a4Base base l (dDecD d).2.2.1 (dDecD d).2.2.2
  | Sum.inr (_, b) => b.elim0

/-- the full-cut lines of every live role: ALL the lines of the head of its data pair (2: A2, 3: A3, else A4). -/
def cutS3 (l : H) : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Finset (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => if (dDecD d).1 = 2 then a2Lines l (dDecD d).2.1
      else if (dDecD d).1 = 3 then a3Lines l (dDecD d).2.1 else a4Lines l (dDecD d).2.1
  | Sum.inr (_, b) => b.elim0

lemma cutS3_card2 (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsLP (nb := 0) 2 hb) : (cutS3 l r).card = 16 := by
  obtain ⟨x, -, g, rfl⟩ := (mem_headsLP 2 hb r).1 hr
  obtain ⟨ρ, s, t⟩ := x
  cases s
  · exact a2Lines_card hH l false
  · exact a2Lines_card hH l true

lemma cutS3_card3 (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsLP (nb := 0) 3 hb) : (cutS3 l r).card = 32 := by
  obtain ⟨x, -, g, rfl⟩ := (mem_headsLP 3 hb r).1 hr
  obtain ⟨ρ, s, t⟩ := x
  cases s
  · exact a3Lines_card hH l false
  · exact a3Lines_card hH l true

lemma cutS3_card4 (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsLP (nb := 0) 4 hb) : (cutS3 l r).card = 48 := by
  obtain ⟨x, -, g, rfl⟩ := (mem_headsLP 4 hb r).1 hr
  obtain ⟨ρ, s, t⟩ := x
  cases s
  · exact a4Lines_card hH l false
  · exact a4Lines_card hH l true

/-- **the 16-line cut fact**: each A2 head is the block of all the lines `cutS3` of its frame `cutA3`. -/
lemma bph_cut2 (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsLP (nb := 0) 2 hb) (x : Space (BC.LC (Fin 8) H l)) :
    MX.bph (zG2 base l hH r) x = MX.bph ((cutA3 base l r).fam (cutS3 l r)) x := by
  obtain ⟨p, -, g, rfl⟩ := (mem_headsLP 2 hb r).1 hr
  obtain ⟨ρ, s, t⟩ := p
  cases s
  · exact MX.bph_cast (a2Lines_card hH l false).symm ((a4Base base l g t).fam (a2Lines l false)) x
  · exact MX.bph_cast (a2Lines_card hH l true).symm ((a4Base base l g t).fam (a2Lines l true)) x

/-- **the 32-line cut fact**: each A3 head is the block of all the lines `cutS3` of its frame `cutA3`. -/
lemma bph_cut3 (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsLP (nb := 0) 3 hb) (x : Space (BC.LC (Fin 8) H l)) :
    MX.bph (zG3 base l hH r) x = MX.bph ((cutA3 base l r).fam (cutS3 l r)) x := by
  obtain ⟨p, -, g, rfl⟩ := (mem_headsLP 3 hb r).1 hr
  obtain ⟨ρ, s, t⟩ := p
  cases s
  · exact MX.bph_cast (a3Lines_card hH l false).symm ((a4Base base l g t).fam (a3Lines l false)) x
  · exact MX.bph_cast (a3Lines_card hH l true).symm ((a4Base base l g t).fam (a3Lines l true)) x

/-- **the 48-line cut fact**: each A4 head is the block of all the lines `cutS3` of its frame `cutA3`. -/
lemma bph_cut4 (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (hb : Finset (Fin nR × Bool × T))
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) (hr : r ∈ headsLP (nb := 0) 4 hb) (x : Space (BC.LC (Fin 8) H l)) :
    MX.bph (zG4 base l hH r) x = MX.bph ((cutA3 base l r).fam (cutS3 l r)) x := by
  obtain ⟨p, -, g, rfl⟩ := (mem_headsLP 4 hb r).1 hr
  obtain ⟨ρ, s, t⟩ := p
  cases s
  · exact MX.bph_cast (a4Lines_card hH l false).symm ((a4Base base l g t).fam (a4Lines l false)) x
  · exact MX.bph_cast (a4Lines_card hH l true).symm ((a4Base base l g t).fam (a4Lines l true)) x

end HeadData

section InstW
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok) (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv)
  (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
  (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
  (S : HostSchedT nR Sl T) (hfit : S.fits (resIcW Ic))

/-- the unit price of the geometric warp network is p-a3's `unitPriceTW` (the step `e` of `bridgeHostTW_gcert`). -/
lemma xnetGeomW_unit (φ : ℕ → ℝ) :
    (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).unit φ = unitPriceTW Ic S φ := by
  simp only [XNetW.unit, XNetW.callU, Finset.sum_add_distrib, sum_tailUW, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, unitPriceTW]
  simp only [XNetW.hcost, hcostT, xnetGeomW, bcost_zero, add_zero, mul_zero, Finset.sum_const_zero]

include I hIc hbase hOk hfit in
/-- **THE HEADS-FIRST CERTIFICATE OF THE GEOMETRIC WARP NETWORK, three head kinds.** -/
theorem xnetGeomW_heads_first3 (hb2 hb3 hb4 : Finset (Fin nR × Bool × T))
    (hu2 : ∀ ρ l' q ρh j, (ρh, j) ∈ hb2 → S.host ρ l' q ≠ (ρh, 0, j))
    (hu3 : ∀ ρ l' q ρh j, (ρh, j) ∈ hb3 → S.host ρ l' q ≠ (ρh, 2, j))
    (hu4 : ∀ ρ l' q ρh j, (ρh, j) ∈ hb4 → S.host ρ l' q ≠ (ρh, 4, j))
    (hf2 : ∀ ρ j, (ρ, j) ∈ hb2 → S.hrem ρ 0 j = 16) (hf3 : ∀ ρ j, (ρ, j) ∈ hb3 → S.hrem ρ 2 j = 32)
    (hf4 : ∀ ρ j, (ρ, j) ∈ hb4 → S.hrem ρ 4 j = 48) :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceTW Ic S φ
          - (((headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) 2 hb2).length : ℝ) * φ 16
            + ((headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) 3 hb3).length : ℝ) * φ 32
            + ((headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) 4 hb4).length : ℝ) * φ 48)) ∧
      GLiveKernel (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (MX.headWord Sum.inl (headsLP 2 hb2) (fun _ => 16) (zG2 base l hH) (zG2_indep base l hH)
          ++ (MX.headWord Sum.inl (headsLP 3 hb3) (fun _ => 32) (zG3 base l hH) (zG3_indep base l hH)
            ++ (MX.headWord Sum.inl (headsLP 4 hb4) (fun _ => 48) (zG4 base l hH) (zG4_indep base l hH)
              ++ body))) := by
  have hz2 : ∀ ρ j, (ρ, j) ∈ hb2 → ∀ g, GReach (blockMat (zG2 base l hH (hroleP 2 ρ g j))
      * (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x0A4 g j)
      ((xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x1A2 g j) (fun _ => 0) := by
    intro ρ j _ g
    rw [zG2_head]
    obtain ⟨s, t⟩ := j
    cases s
    · exact a2t_head_geom I.tv base l hbase hH g (false, t)
    · exact a2t_head_geom I.tv base l hbase hH g (true, t)
  have hz3 : ∀ ρ j, (ρ, j) ∈ hb3 → ∀ g, GReach (blockMat (zG3 base l hH (hroleP 3 ρ g j))
      * (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x0A4 g j)
      ((xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x1A3 g j) (fun _ => 0) := by
    intro ρ j _ g
    rw [zG3_head]
    obtain ⟨s, t⟩ := j
    cases s
    · exact a3t_head_geom I.tv base l hbase hH g (false, t)
    · exact a3t_head_geom I.tv base l hbase hH g (true, t)
  have hz4 : ∀ ρ j, (ρ, j) ∈ hb4 → ∀ g, GReach (blockMat (zG4 base l hH (hroleP 4 ρ g j))
      * (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x0A4 g j)
      ((xnetGeomW I Ic hIc base l hbase hH hOk S hfit).x1A4 g j) (fun _ => 0) := by
    intro ρ j _ g
    rw [zG4_head]
    obtain ⟨s, t⟩ := j
    cases s
    · exact a4t_head_geom I.tv base l hbase hH g (false, t)
    · exact a4t_head_geom I.tv base l hbase hH g (true, t)
  have hunh : ∀ ρ l' q ρh c j, isHd hb2 hb3 hb4 ρh c j →
      (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).hostAt ρ l' q ≠ some (ρh, c, j) := by
    rintro ρ l' q ρh c j (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) e
    · exact hu2 ρ l' q ρh j h (Option.some_injective _ e)
    · exact hu3 ρ l' q ρh j h (Option.some_injective _ e)
    · exact hu4 ρ l' q ρh j h (Option.some_injective _ e)
  obtain ⟨body, hP, hc, hk⟩ := (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).heads_first3 hb2 hb3 hb4 hunh
    hf2 hf3 hf4 (zG2 base l hH) (zG3 base l hH) (zG4 base l hH) (zG2_indep base l hH) (zG3_indep base l hH)
    (zG4_indep base l hH) hz2 hz3 hz4
  refine ⟨body, hP, fun φ => ?_, hk⟩
  rw [hc φ, xnetGeomW_unit]

end InstW
end
end XHostTW
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostTW.xnetGeomW_unit
#print axioms OAI.PowerSaving.XHostTW.xnetGeomW_heads_first3
#print axioms OAI.PowerSaving.XHostTW.headBinsK_eq
#print axioms OAI.PowerSaving.XHostTW.bph_cut2
#print axioms OAI.PowerSaving.XHostTW.bph_cut3
#print axioms OAI.PowerSaving.XHostTW.bph_cut4
