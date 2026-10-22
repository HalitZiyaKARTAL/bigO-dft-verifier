import Submission.Work.XHostT.HFW2979.GeomA4W

/-!
# (key: heads-first, three head kinds) The A2 and A3 head geometry (warp network, tv frames)

The A4 head geometry of Work/XHostT/HF/GeomA4.lean and Work/XHostT/HFW2979/GeomA4W.lean, for the first-touch climbs A2
(host kind 0: `bs401_1`, 16 lines, end frame of stage 1) and A3 (host kind 2: `bs401_3`, 32 lines, end frame of
stage 3): the climb of class `t`, side `s`, gauge `g` runs inside the same orthonormal base `a4Base base l g t` from the
frame of the lines `a4S0 l s` (the start frame of all three first-touch climbs) to the frame of the lines `a2S1 l s`
(resp. `a3S1 l s`), so it is ONE block of the lines `a2Lines l s` (resp. `a3Lines l s`) and then a free shift.
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD
noncomputable section

section GeomA23
variable {H T : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- the lines of the A2 end frame (side `s`). -/
def a2S1 (l : H) : Bool → Finset (BC.LC (Fin 8) H l)
  | false => JC univ (qC bs401_1)
  | true => JC (univ \ {l}) (qC bs401_1)

/-- **the 16 lines of an A2 head** (side `s`): the lines the A2 climb adds. -/
def a2Lines (l : H) (s : Bool) : Finset (BC.LC (Fin 8) H l) := a2S1 l s \ a4S0 l s

lemma a2S0_sub (l : H) (s : Bool) : a4S0 l s ⊆ a2S1 l s := by
  cases s
  · exact Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)
  · exact Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)

lemma a2Lines_card (hH : Fintype.card H = 9) (l : H) (s : Bool) : (a2Lines l s).card = 16 := by
  have e1 := Finset.card_sdiff_add_card_eq_card (a2S0_sub l s)
  have e2 : 16 + (a4S0 l s).card = (a2S1 l s).card := by
    cases s
    · show 16 + (JC {l} ∅ : Finset (BC.LC (Fin 8) H l)).card = (JC univ (qC bs401_1)).card
      rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty, card_bs401_1, hH]
    · show 16 + (JC ∅ ∅ : Finset (BC.LC (Fin 8) H l)).card = (JC (univ \ {l}) (qC bs401_1)).card
      rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty, card_bs401_1, hH]
  unfold a2Lines
  omega

/-- **the 16 head directions** of an A2 bin of side `j.1`, class `j.2`, gauge `g`: the lines `a2Lines` of
`a4Base`. -/
def a2Dir (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    Fin 16 → Space (BC.LC (Fin 8) H l) :=
  fun i => (a4Base base l g j.2).fam (a2Lines l j.1) (Fin.cast (a2Lines_card hH l j.1).symm i)

lemma a2Dir_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l))
    (j : Bool × T) : LinearIndependent F (a2Dir base l hH g j) :=
  ((a4Base base l g j.2).fam_indep _).comp _ (Fin.cast_injective _)

lemma blockMat_a2Dir (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l))
    (j : Bool × T) : blockMat (a2Dir base l hH g j) = blockMat ((a4Base base l g j.2).fam (a2Lines l j.1)) :=
  MX.blockMat_congr _ _ (fun x => MX.bph_cast (a2Lines_card hH l j.1).symm ((a4Base base l g j.2).fam (a2Lines l j.1)) x)

/-- the lines of the A3 end frame (side `s`). -/
def a3S1 (l : H) : Bool → Finset (BC.LC (Fin 8) H l)
  | false => JC univ (qC bs401_3)
  | true => JC (univ \ {l}) (qC bs401_3)

/-- **the 32 lines of an A3 head** (side `s`): the lines the A3 climb adds. -/
def a3Lines (l : H) (s : Bool) : Finset (BC.LC (Fin 8) H l) := a3S1 l s \ a4S0 l s

lemma a3S0_sub (l : H) (s : Bool) : a4S0 l s ⊆ a3S1 l s := by
  cases s
  · exact Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)
  · exact Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)

lemma a3Lines_card (hH : Fintype.card H = 9) (l : H) (s : Bool) : (a3Lines l s).card = 32 := by
  have e1 := Finset.card_sdiff_add_card_eq_card (a3S0_sub l s)
  have e2 : 32 + (a4S0 l s).card = (a3S1 l s).card := by
    cases s
    · show 32 + (JC {l} ∅ : Finset (BC.LC (Fin 8) H l)).card = (JC univ (qC bs401_3)).card
      rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty, card_bs401_3, hH]
    · show 32 + (JC ∅ ∅ : Finset (BC.LC (Fin 8) H l)).card = (JC (univ \ {l}) (qC bs401_3)).card
      rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty, card_bs401_3, hH]
  unfold a3Lines
  omega

/-- **the 32 head directions** of an A3 bin of side `j.1`, class `j.2`, gauge `g`: the lines `a3Lines` of
`a4Base`. -/
def a3Dir (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    Fin 32 → Space (BC.LC (Fin 8) H l) :=
  fun i => (a4Base base l g j.2).fam (a3Lines l j.1) (Fin.cast (a3Lines_card hH l j.1).symm i)

lemma a3Dir_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l))
    (j : Bool × T) : LinearIndependent F (a3Dir base l hH g j) :=
  ((a4Base base l g j.2).fam_indep _).comp _ (Fin.cast_injective _)

lemma blockMat_a3Dir (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (g : Orth (BC.LC (Fin 8) H l))
    (j : Bool × T) : blockMat (a3Dir base l hH g j) = blockMat ((a4Base base l g j.2).fam (a3Lines l j.1)) :=
  MX.blockMat_congr _ _ (fun x => MX.bph_cast (a3Lines_card hH l j.1).symm ((a4Base base l g j.2).fam (a3Lines l j.1)) x)

end GeomA23
end
end XHostT

namespace XHostTW
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT
noncomputable section

section GeomA23W
variable {H T : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
variable (tv : T → Space H) (base : T → OBase H) (l : H)
variable (hbase : ∀ t, tv t = (base t).v l) (hH : Fintype.card H = 9)
include hbase

lemma x0t_A2_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x0t_A2 tv base l g j = frame (a4Base base l g j.2) (a4S0 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · show PhiC g ∅ (tt (tv t)) = frame (BBC (base t) l g) (JC {l} ∅)
    rw [hbase t]; exact classT_X0 (base t) l g
  · exact classT_Y0 (base t) l g

lemma x1t_A2_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1t_A2 tv base l g j = frame (a4Base base l g j.2) (a2S1 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · exact classT_X (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g
  · show PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) (1 + tt (tv t))
      = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_1))
    rw [hbase t]; exact classT_Y (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g

/-- **the A2 climb is the head block and a free shift** (tv frames). -/
theorem a2t_climb_eq (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1t_A2 tv base l g j = Binary.shift ((a4Base base l g j.2).corr (a2Lines l j.1))
      * (blockMat (a2Dir base l hH g j) * x0t_A2 tv base l g j) := by
  rw [x0t_A2_frame tv base l hbase, x1t_A2_frame tv base l hbase, blockMat_a2Dir, ← Matrix.mul_assoc,
    ← OBase.deltas_eq, a2Lines, ← OBase.frame_union _ _ _ Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (a2S0_sub l j.1)]

/-- **the A2 head geometry** (tv frames): after the head block the A2 end frame is reached for free. -/
theorem a2t_head_geom (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (blockMat (a2Dir base l hH g j) * x0t_A2 tv base l g j) (x1t_A2 tv base l g j) (fun _ => 0) := by
  rw [a2t_climb_eq tv base l hbase hH g j]
  exact fun ρ _ _ r => gstep_free (Free.shift _) r _

lemma x0t_A3_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x0t_A3 tv base l g j = frame (a4Base base l g j.2) (a4S0 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · show PhiC g ∅ (tt (tv t)) = frame (BBC (base t) l g) (JC {l} ∅)
    rw [hbase t]; exact classT_X0 (base t) l g
  · exact classT_Y0 (base t) l g

lemma x1t_A3_frame (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1t_A3 tv base l g j = frame (a4Base base l g j.2) (a3S1 l j.1) := by
  obtain ⟨s, t⟩ := j
  cases s
  · exact classT_X (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g
  · show PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) (1 + tt (tv t))
      = frame (BBC (base t) l g) (JC (univ \ {l}) (qC bs401_3))
    rw [hbase t]; exact classT_Y (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g

/-- **the A3 climb is the head block and a free shift** (tv frames). -/
theorem a3t_climb_eq (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    x1t_A3 tv base l g j = Binary.shift ((a4Base base l g j.2).corr (a3Lines l j.1))
      * (blockMat (a3Dir base l hH g j) * x0t_A3 tv base l g j) := by
  rw [x0t_A3_frame tv base l hbase, x1t_A3_frame tv base l hbase, blockMat_a3Dir, ← Matrix.mul_assoc,
    ← OBase.deltas_eq, a3Lines, ← OBase.frame_union _ _ _ Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (a3S0_sub l j.1)]

/-- **the A3 head geometry** (tv frames): after the head block the A3 end frame is reached for free. -/
theorem a3t_head_geom (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (blockMat (a3Dir base l hH g j) * x0t_A3 tv base l g j) (x1t_A3 tv base l g j) (fun _ => 0) := by
  rw [a3t_climb_eq tv base l hbase hH g j]
  exact fun ρ _ _ r => gstep_free (Free.shift _) r _

end GeomA23W
end
end XHostTW
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.a2Lines_card
#print axioms OAI.PowerSaving.XHostT.a3Lines_card
#print axioms OAI.PowerSaving.XHostTW.a2t_head_geom
#print axioms OAI.PowerSaving.XHostTW.a3t_head_geom
