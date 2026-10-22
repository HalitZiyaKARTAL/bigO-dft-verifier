import Submission.Work.TensorEng.K4FEngine
import Submission.Work.K4T.Hole
-- changed for the tensor-power extension (26159999/10000000000); see Submission.lean

/-!
# Route B: the tensor engine for `G` copies of the RAW unit (closes hole H3)

`k4f_engine_of_rawG`: the tensor agent's `TensorEng.k4f_engine_of_raw` (ONE copy of the raw unit) for `G ≥ 1` copies:
the inventories of the bundled unit are `G • ofHist PK4F` and `G • ofHist TK4F`, and the strict moment fact for `G`
copies is the tensor agent's scaling inside `TensorEng.k4f_engine_of_rawG`.  Then `PB.K4T.tensorEngineG` is the
statement of hole H3, proved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OAI.PowerSaving.PB.K4T

lemma rawTgtB_eq : rawTgtB = TensorProto.K4F.TK4F := rfl
lemma rawPaidB_eq : rawPaidB = TensorProto.K4F.PK4F := rfl

/-- **Hole H3, proved**: a RAW certificate with `G` copies gives the engine statement of K4T (the tensor agent's
`TensorEng.k4f_engine_of_rawG` at `zE = 1 - 2615999999/10^12`). -/
theorem tensorEngineG (α ρ σ : Type) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] (hc : RawCertG α ρ σ) : MX.K4T.EngineStmt.{0} := by
  intro cl m ι k v
  obtain ⟨e, tr, tz, wd, G, he, tind, hP, hw, hG, hα, hcnt, hhist⟩ := hc
  -- every target rank is a rank of `rawTgtB`, hence in `[4, 73]`
  have htr : ∀ l, 1 ≤ tr l ∧ tr l ≤ 73 := by
    intro l
    have h1 : 0 < (Finset.univ.filter fun l' => tr l' = tr l).card := Finset.card_pos.mpr ⟨l, by simp⟩
    rw [hcnt] at h1
    have h2 : BlockAccounting.histFn rawTgtB (tr l) ≠ 0 := by
      intro h0; rw [h0, Nat.mul_zero] at h1; omega
    have h3 := BlockAccounting.mem_keys_of_histFn_ne_zero _ _ h2
    have h4 : tr l ∈ ({4, 5, 6, 7, 8, 9, 25, 41, 73} : Finset ℕ) := by
      simpa [BlockAccounting.keys, rawTgtB] using h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    omega
  exact TensorEng.k4f_engine_of_rawG e tr tz wd G he tind hP hw hG hα htr hcnt hhist (by norm_num) (by norm_num)
    m cl k v

end OAI.PowerSaving.PB.K4T

#print axioms OAI.PowerSaving.PB.K4T.tensorEngineG
